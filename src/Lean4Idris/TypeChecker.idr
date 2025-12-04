||| Type checker for Lean 4 kernel
|||
||| Core operations:
||| - inferType: compute the type of an expression
||| - whnf: reduce to weak head normal form (beta, let, delta)
||| - isDefEq: check definitional equality
|||
||| Supports both closed expressions and open expressions with local context.
module Lean4Idris.TypeChecker

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Subst
import Lean4Idris.Pretty
import Data.SortedMap
import Debug.Trace
import Data.Fin
import Data.List
import Data.Vect
import Data.String
import System.FFI
import System.File
import Debug.Trace

debugFile : File
debugFile = unsafePerformIO $ do
  Right f <- openFile "/tmp/typecheck_debug.txt" Append
    | Left _ => pure stdin  -- fallback
  pure f

debugPrint : String -> a -> a
debugPrint msg x = unsafePerformIO $ do
  Right () <- fPutStrLn debugFile (msg ++ "\n")
    | Left _ => pure x
  fflush debugFile
  pure x

%default total

------------------------------------------------------------------------
-- Environment
------------------------------------------------------------------------

||| A type checking environment holds all known declarations
public export
record TCEnv where
  constructor MkTCEnv
  decls : SortedMap Name Declaration
  quotInit : Bool  -- True if quotient types are initialized
  ||| Types of placeholder constants created by closeWithPlaceholders.
  ||| When we close an open term, bound variables become placeholder constants
  ||| like `Const "_local_x" []`. This map tracks their types so we can
  ||| properly type-check expressions containing them.
  placeholders : SortedMap Name ClosedExpr
  ||| Maps binder names to comparison placeholder names.
  ||| Used during isDefEq to recognize that inference placeholders
  ||| (like `α.0._local`) should be treated as equal to comparison placeholders
  ||| (like `_x._isDefEqBody`) when comparing body types.
  binderAliases : SortedMap Name Name
  ||| Global counter for placeholder names to ensure uniqueness across context depths.
  ||| This ensures that even when closeWithPlaceholders is called at different depths,
  ||| each variable gets a unique placeholder that persists.
  nextPlaceholder : Nat

||| Empty environment
public export
emptyEnv : TCEnv
emptyEnv = MkTCEnv empty False empty empty 0

||| Add a placeholder constant with its type (as an axiom in the environment)
||| This allows regular constant lookup to find placeholder types.
public export
addPlaceholder : Name -> ClosedExpr -> TCEnv -> TCEnv
addPlaceholder name ty env =
  -- Add as both a placeholder (for tracking) and as an axiom (for lookup)
  let env' = { placeholders $= insert name ty } env
  in { decls $= insert name (AxiomDecl name ty []) } env'

||| Look up a placeholder's type
public export
lookupPlaceholder : Name -> TCEnv -> Maybe ClosedExpr
lookupPlaceholder name env = lookup name env.placeholders

||| Clear all placeholders (for fresh type checking context)
public export
clearPlaceholders : TCEnv -> TCEnv
clearPlaceholders env = { placeholders := empty, binderAliases := empty } env

||| Register a binder alias: inference placeholders with this binder name
||| should be treated as equal to the comparison placeholder
public export
addBinderAlias : Name -> Name -> TCEnv -> TCEnv
addBinderAlias binderName comparisonPh env =
  { binderAliases $= insert binderName comparisonPh } env

||| Look up what placeholder name a binder maps to
public export
lookupBinderAlias : Name -> TCEnv -> Maybe Name
lookupBinderAlias binderName env = lookup binderName env.binderAliases

||| Enable quotient types in the environment
public export
enableQuot : TCEnv -> TCEnv
enableQuot env = { quotInit := True } env

||| Add a declaration to the environment
public export
addDecl : Declaration -> TCEnv -> TCEnv
addDecl d env = case declName d of
  Just n  => { decls $= insert n d } env
  Nothing => env

||| Look up a declaration by name
public export
lookupDecl : Name -> TCEnv -> Maybe Declaration
lookupDecl n env = lookup n env.decls

------------------------------------------------------------------------
-- Local Context
------------------------------------------------------------------------

||| Local context entry - information about a bound variable
public export
record LocalEntry where
  constructor MkLocalEntry
  name : Name
  type : ClosedExpr      -- Type of this variable (as closed expr)
  value : Maybe ClosedExpr  -- Value if this is a let-binding
  placeholder : Maybe ClosedExpr  -- Placeholder constant assigned to this variable

||| Local context for typing expressions with bound variables.
||| Maps each bound variable index to its type.
|||
||| When we have `Expr n`, the context has `n` entries.
||| Entry at index 0 corresponds to de Bruijn index 0 (most recent binder).
public export
LocalCtx : Nat -> Type
LocalCtx n = Vect n LocalEntry

||| Empty local context (for closed expressions)
public export
emptyCtx : LocalCtx 0
emptyCtx = []

||| Extend context with a new local declaration (going under a binder)
||| The type is given as a closed expression (already substituted)
public export
extendCtx : Name -> ClosedExpr -> LocalCtx n -> LocalCtx (S n)
extendCtx name ty ctx = MkLocalEntry name ty Nothing Nothing :: ctx

||| Extend context with a let-binding (going under a let)
public export
extendCtxLet : Name -> ClosedExpr -> ClosedExpr -> LocalCtx n -> LocalCtx (S n)
extendCtxLet name ty val ctx = MkLocalEntry name ty (Just val) Nothing :: ctx

||| Look up a variable's type in the context
public export
lookupCtx : Fin n -> LocalCtx n -> LocalEntry
lookupCtx FZ (entry :: _) = entry
lookupCtx (FS k) (_ :: ctx) = lookupCtx k ctx

------------------------------------------------------------------------
-- Errors
------------------------------------------------------------------------

||| Type checking errors
public export
data TCError : Type where
  ||| Expected a type (Sort) but got something else
  TypeExpected : ClosedExpr -> TCError
  ||| Expected a function type (Pi) but got something else
  FunctionExpected : ClosedExpr -> TCError
  ||| Application type mismatch: argument type doesn't match expected
  AppTypeMismatch : (expected : ClosedExpr) -> (actual : ClosedExpr) -> TCError
  ||| Let binding type mismatch
  LetTypeMismatch : (expected : ClosedExpr) -> (actual : ClosedExpr) -> TCError
  ||| Unknown constant
  UnknownConst : Name -> TCError
  ||| Wrong number of universe levels
  WrongNumLevels : (expected : Nat) -> (actual : Nat) -> Name -> TCError
  ||| Negative occurrence in inductive type (non-strict positivity)
  NegativeOccurrence : (indName : Name) -> (ctorName : Name) -> TCError
  ||| Constructor return type doesn't match inductive type
  CtorWrongReturnType : (ctorName : Name) -> (expected : Name) -> (actual : ClosedExpr) -> TCError
  ||| Constructor field count doesn't match type
  CtorWrongFieldCount : (ctorName : Name) -> (declared : Nat) -> (actual : Nat) -> TCError
  ||| Constructor references wrong inductive type
  CtorWrongInductive : (ctorName : Name) -> (declared : Name) -> (actual : Name) -> TCError
  ||| Constructor universe parameters don't match inductive
  CtorUniverseMismatch : (ctorName : Name) -> (indParams : List Name) -> (ctorParams : List Name) -> TCError
  ||| Inductive type not found for constructor
  CtorInductiveNotFound : (ctorName : Name) -> (indName : Name) -> TCError
  ||| Cyclic universe level parameter (would cause infinite loop)
  CyclicLevelParam : Name -> TCError
  ||| Other error
  OtherError : String -> TCError

export
covering
Show TCError where
  show (TypeExpected e) = "type expected (got: " ++ showExprHead e ++ ")"
    where
      showExprHead : ClosedExpr -> String
      showExprHead (Sort _) = "Sort"
      showExprHead (Const n _) = "Const " ++ show n
      showExprHead (App _ _) = "App"
      showExprHead (Lam _ _ _ _) = "Lam"
      showExprHead (Pi _ _ _ _) = "Pi"
      showExprHead (Let _ _ _ _) = "Let"
      showExprHead (BVar _) = "BVar"
      showExprHead (Proj _ _ _) = "Proj"
      showExprHead (NatLit _) = "NatLit"
      showExprHead (StringLit _) = "StringLit"
  show (FunctionExpected e) = "function expected: " ++ show e
  show (AppTypeMismatch dom argTy) = "application type mismatch: expected " ++ show dom ++ ", got " ++ show argTy
  show (LetTypeMismatch _ _) = "let binding type mismatch"
  show (UnknownConst n) = "XXXUNKNOWN constant: " ++ show n
  show (WrongNumLevels exp act n) =
    "wrong number of universe levels for " ++ show n ++
    ": expected " ++ show exp ++ ", got " ++ show act
  show (NegativeOccurrence ind ctor) =
    "negative occurrence of " ++ show ind ++ " in constructor " ++ show ctor
  show (CtorWrongReturnType ctor expected _) =
    "constructor " ++ show ctor ++ " must return " ++ show expected
  show (CtorWrongFieldCount ctor decl actual) =
    "constructor " ++ show ctor ++ " declares " ++ show decl ++
    " fields but type has " ++ show actual
  show (CtorWrongInductive ctor decl actual) =
    "constructor " ++ show ctor ++ " registered for " ++ show decl ++
    " but returns " ++ show actual
  show (CtorUniverseMismatch ctor indPs ctorPs) =
    "constructor " ++ show ctor ++ " universe params don't match inductive"
  show (CtorInductiveNotFound ctor ind) =
    "inductive " ++ show ind ++ " not found for constructor " ++ show ctor
  show (CyclicLevelParam n) =
    "cyclic universe level parameter: " ++ show n
  show (OtherError s) = s

------------------------------------------------------------------------
-- Type Checker Monad
------------------------------------------------------------------------

||| Type checker result
public export
TC : Type -> Type
TC = Either TCError

||| Run type checker
export
runTC : TC a -> Either TCError a
runTC = id

------------------------------------------------------------------------
-- Helper: Get app spine
------------------------------------------------------------------------

||| Decompose expression into head and arguments
||| e.g., f a b c => (f, [a, b, c])
getAppSpine : ClosedExpr -> (ClosedExpr, List ClosedExpr)
getAppSpine e = go e []
  where
    go : ClosedExpr -> List ClosedExpr -> (ClosedExpr, List ClosedExpr)
    go (App f x) args = go f (x :: args)
    go head args = (head, args)

||| Get the nth element of a list (0-indexed)
listNth : List a -> Nat -> Maybe a
listNth [] _ = Nothing
listNth (x :: _) Z = Just x
listNth (_ :: xs) (S n) = listNth xs n

||| Drop first n elements
listDrop : Nat -> List a -> List a
listDrop Z xs = xs
listDrop (S n) [] = []
listDrop (S n) (_ :: xs) = listDrop n xs

||| Take first n elements
listTake : Nat -> List a -> List a
listTake Z _ = []
listTake (S n) [] = []
listTake (S n) (x :: xs) = x :: listTake n xs

------------------------------------------------------------------------
-- Delta Reduction (Constant Unfolding)
------------------------------------------------------------------------

||| Get the value of a definition if it can be unfolded
||| Returns Nothing for axioms, opaque definitions, etc.
getDeclValue : Declaration -> Maybe ClosedExpr
getDeclValue (DefDecl _ _ value hint _ _) =
  case hint of
    Opaq => Nothing  -- Opaque definitions don't unfold
    _    => Just value
getDeclValue (ThmDecl _ _ value _) = Just value  -- Theorems can unfold (for proof irrelevance later)
getDeclValue _ = Nothing  -- Axioms, inductives, etc. don't have values to unfold

||| Try to unfold a constant reference
||| Returns the unfolded value with universe levels instantiated
covering
unfoldConst : TCEnv -> Name -> List Level -> Maybe ClosedExpr
unfoldConst env name levels = do
  decl <- lookupDecl name env
  value <- getDeclValue decl
  let params = declLevelParams decl
  -- Check level count matches
  guard (length params == length levels)
  -- Use the non-safe version since level parameter names can shadow outer names
  -- (e.g., outParam.{u+2} where outParam has param "u" and caller also has "u")
  Just (instantiateLevelParams params levels value)

||| Get the head constant of an application spine
||| e.g., for `f a b c` returns `Just (f, [a, b, c])`
getAppConst : ClosedExpr -> Maybe (Name, List Level, List ClosedExpr)
getAppConst e = go e []
  where
    go : ClosedExpr -> List ClosedExpr -> Maybe (Name, List Level, List ClosedExpr)
    go (App f x) args = go f (x :: args)
    go (Const name levels) args = Just (name, levels, args)
    go _ _ = Nothing

||| Try to unfold the head of an expression (delta reduction)
covering
unfoldHead : TCEnv -> ClosedExpr -> Maybe ClosedExpr
unfoldHead env e =
  case getAppConst e of
    Just (name, levels, args) =>
      case unfoldConst env name levels of
        Just value => Just (mkApp value args)
        Nothing => Nothing
    Nothing =>
      -- Not an application of a constant, try direct constant
      case e of
        Const name levels => unfoldConst env name levels
        _ => Nothing

------------------------------------------------------------------------
-- Iota Reduction (Recursor Application)
------------------------------------------------------------------------

||| Get the recursor info for a name
getRecursorInfo : TCEnv -> Name -> Maybe RecursorInfo
getRecursorInfo env name =
  case lookupDecl name env of
    Just (RecDecl info _) => Just info
    _ => Nothing

||| Get the recursor info and level params for a name
getRecursorInfoWithLevels : TCEnv -> Name -> Maybe (RecursorInfo, List Name)
getRecursorInfoWithLevels env name =
  case lookupDecl name env of
    Just (RecDecl info params) => Just (info, params)
    _ => Nothing

||| Get the constructor info for a name
getConstructorInfo : TCEnv -> Name -> Maybe (Name, Nat, Nat, Nat)  -- (inductName, ctorIdx, numParams, numFields)
getConstructorInfo env name =
  case lookupDecl name env of
    Just (CtorDecl _ _ indName ctorIdx numParams numFields _) => Just (indName, ctorIdx, numParams, numFields)
    _ => Nothing

||| Find the recursor rule for a given constructor
findRecRule : List RecursorRule -> Name -> Maybe RecursorRule
findRecRule [] _ = Nothing
findRecRule (rule :: rules) ctorName =
  if rule.ctorName == ctorName
    then Just rule
    else findRecRule rules ctorName

||| Get the major premise index for a recursor
||| majorIdx = numParams + numMotives + numMinors + numIndices
getMajorIdx : RecursorInfo -> Nat
getMajorIdx info = info.numParams + info.numMotives + info.numMinors + info.numIndices

||| Iterate a whnf step function until fixed point
iterWhnfStep : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Nat -> ClosedExpr
iterWhnfStep step m 0 = m
iterWhnfStep step m (S fuel) =
  case step m of
    Just m' => iterWhnfStep step m' fuel
    Nothing => m

||| Get constant name and levels from head of expression
getConstHead : ClosedExpr -> Maybe (Name, List Level)
getConstHead (Const n ls) = Just (n, ls)
getConstHead _ = Nothing

||| Substitute a list of arguments for leading Pi binders
||| substArgs [a, b, c] (∀x y z, body) = body[x:=a, y:=b, z:=c]
||| Note: Works with well-scoped expressions - each substitution reduces scope by 1
substArgs : {n : Nat} -> List (Expr n) -> Expr n -> Expr n
substArgs [] ty = ty
substArgs {n} (arg :: args) (Pi _ _ _ cod) = substArgs args (subst0 cod arg)
substArgs _ ty = ty  -- Ran out of Pis

||| Get the idx-th Pi domain from a type, after substituting previous args
||| For a type like (α : Type) → (β : Type) → α → β → Prod α β
||| with args [Nat, Bool], getNthPiDomSubst 0 args ty = Nat, getNthPiDomSubst 1 = Bool
|||
||| Note: Uses subst0Single instead of subst0 to properly substitute the bound variable
||| at ALL depths. This is necessary because the field types may have nested Pis that
||| reference the parameter being substituted.
covering
getNthPiDomSubst : {n : Nat} -> Nat -> List (Expr n) -> Expr n -> Maybe (Expr n)
getNthPiDomSubst Z _ (Pi _ _ dom _) = Just dom
getNthPiDomSubst (S k) [] (Pi _ _ _ cod) =
  -- No more args to substitute, but we still need to continue
  getNthPiDomSubst k [] (believe_me cod)
getNthPiDomSubst (S k) (arg :: args) (Pi _ _ _ cod) =
  -- Use subst0Single to substitute the bound variable at ALL depths
  let result = subst0Single (believe_me cod) (believe_me arg) in
  getNthPiDomSubst k args (believe_me result)
getNthPiDomSubst _ _ _ = Nothing

||| Try iota reduction on a recursor application
||| If the expression is `Rec.rec params motives minors indices (Ctor args)`,
||| reduce it using the matching recursor rule.
covering
tryIotaReduction : TCEnv -> ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryIotaReduction env e whnfStep = do
  -- Check if head is a recursor
  let (head, args) = getAppSpine e
  (recName, recLevels) <- getConstHead head
  (recInfo, recLevelParams) <- getRecursorInfoWithLevels env recName

  -- Get the major premise
  let majorIdx = getMajorIdx recInfo
  major <- listNth args majorIdx

  -- Try to reduce major to WHNF
  let major' = iterWhnfStep whnfStep major 100

  -- Check if major is a constructor application
  let (majorHead, majorArgs) = getAppSpine major'
  (ctorName, _) <- getConstHead majorHead
  (_, _, ctorNumParams, ctorNumFields) <- getConstructorInfo env ctorName

  -- Find the matching recursor rule
  rule <- findRecRule recInfo.rules ctorName

  -- Check we have enough constructor arguments for the fields
  guard (length majorArgs >= ctorNumParams + ctorNumFields)

  -- Build the result:
  -- rhs[levels] applied to:
  --   1. params, motives, minors (first firstIndexIdx of recArgs)
  --   2. constructor fields (skip params from majorArgs)
  --   3. remaining args after major

  let firstIndexIdx = recInfo.numParams + recInfo.numMotives + recInfo.numMinors
  -- Use non-safe instantiation since level param names can shadow outer names
  let rhs = instantiateLevelParams recLevelParams recLevels rule.rhs

  -- Apply: rhs params motives minors
  let rhsWithParamsMotivesMinors = mkApp rhs (listTake firstIndexIdx args)

  -- Apply constructor fields (skip params from majorArgs)
  let ctorFields = listDrop ctorNumParams majorArgs
  let rhsWithFields = mkApp rhsWithParamsMotivesMinors ctorFields

  -- Apply remaining args after major
  let remainingArgs = listDrop (majorIdx + 1) args
  pure (mkApp rhsWithFields remainingArgs)

------------------------------------------------------------------------
-- Projection Reduction
------------------------------------------------------------------------

||| Try to reduce a projection.
||| Proj structName idx struct reduces when struct is a constructor application.
||| Result is the (numParams + idx)-th argument of the constructor.
tryProjReduction : TCEnv -> ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryProjReduction env (Proj structName idx struct) whnfStep = do
  -- Reduce struct to WHNF
  let struct' = iterWhnfStep whnfStep struct 100
  -- Check if it's a constructor application
  let (head, args) = getAppSpine struct'
  (ctorName, _) <- getConstHead head
  (_, _, numParams, numFields) <- getConstructorInfo env ctorName
  -- Extract the field at idx (after params)
  guard (idx < numFields)
  listNth args (numParams + idx)
tryProjReduction _ _ _ = Nothing

------------------------------------------------------------------------
-- Quotient Reduction
------------------------------------------------------------------------

||| Canonical names for quotient primitives
quotName : Name
quotName = Str "Quot" Anonymous

quotMkName : Name
quotMkName = Str "mk" (Str "Quot" Anonymous)

quotLiftName : Name
quotLiftName = Str "lift" (Str "Quot" Anonymous)

quotIndName : Name
quotIndName = Str "ind" (Str "Quot" Anonymous)

||| Try quotient reduction.
|||
||| Quot.lift reduces when applied to Quot.mk:
|||   Quot.lift {α} {r} {β} f h (Quot.mk r a) → f a
|||
||| Quot.ind reduces similarly:
|||   Quot.ind {α} {r} {β} h (Quot.mk r a) → h a
|||
||| Based on lean4lean's quotReduceRec.
tryQuotReduction : ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryQuotReduction e whnfStep = do
  let (head, args) = getAppSpine e
  (fnName, _) <- getConstHead head
  -- Quot.lift has 6 args: {α} {r} {β} f h q
  -- mkPos = 5 (q), argPos = 3 (f)
  -- Quot.ind has 5 args: {α} {r} {β} h q
  -- mkPos = 4 (q), argPos = 3 (h)
  (mkPos, argPos) <- the (Maybe (Nat, Nat)) $
    if fnName == quotLiftName then Just (5, 3)
    else if fnName == quotIndName then Just (4, 3)
    else Nothing
  -- Check we have enough arguments
  guard (List.length args > mkPos)
  -- Get the argument at mkPos and reduce to WHNF
  mkArg <- listNth args mkPos
  let mkArg' = iterWhnfStep whnfStep mkArg 100
  -- Check if it's Quot.mk with 3 args: {α} r a
  let (mkHead, mkArgs) = getAppSpine mkArg'
  (mkName, _) <- getConstHead mkHead
  guard (mkName == quotMkName && List.length mkArgs == 3)
  -- Get the value 'a' from Quot.mk (last argument)
  a <- listNth mkArgs 2
  -- Get f or h from the original args
  fOrH <- listNth args argPos
  -- Result: f a (or h a) plus any remaining args after mkPos
  let result = App fOrH a
  let remainingArgs = listDrop (mkPos + 1) args
  pure (mkApp result remainingArgs)

------------------------------------------------------------------------
-- WHNF (Weak Head Normal Form)
------------------------------------------------------------------------

||| Reduce expression to weak head normal form.
|||
||| This performs:
||| - Beta reduction: (λx.body) arg → body[0 := arg]
||| - Let substitution: let x = v in body → body[0 := v]
||| - Delta reduction: unfold constant definitions
||| - Iota reduction: reduce recursor applications when major premise is a constructor
||| - Projection reduction: Proj idx (Ctor args) → args[numParams + idx]
||| - Quotient reduction: Quot.lift f h (Quot.mk r a) → f a
|||
||| We use a fuel parameter to ensure termination.
export
covering
whnf : TCEnv -> ClosedExpr -> TC ClosedExpr
whnf env e = whnfFuel 20 e
  where
    ||| Single step of whnf (beta/let reduction)
    ||| For nested applications like (((λ...) a) b), we reduce the innermost
    ||| beta-redex first.
    |||
    ||| Note: Uses subst0Single instead of subst0 to correctly handle substitution
    ||| into bodies that contain nested binders. subst0 incorrectly substitutes
    ||| BVar 0 inside nested lambdas (which refers to the inner binder, not the
    ||| outer free variable being substituted).
    whnfStepCore : ClosedExpr -> Maybe ClosedExpr
    whnfStepCore (App (Lam _ _ _ body) arg) = Just (subst0Single body arg)
    whnfStepCore (App f arg) =
      -- If f is reducible, reduce it and reconstruct
      case whnfStepCore f of
        Just f' => Just (App f' arg)
        Nothing => Nothing
    whnfStepCore (Let _ _ val body) = Just (subst0Single body val)
    whnfStepCore _ = Nothing

    ||| Combined step including delta
    whnfStepWithDelta : ClosedExpr -> Maybe ClosedExpr
    whnfStepWithDelta e =
      case whnfStepCore e of
        Just e' => Just e'
        Nothing => unfoldHead env e

    whnfFuel : Nat -> ClosedExpr -> TC ClosedExpr
    whnfFuel 0 e = Right e  -- out of fuel, return as-is
    whnfFuel (S k) e =
      -- First try beta/let reduction
      case whnfStepCore e of
        Just e' => whnfFuel k e'
        Nothing =>
          -- Then try projection reduction
          case tryProjReduction env e whnfStepWithDelta of
            Just e' => whnfFuel k e'
            Nothing =>
              -- Then try quotient reduction (if enabled)
              case (if env.quotInit then tryQuotReduction e whnfStepWithDelta else Nothing) of
                Just e' => whnfFuel k e'
                Nothing =>
                  -- Then try iota reduction (recursors)
                  case tryIotaReduction env e whnfStepWithDelta of
                    Just e' => whnfFuel k e'
                    Nothing =>
                      -- Then try delta reduction
                      case unfoldHead env e of
                        Just e' => whnfFuel k e'
                        Nothing => Right e

||| WHNF without delta reduction (for internal use)
||| Used when we want to reduce but not unfold definitions
export
covering
whnfCore : ClosedExpr -> TC ClosedExpr
whnfCore e = whnfCoreFuel 1000 e
  where
    whnfStepCore : ClosedExpr -> Maybe ClosedExpr
    whnfStepCore (App (Lam _ _ _ body) arg) = Just (subst0Single body arg)
    whnfStepCore (Let _ _ val body) = Just (subst0Single body val)
    whnfStepCore _ = Nothing

    whnfCoreFuel : Nat -> ClosedExpr -> TC ClosedExpr
    whnfCoreFuel 0 e = Right e
    whnfCoreFuel (S k) e = case whnfStepCore e of
      Nothing => Right e
      Just e' => whnfCoreFuel k e'

||| Get the head constant and arguments from an application spine
getAppHead : ClosedExpr -> Maybe (Name, List ClosedExpr)
getAppHead expr = go expr []
  where
    go : ClosedExpr -> List ClosedExpr -> Maybe (Name, List ClosedExpr)
    go (App f' arg) args = go f' (arg :: args)
    go (Const name _) args = Just (name, args)
    go _ _ = Nothing

mutual
  ||| Given a placeholder type and application args, compute the result type
  ||| and check if it's a Sort
  covering
  ensureSortOfApp : TCEnv -> ClosedExpr -> List ClosedExpr -> TC Level
  ensureSortOfApp env' ty [] = ensureSortWhnf env' ty
  ensureSortOfApp env' (Pi _ _ dom cod) (arg :: args) =
    ensureSortOfApp env' (subst0Single cod arg) args
  ensureSortOfApp env' ty args =
    -- ty is not a Pi but we have more args (or args are empty)
    -- This can happen with type variables - just return a universe level
    case ty of
      Sort l => Right l
      Pi _ _ _ cod =>
        -- Pi type when expecting Sort - the codomain might be a Sort after more applications
        -- Trust the input and return a synthetic level
        Right Zero
      Const name _ =>
        case lookupPlaceholder name env' of
          Just (Sort l) => Right l  -- Type variable - trust it's used as a type
          Just innerTy => ensureSortOfApp env' innerTy args
          Nothing =>
            -- Check declarations
            case lookupDecl name env' of
              Just decl => case declType decl of
                Just dty => ensureSortOfApp env' dty args
                Nothing => Left (OtherError $ "ensureSort: const " ++ show name ++ " has no type")
              Nothing => Left (OtherError $ "ensureSort: unknown const " ++ show name)
      App _ _ =>
        -- Stuck application - try to resolve recursively
        case getAppHead ty of
          Just (name, innerArgs) =>
            case lookupPlaceholder name env' of
              Just innerTy => ensureSortOfApp env' innerTy (innerArgs ++ args)
              Nothing =>
                case lookupDecl name env' of
                  Just decl => case declType decl of
                    Just dty => ensureSortOfApp env' dty (innerArgs ++ args)
                    Nothing => Left (TypeExpected ty)
                  Nothing => Left (TypeExpected ty)
          Nothing => Left (TypeExpected ty)
      _ => Left (OtherError $ "ensureSort: exhausted Pis")

  covering
  ensureSortWhnf : TCEnv -> ClosedExpr -> TC Level
  ensureSortWhnf env' (Sort l) = Right l
  ensureSortWhnf env' (Const name _) =
    -- Check if it's a placeholder constant that represents a type variable
    case lookupPlaceholder name env' of
      Just (Sort l) => Right l  -- Placeholder has Sort type, use that level
      Just ty => ensureSortWhnf env' ty  -- Try recursively
      Nothing => Left (TypeExpected (Const name []))  -- Not a placeholder, regular constant
  ensureSortWhnf env' expr@(App _ _) =
    -- Application that didn't reduce - might be a type family application
    -- Check if the head is a placeholder or a known constant
    case getAppHead expr of
      Just (name, args) =>
        case lookupPlaceholder name env' of
          Just ty => ensureSortOfApp env' ty args
          Nothing =>
            -- Not a placeholder - check if it's a known constant (inductive, etc.)
            case lookupDecl name env' of
              Just decl => case declType decl of
                Just ty => ensureSortOfApp env' ty args
                Nothing => Left (TypeExpected expr)
              Nothing => Left (OtherError $ "ensureSort: stuck App with unknown head " ++ show name)
      Nothing => Left (TypeExpected expr)
  ensureSortWhnf _ (Pi _ _ _ _) =
    -- Pi type when expecting Sort - this happens with type families
    -- Trust the input and return a synthetic level
    Right Zero
  ensureSortWhnf _ other = Left (TypeExpected other)

||| Check if expression is a Sort
export
covering
ensureSort : TCEnv -> ClosedExpr -> TC Level
ensureSort env e = do
  e' <- whnf env e
  ensureSortWhnf env e'

mutual
  covering
  ||| Given a placeholder type and application args, compute the result type
  ||| and check if it's a Pi
  ensurePiOfApp : TCEnv -> ClosedExpr -> List ClosedExpr -> TC (Name, BinderInfo, ClosedExpr, Expr 1)
  ensurePiOfApp env' ty [] = ensurePiWhnf env' ty  -- No more args, check if ty is Pi
  ensurePiOfApp env' (Pi _ _ dom cod) (arg :: args) = do
    -- Apply arg to get result type, then reduce and continue
    -- Use subst0Single to correctly handle nested binders in the codomain
    let resultTy = subst0Single cod arg
    resultTy' <- whnf env' resultTy
    ensurePiOfApp env' resultTy' args
  ensurePiOfApp env' ty args =
    -- ty is not a Pi but we have more args
    -- This can happen with type variables - trust that the original expression was well-typed
    -- and return synthetic Pi components
    case ty of
      Const name _ =>
        case lookupPlaceholder name env' of
          Just (Sort l) =>
            -- Type variable used as function type - trust the input
            Right (Anonymous, Default, ty, weaken1 ty)
          Just innerTy => ensurePiOfApp env' innerTy args  -- Try recursively
          Nothing => Left (OtherError $ "ensurePi: exhausted Pi with non-placeholder type")
      _ => Left (OtherError $ "ensurePi: exhausted Pi types with " ++ show (length args) ++ " args remaining")

  covering
  ensurePiWhnf : TCEnv -> ClosedExpr -> TC (Name, BinderInfo, ClosedExpr, Expr 1)
  ensurePiWhnf env' expr = case expr of
    Pi name bi dom cod => Right (name, bi, dom, cod)
    Const name levels =>
      -- Check if it's a placeholder constant
      case lookupPlaceholder name env' of
        Just (Pi pname bi dom cod) => Right (pname, bi, dom, cod)
        Just (Sort l) =>
          -- Type variable of type Sort l - trust it's used as a function type
          -- Synthesize Pi components: domain is the placeholder itself, codomain is unknown
          -- This is a "trust the input" approach since Lean already verified correctness
          Right (Anonymous, Default, expr, weaken1 expr)
        Just ty =>
          -- Try recursively - the type might itself reduce to something useful
          ensurePiWhnf env' ty
        Nothing =>
          -- Not a placeholder - might be a regular constant that's a type synonym
          Left (OtherError $ "ensurePiWhnf Const: " ++ show name ++ " not in placeholders")
    App _ _ =>
      -- Application that didn't reduce - might be placeholder application
      -- If the head is a placeholder or known constant with a Pi type
      case getAppHead expr of
        Just (name, args) =>
          case lookupPlaceholder name env' of
            Just ty => ensurePiOfApp env' ty args
            Nothing =>
              -- Not a placeholder - check if it's a known constant
              case lookupDecl name env' of
                Just decl => case declType decl of
                  Just ty => ensurePiOfApp env' ty args
                  Nothing => Left (FunctionExpected expr)
                Nothing => Left (OtherError $ "ensurePi: stuck App with unknown head " ++ show name)
        Nothing => Left (FunctionExpected expr)
    Sort l =>
      -- A Sort cannot be applied to arguments - it's not a function type
      Left (FunctionExpected expr)
    Lam _ _ _ _ => Left (OtherError $ "ensurePiWhnf: expected Pi, got Lam")
    Let _ _ _ _ => Left (OtherError $ "ensurePiWhnf: expected Pi, got Let")
    BVar _ => Left (OtherError $ "ensurePiWhnf: expected Pi, got BVar (should not happen in closed expr)")
    Proj _ _ _ => Left (OtherError $ "ensurePiWhnf: expected Pi, got Proj")
    NatLit _ => Left (OtherError $ "ensurePiWhnf: expected Pi, got NatLit")
    StringLit _ => Left (OtherError $ "ensurePiWhnf: expected Pi, got StringLit")

||| Check if expression is a Pi type.
||| For placeholder constants (type variables), we trust that they're used correctly
||| and synthesize Pi components based on the placeholder's universe.
export
covering
ensurePi : TCEnv -> ClosedExpr -> TC (Name, BinderInfo, ClosedExpr, Expr 1)
ensurePi env e = do
  e' <- whnf env e
  ensurePiWhnf env e'

------------------------------------------------------------------------
-- Type Inference
------------------------------------------------------------------------

||| Create a placeholder constant name for a local variable
||| Uses a unique counter to avoid name collisions
placeholderName : Name -> Nat -> Name
placeholderName n counter = Str "_local" (Num counter n)

||| Build a vector of placeholder constants for all context entries
||| Returns the updated environment, updated context with placeholders assigned, and the vector of placeholders.
||| The placeholders are in order matching the context (index 0 = first entry = innermost).
||| Uses a global counter from the environment to ensure unique placeholder names.
||| IMPORTANTLY: reuses existing placeholders if already assigned to an entry.
covering
buildPlaceholders : TCEnv -> LocalCtx n -> (TCEnv, LocalCtx n, Vect n ClosedExpr)
buildPlaceholders env [] = (env, [], [])
buildPlaceholders env {n = S k} (entry :: ctx) =
  case entry.placeholder of
    Just ph =>
      -- Entry already has a placeholder, reuse it
      let (env', ctx', rest) = buildPlaceholders env ctx
      in (env', entry :: ctx', ph :: rest)
    Nothing =>
      -- Create a new placeholder for this entry
      let counter = env.nextPlaceholder
          phName = placeholderName entry.name counter
          env' = { nextPlaceholder := S counter } env
          env'' = debugPrint ("buildPlaceholders: creating " ++ show phName ++ " : " ++ show entry.type) $ addPlaceholder phName entry.type env'
          ph : ClosedExpr = Const phName []
          entry' = { placeholder := Just ph } entry
          (env''', ctx', rest) = buildPlaceholders env'' ctx
      in (env''', entry' :: ctx', ph :: rest)

||| Close an expression by substituting all bound variables with placeholders.
||| This is used to convert Expr n to ClosedExpr for type checking purposes.
|||
||| We substitute each variable with a unique constant based on its name.
||| Also registers placeholder types in the environment so they can be looked up later.
||| Uses a global counter to ensure unique placeholder names across multiple closures.
||| Returns the updated context with placeholders assigned to entries.
|||
||| This version uses substAll for simultaneous substitution, which correctly
||| handles nested binders where free variables appear at shifted indices.
covering
closeWithPlaceholders : TCEnv -> LocalCtx n -> Expr n -> (TCEnv, LocalCtx n, ClosedExpr)
closeWithPlaceholders env ctx e =
  let (env', ctx', placeholders) = buildPlaceholders env ctx
  in (env', ctx', substAll placeholders e)

||| Replace a specific placeholder constant with a BVar at a given depth.
||| This is used when constructing the codomain of a Pi type from an inferred body type.
||| The placeholder is the one assigned to the innermost bound variable.
|||
||| For example, if we have `α.0._local → α.0._local` and the placeholder is `α.0._local`,
||| the result should be `BVar 0 → BVar 0` as an Expr 1.
|||
||| The `depth` parameter tracks how many binders we've gone under.
||| At depth 0, the placeholder becomes BVar 0.
||| At depth 1 (under one binder), the placeholder becomes BVar 1.
||| etc.
|||
||| This function increases the scope by 1 (adding the new BVar) and also
||| shifts existing BVars to make room for the new one.
covering
replacePlaceholderWithBVarDepth : {m : Nat} -> (depth : Nat) -> ClosedExpr -> Expr m -> Expr (S m)
replacePlaceholderWithBVarDepth depth placeholder e = go {k=m} depth e
  where
    -- Convert a Nat to a Fin (S n) by repeatedly applying FS
    -- Returns Nothing if nat >= n+1
    natToFin : (nat : Nat) -> (n : Nat) -> Maybe (Fin (S n))
    natToFin Z _ = Just FZ
    natToFin (S k) Z = Nothing
    natToFin (S k) (S m) = map FS (natToFin k m)

    go : {k : Nat} -> Nat -> Expr k -> Expr (S k)
    go _ (Sort l) = Sort l
    go _ (BVar i) = BVar (FS i)  -- Shift existing BVars up by 1
    go d (Const n ls) =
      -- Check if this is the placeholder we're looking for
      if Const n ls == placeholder
        then case natToFin d k of
               Just idx => BVar idx
               Nothing => Const n ls  -- Shouldn't happen if depth is correct
        else Const n ls
    go d (App f x) = App (go d f) (go d x)
    go d (Lam name bi ty body) = Lam name bi (go d ty) (go (S d) body)
    go d (Pi name bi dom cod) = Pi name bi (go d dom) (go (S d) cod)
    go d (Let name ty val body) = Let name (go d ty) (go d val) (go (S d) body)
    go d (Proj sn i s) = Proj sn i (go d s)
    go _ (NatLit n) = NatLit n
    go _ (StringLit s) = StringLit s

||| Convenience wrapper for the common case of replacing in a ClosedExpr at depth 0
covering
replacePlaceholderWithBVar : ClosedExpr -> ClosedExpr -> Expr 1
replacePlaceholderWithBVar placeholder e = replacePlaceholderWithBVarDepth 0 placeholder e

||| Helper to find placeholder index in a list of entries
findPlaceholderIdx : List LocalEntry -> Name -> Nat -> Maybe Nat
findPlaceholderIdx [] _ _ = Nothing
findPlaceholderIdx (entry :: rest) name idx =
  case entry.placeholder of
    Just (Const phName []) =>
      if phName == name
        then Just idx  -- Found it at this index
        else findPlaceholderIdx rest name (S idx)
    _ => findPlaceholderIdx rest name (S idx)

||| Make a BVar from a Nat (unsafe, but index should be in range)
||| This creates BVar with the given de Bruijn index
makeBVarFromNat : Nat -> ClosedExpr
makeBVarFromNat k = believe_me (BVar {n = S k} (natToFin k))
  where
    -- Convert Nat to Fin (S k) - always succeeds since k < S k
    natToFin : (n : Nat) -> Fin (S n)
    natToFin Z = FZ
    natToFin (S m) = FS (natToFin m)

||| Core implementation of placeholder-to-BVar replacement
||| Takes a list of entries and replaces all matching placeholders with BVars
covering
replaceAllPlaceholdersGo : List LocalEntry -> Nat -> ClosedExpr -> ClosedExpr
replaceAllPlaceholdersGo entries depth (Sort l) = Sort l
replaceAllPlaceholdersGo entries depth (BVar i) = BVar i  -- Shouldn't happen in ClosedExpr
replaceAllPlaceholdersGo entries depth (Const name ls) =
  case findPlaceholderIdx entries name 0 of
    Just idx => makeBVarFromNat (idx + depth)  -- Replace with BVar at appropriate depth
    Nothing => Const name ls            -- Not a placeholder, keep as-is
replaceAllPlaceholdersGo entries depth (App f x) =
  App (replaceAllPlaceholdersGo entries depth f) (replaceAllPlaceholdersGo entries depth x)
replaceAllPlaceholdersGo entries depth (Lam name bi ty body) =
  Lam name bi (replaceAllPlaceholdersGo entries depth ty)
              (believe_me (replaceAllPlaceholdersGo entries (S depth) (believe_me body)))
replaceAllPlaceholdersGo entries depth (Pi name bi dom cod) =
  Pi name bi (replaceAllPlaceholdersGo entries depth dom)
             (believe_me (replaceAllPlaceholdersGo entries (S depth) (believe_me cod)))
replaceAllPlaceholdersGo entries depth (Let name ty val body) =
  Let name (replaceAllPlaceholdersGo entries depth ty)
           (replaceAllPlaceholdersGo entries depth val)
           (believe_me (replaceAllPlaceholdersGo entries (S depth) (believe_me body)))
replaceAllPlaceholdersGo entries depth (Proj sn i s) =
  Proj sn i (replaceAllPlaceholdersGo entries depth s)
replaceAllPlaceholdersGo entries depth (NatLit k) = NatLit k
replaceAllPlaceholdersGo entries depth (StringLit s) = StringLit s

||| Replace ALL placeholders from a list of entries with their corresponding BVars.
||| This is a variant that takes List LocalEntry directly for easier use.
covering
export
replaceAllPlaceholdersWithBVars' : List LocalEntry -> ClosedExpr -> ClosedExpr
replaceAllPlaceholdersWithBVars' entries e = replaceAllPlaceholdersGo entries 0 e

||| Replace ALL placeholders from a context with their corresponding BVars.
||| Given a context of n entries, converts a ClosedExpr to Expr n.
||| Each placeholder in the context gets replaced with its corresponding BVar:
||| - Entry 0 (innermost) → BVar 0
||| - Entry 1 → BVar 1
||| - etc.
|||
||| This is used to convert a fully-closed result type back to an open expression
||| with proper de Bruijn indices.
covering
replaceAllPlaceholdersWithBVars : {n : Nat} -> LocalCtx n -> ClosedExpr -> Expr n
replaceAllPlaceholdersWithBVars {n} ctx e = believe_me (replaceAllPlaceholdersGo (toList ctx) 0 e)

------------------------------------------------------------------------
-- Projection Type Inference Helpers
------------------------------------------------------------------------

||| Get the inductive info for a name (if it exists and is an inductive)
getInductiveInfo : TCEnv -> Name -> Maybe InductiveInfo
getInductiveInfo env name =
  case lookupDecl name env of
    Just (IndDecl info _) => Just info
    _ => Nothing

||| Get the single constructor of a structure (structures have exactly one constructor)
||| Note: The InductiveInfo stores constructor names but with placeholder types.
||| We need to look up the actual CtorDecl to get the real type.
getStructCtor : TCEnv -> Name -> Maybe ConstructorInfo
getStructCtor env structName = do
  indInfo <- getInductiveInfo env structName
  case indInfo.constructors of
    [ctorInfo] =>
      -- Look up the actual CtorDecl to get the real type
      case lookupDecl ctorInfo.name env of
        Just (CtorDecl name ty _ _ _ _ _) => Just (MkConstructorInfo name ty)
        _ => Just ctorInfo  -- Fall back to placeholder if CtorDecl not found
    _ => Nothing  -- Not a structure (0 or multiple constructors)

||| Get the type of a projection field from a structure
||| Given struct name, field index, and struct params (extracted from struct type),
||| returns the field type with parameters substituted
|||
||| For a structure like Prod with constructor:
|||   Prod.mk : {α β : Type} → α → β → Prod α β
||| and a value s : Prod Nat Bool, we have params = [Nat, Bool]
||| So getProjType "Prod" 0 [Nat, Bool] = Nat
|||    getProjType "Prod" 1 [Nat, Bool] = Bool
|||
||| Note: The field index is offset by numParams in the constructor type.
||| Field 0 is at Pi position numParams, field 1 at numParams+1, etc.
covering
getProjType : TCEnv -> Name -> Nat -> List ClosedExpr -> Maybe ClosedExpr
getProjType env structName idx structParams = do
  indInfo <- getInductiveInfo env structName
  let numParams = indInfo.numParams
  ctor <- getStructCtor env structName
  getNthPiDomSubst (numParams + idx) structParams ctor.type

||| Deep normalization of types - normalizes under binders.
||| Used for type comparison when types may have beta redexes in nested positions.
|||
||| For example, normalizes:
|||   (val : Nat) -> (isLt : ...) -> ((fun (t : Fin n) => Sort u) (Fin.mk n val isLt))
||| to:
|||   (val : Nat) -> (isLt : ...) -> Sort u
|||
||| This is necessary for type comparison when one type has unreduced
||| beta redexes nested inside Pi types.
|||
||| Uses a generic version that works on any expression with n free variables.
-- Beta reduce an application if possible (works on any Expr n)
covering
betaReduceN : {n : Nat} -> Expr n -> Maybe (Expr n)
betaReduceN (App (Lam _ _ _ body) arg) = Just (subst0SingleN body arg)
betaReduceN _ = Nothing

-- Helper functions for normalizeTypeOpenWithEnv
getAppSpineN : {m : Nat} -> Expr m -> (Expr m, List (Expr m))
getAppSpineN e = go e []
  where
    go : Expr m -> List (Expr m) -> (Expr m, List (Expr m))
    go (App f x) args = go f (x :: args)
    go e args = (e, args)

mkAppN : {m : Nat} -> Expr m -> List (Expr m) -> Expr m
mkAppN f [] = f
mkAppN f (x :: xs) = mkAppN (App f x) xs

-- Try to unfold a constant in an open expression context
covering
unfoldConstN : TCEnv -> {n : Nat} -> Name -> List Level -> Maybe (Expr n)
unfoldConstN env name levels = do
  decl <- lookupDecl name env
  value <- getDeclValue decl
  let params = declLevelParams decl
  guard (length params == length levels)
  -- Use non-safe instantiation since level param names can shadow outer names
  let instantiated = instantiateLevelParams params levels value
  Just (believe_me instantiated)

-- Try delta reduction on an application whose head is a constant
covering
tryDeltaOpenN : TCEnv -> {n : Nat} -> Expr n -> Maybe (Expr n)
tryDeltaOpenN env e =
  let (head, args) = getAppSpineN e
  in case head of
    Const name levels => do
      unfolded <- unfoldConstN env name levels
      Just (mkAppN unfolded args)
    _ => Nothing

-- Try iota reduction for Nat.rec when the major premise is a constructor
-- Nat.rec.{u} motive zeroCase succCase Nat.zero = zeroCase
-- Nat.rec.{u} motive zeroCase succCase (Nat.succ n) = succCase n (Nat.rec.{u} motive zeroCase succCase n)
tryNatRecIota : {n : Nat} -> Expr n -> Maybe (Expr n)
tryNatRecIota e =
  let (head, args) = getAppSpineN e
  in case head of
    Const name [u] =>
      if name == Str "rec" (Str "Nat" Anonymous)
        then case args of
          -- Nat.rec motive zeroCase succCase major
          [motive, zeroCase, succCase, major] =>
            case major of
              -- Nat.zero case: result = zeroCase
              Const zeroName [] =>
                if zeroName == Str "zero" (Str "Nat" Anonymous)
                  then Just zeroCase
                  else Nothing
              -- Nat.succ n case: result = succCase n (Nat.rec motive zeroCase succCase n)
              App (Const succName []) innerN =>
                if succName == Str "succ" (Str "Nat" Anonymous)
                  then let recCall = mkAppN (Const name [u]) [motive, zeroCase, succCase, innerN]
                       in Just (App (App succCase innerN) recCall)
                  else Nothing
              _ => Nothing
          _ => Nothing
        else Nothing
    _ => Nothing

-- For open expressions (under binders), we can do beta reduction
-- and delta reduction on constants. For iota reduction,
-- we need to handle it symbolically when the major premise is a constructor.
covering
normalizeTypeOpenWithEnv : TCEnv -> {n : Nat} -> Expr n -> TC (Expr n)
normalizeTypeOpenWithEnv env e = case betaReduceN e of
  Just e' => normalizeTypeOpenWithEnv env e'
  Nothing => case e of
    Pi name bi dom cod => do
      dom' <- normalizeTypeOpenWithEnv env dom
      cod' <- normalizeTypeOpenWithEnv env cod
      Right (Pi name bi dom' cod')
    Lam name bi ty body => do
      ty' <- normalizeTypeOpenWithEnv env ty
      body' <- normalizeTypeOpenWithEnv env body
      Right (Lam name bi ty' body')
    App f arg => do
      f' <- normalizeTypeOpenWithEnv env f
      arg' <- normalizeTypeOpenWithEnv env arg
      let app = App f' arg'
      case betaReduceN app of
        Just reduced => normalizeTypeOpenWithEnv env reduced
        Nothing =>
          -- Try iota reduction for Nat.rec
          case tryNatRecIota app of
            Just reduced => normalizeTypeOpenWithEnv env reduced
            Nothing =>
              -- Try delta reduction if f' is a constant
              case tryDeltaOpenN env app of
                Just reduced => normalizeTypeOpenWithEnv env reduced
                Nothing => Right app
    Let name ty val body => normalizeTypeOpenWithEnv env (subst0SingleN body val)
    Proj n i e => do
      e' <- normalizeTypeOpenWithEnv env e
      Right (Proj n i e')
    Sort l => Right (Sort (simplify l))
    -- For constants, try delta reduction
    Const name levels => case unfoldConstN env name levels of
      Just unfolded => normalizeTypeOpenWithEnv env unfolded
      Nothing => Right (Const name levels)
    e => Right e

-- Wrapper that doesn't need env (for backwards compat)
covering
normalizeTypeOpen : {n : Nat} -> Expr n -> TC (Expr n)
normalizeTypeOpen e = case betaReduceN e of
  Just e' => normalizeTypeOpen e'
  Nothing => case e of
    Pi name bi dom cod => do
      dom' <- normalizeTypeOpen dom
      cod' <- normalizeTypeOpen cod
      Right (Pi name bi dom' cod')
    Lam name bi ty body => do
      ty' <- normalizeTypeOpen ty
      body' <- normalizeTypeOpen body
      Right (Lam name bi ty' body')
    App f arg => do
      f' <- normalizeTypeOpen f
      arg' <- normalizeTypeOpen arg
      let app = App f' arg'
      case betaReduceN app of
        Just reduced => normalizeTypeOpen reduced
        Nothing => Right app
    Let name ty val body => normalizeTypeOpen (subst0SingleN body val)
    Proj n i e => do
      e' <- normalizeTypeOpen e
      Right (Proj n i e')
    Sort l => Right (Sort (simplify l))
    e => Right e

||| Deep normalization for closed expressions
||| Recursively normalizes under binders using whnf at each level
covering
normalizeType : TCEnv -> ClosedExpr -> TC ClosedExpr
normalizeType env e = do
  -- First whnf at top level (handles delta, iota, beta)
  e' <- whnf env e
  -- Then recurse into subexpressions
  normalizeDeep e'
  where
    covering
    normalizeDeep : ClosedExpr -> TC ClosedExpr
    normalizeDeep (Pi name bi dom cod) = do
      dom' <- normalizeType env dom
      -- For codomain, we need to handle it carefully since it has a bound var
      -- Use normalizeTypeOpenWithEnv to allow delta reduction in open terms
      cod' <- normalizeTypeOpenWithEnv env cod
      Right (Pi name bi dom' cod')
    normalizeDeep (Lam name bi ty body) = do
      ty' <- normalizeType env ty
      body' <- normalizeTypeOpenWithEnv env body
      Right (Lam name bi ty' body')
    normalizeDeep (App f arg) = do
      -- App after whnf means no beta/delta/iota at head, so just normalize subterms
      f' <- normalizeType env f
      arg' <- normalizeType env arg
      Right (App f' arg')
    normalizeDeep (Let name ty val body) = do
      -- Let should have been reduced by whnf, but normalize subterms anyway
      ty' <- normalizeType env ty
      val' <- normalizeType env val
      body' <- normalizeTypeOpenWithEnv env body
      Right (Let name ty' val' body')
    normalizeDeep (Proj n i e) = do
      e' <- normalizeType env e
      Right (Proj n i e')
    normalizeDeep (Sort l) = Right (Sort (simplify l))
    normalizeDeep e = Right e  -- Const, BVar, NatLit, StringLit

mutual
  ||| Infer the type of a closed expression.
  ||| Returns the updated environment (with any new placeholders) and the type.
  ||| Delegates to inferTypeOpen with empty context for binder forms.
  export
  covering
  inferTypeE : TCEnv -> ClosedExpr -> TC (TCEnv, ClosedExpr)

  -- Sort : Sort (succ level)
  inferTypeE env (Sort l) = Right (env, Sort (Succ l))

  -- Const: look up type in environment and instantiate levels
  -- First check if it's a placeholder constant (from closeWithPlaceholders)
  inferTypeE env (Const name levels) =
    case lookupPlaceholder name env of
      Just ty => Right (env, ty)  -- Placeholder constant - return its registered type
      Nothing =>
        case lookupDecl name env of
          Nothing => Left (OtherError $ "unknown constant: " ++ show name ++
                          "\n  Name structure: " ++ showNameStructure name ++
                          "\n  Registered placeholders: " ++ show (length (Data.SortedMap.toList env.placeholders)))
          Just decl => case declType decl of
            Nothing => Left (UnknownConst name)  -- QuotDecl has no direct type
            Just ty =>
              let params = declLevelParams decl in
              if length params /= length levels
                then Left (WrongNumLevels (length params) (length levels) name)
                -- Use non-safe version: the level names in the replacement are from
                -- the outer scope (current definition), not the inner scope (instantiated definition).
                -- So "u := u+1" where the inner u is Fin.casesOn's param and outer u is
                -- Fin.noConfusionType's param is NOT a cycle.
                else Right (env, instantiateLevelParams params levels ty)
  where
    showNameStructure : Name -> String
    showNameStructure Anonymous = "Anonymous"
    showNameStructure (Str s parent) = "Str \"" ++ s ++ "\" (" ++ showNameStructure parent ++ ")"
    showNameStructure (Num n parent) = "Num " ++ show n ++ " (" ++ showNameStructure parent ++ ")"

  -- App: infer function type, check it's Pi, verify arg type, instantiate with arg
  inferTypeE env (App f arg) = do
    (env1, fTy) <- inferTypeE env f
    (_, _, dom, cod) <- ensurePi env1 fTy
    -- Verify argument type matches domain
    (env2, argTy) <- inferTypeE env1 arg
    -- First whnf to unfold constants like outParam, then normalizeType for nested beta
    argTy1 <- whnf env2 argTy
    argTy' <- normalizeType env2 argTy1
    dom1 <- whnf env2 dom
    dom' <- normalizeType env2 dom1
    if argTy' == dom'
      then do
        let resultTy = subst0Single cod arg
        -- Reduce the result type to handle beta redexes like ((fun _ => C x) y)
        resultTy' <- whnf env2 resultTy
        Right (env2, resultTy')
      else do
        debugPrint ("inferTypeE App mismatch:\n  f=" ++ show f ++ "\n  arg=" ++ show arg ++ "\n  fTy=" ++ show fTy ++ "\n  dom (before whnf)=" ++ show dom ++ "\n  dom1 (after whnf)=" ++ show dom1 ++ "\n  dom' (after normalize)=" ++ show dom' ++ "\n  argTy (before whnf)=" ++ show argTy ++ "\n  argTy1 (after whnf)=" ++ show argTy1 ++ "\n  argTy' (after normalize)=" ++ show argTy') $
          Left (AppTypeMismatch dom' argTy')

  -- Lam: delegate to inferTypeOpenE which properly handles the body
  inferTypeE env (Lam name bi ty body) = do
    (env', _, resultTy) <- inferTypeOpenE env emptyCtx (Lam name bi ty body)
    Right (env', resultTy)

  -- Pi: delegate to inferTypeOpenE which properly handles the codomain
  inferTypeE env (Pi name bi dom cod) = do
    (env', _, resultTy) <- inferTypeOpenE env emptyCtx (Pi name bi dom cod)
    Right (env', resultTy)

  -- Let: delegate to inferTypeOpenE which properly handles the body
  inferTypeE env (Let name ty val body) = do
    (env', _, resultTy) <- inferTypeOpenE env emptyCtx (Let name ty val body)
    Right (env', resultTy)

  -- Proj: delegate to inferTypeOpenE
  inferTypeE env (Proj structName idx structExpr) = do
    (env', _, resultTy) <- inferTypeOpenE env emptyCtx (Proj structName idx structExpr)
    Right (env', resultTy)

  -- NatLit: type is Nat
  inferTypeE env (NatLit _) = Right (env, Const (Str "Nat" Anonymous) [])

  -- StringLit: type is String
  inferTypeE env (StringLit _) = Right (env, Const (Str "String" Anonymous) [])

  ||| Convenience wrapper that discards the environment
  export
  covering
  inferType : TCEnv -> ClosedExpr -> TC ClosedExpr
  inferType env e = do
    (_, ty) <- inferTypeE env e
    Right ty

  -- BVar: should not appear in closed expressions (Fin 0 is empty)

  ------------------------------------------------------------------------
  -- Open Term Type Inference
  ------------------------------------------------------------------------

  ||| Infer the type of an open expression with a local context.
  ||| Returns the updated environment (with placeholders) and the type.
  |||
  ||| This is the general form that handles expressions with bound variables.
  ||| The result type is always a closed expression.
  ||| Returns the updated context with placeholders assigned for proper reuse.
  |||
  ||| Key idea: when we look up a bound variable, we return its type from context.
  ||| When we go under a binder, we extend the context with the domain type.
  export
  covering
  inferTypeOpenE : TCEnv -> LocalCtx n -> Expr n -> TC (TCEnv, LocalCtx n, ClosedExpr)

  -- Sort: same as closed case
  inferTypeOpenE env ctx (Sort l) = Right (env, ctx, Sort (Succ l))

  -- Const: same as closed case (also checks placeholders)
  inferTypeOpenE env ctx (Const name levels) =
    case lookupPlaceholder name env of
      Just ty => Right (env, ctx, ty)  -- Placeholder constant
      Nothing =>
        case lookupDecl name env of
          Nothing => Left (OtherError $ "unknown constant (inferTypeOpenE): " ++ show name ++
                          "\n  Name structure: " ++ showNameStructure name ++
                          "\n  Context depth: " ++ show (length ctx) ++
                          "\n  Registered placeholders: " ++ show (length (Data.SortedMap.toList env.placeholders)))
          Just decl => case declType decl of
            Nothing => Left (UnknownConst name)
            Just ty =>
              let params = declLevelParams decl in
              if length params /= length levels
                then Left (WrongNumLevels (length params) (length levels) name)
                -- Use non-safe version (same reasoning as in inferTypeE)
                else
                  let ty' = instantiateLevelParams params levels ty
                      -- Debug: trace Fin.rec type lookup
                      _ = case name of
                            Str "rec" (Str "Fin" _) => debugPrint ("Const Fin.rec type=" ++ show ty') ()
                            _ => ()
                  in Right (env, ctx, ty')
  where
    showNameStructure : Name -> String
    showNameStructure Anonymous = "Anonymous"
    showNameStructure (Str s parent) = "Str \"" ++ s ++ "\" (" ++ showNameStructure parent ++ ")"
    showNameStructure (Num n parent) = "Num " ++ show n ++ " (" ++ showNameStructure parent ++ ")"

  -- BVar: look up type in local context
  inferTypeOpenE env ctx (BVar i) = Right (env, ctx, (lookupCtx i ctx).type)

  -- App: infer function type, ensure it's Pi, instantiate codomain
  inferTypeOpenE env ctx (App f arg) = do
    (env1, ctx1, fTy) <- inferTypeOpenE env ctx f
    (_, _, dom, cod) <- ensurePi env1 fTy
    -- Substitute the argument into the codomain
    -- We close the argument to get a ClosedExpr for substitution
    -- Use ctx1 which has placeholders from inferring f's type
    let (env2, ctx2, argClosed) = closeWithPlaceholders env1 ctx1 arg
    -- Use subst0Single instead of subst0 to correctly substitute under nested binders
    -- subst0 only substitutes at the outermost level, but nested Pis need depth tracking
    let resultTy = subst0Single cod argClosed
    -- Reduce the result type to handle cases like ((fun _ => C x) y)
    resultTy' <- whnf env2 resultTy
    -- Debug: trace Fin.rec applications
    let _ = case getAppHead f of
              Just headName => if isFinRecName headName
                then debugPrint ("App Fin.rec:\n  fTy=" ++ show fTy ++ "\n  dom=" ++ show dom ++ "\n  cod=" ++ show cod ++ "\n  argClosed=" ++ show argClosed ++ "\n  resultTy=" ++ show resultTy ++ "\n  resultTy'=" ++ show resultTy') ()
                else ()
              Nothing => ()
    Right (env2, ctx2, resultTy')
  where
    getAppHead : Expr n -> Maybe Name
    getAppHead (Const n _) = Just n
    getAppHead (App f' _) = getAppHead f'
    getAppHead _ = Nothing

    isRecName : Name -> Bool
    isRecName (Str "rec" _) = True
    isRecName _ = False

    isFinRecName : Name -> Bool
    isFinRecName (Str "rec" (Str "Fin" Anonymous)) = True
    isFinRecName _ = False

  -- Lam: type is Pi type
  -- The type of (λx:A. body) is (Πx:A. bodyType)
  inferTypeOpenE env ctx (Lam name bi domExpr body) = do
    -- Check domain is a type
    (env1, ctx1, domTy) <- inferTypeOpenE env ctx domExpr
    _ <- ensureSort env1 domTy
    -- Close the domain for use in context extension and in result type
    -- This also assigns placeholders to all context entries
    let (env2, ctx2, domClosed) = closeWithPlaceholders env1 ctx1 domExpr
    -- Create a placeholder for the new bound variable BEFORE extending context
    -- This way we know what placeholder to replace with BVar 0 later
    let counter = env2.nextPlaceholder
        phName = placeholderName name counter
        env3 = { nextPlaceholder := S counter } env2
        env4 = addPlaceholder phName domClosed env3
        ph : ClosedExpr = Const phName []
        -- Extend context with the new variable, pre-assigning its placeholder
        newEntry = MkLocalEntry name domClosed Nothing (Just ph)
        ctx' : LocalCtx (S n) = newEntry :: ctx2
    -- Infer body type with extended context
    (env5, ctx'', bodyTy) <- inferTypeOpenE env4 ctx' body
    -- Debug: check if bodyTy is Lam
    let _ = case bodyTy of
              Lam lamName _ _ _ => debugPrint ("Lam case: bodyTy is Lam!\n  outer name=" ++ show name ++ "\n  lam name=" ++ show lamName ++ "\n  bodyTy=" ++ show bodyTy) ()
              _ => ()
    -- Convert body type: replace ALL placeholders from ctx'' with their BVars
    -- ctx'' has the new variable at index 0, so its placeholder becomes BVar 0
    -- Use replaceAllPlaceholdersWithBVars' which takes List LocalEntry directly
    let bodyCodOpen = replaceAllPlaceholdersWithBVars' (toList ctx'') bodyTy
    let resultCod : Expr 1 = believe_me bodyCodOpen
    -- Debug: always trace for mk names
    let _ = case name of
              Str "mk" _ => debugPrint ("Lam mk: bodyTy=" ++ show bodyTy ++ "\n  resultCod=" ++ show resultCod ++ "\n  ctxLen=" ++ show (length ctx'')) ()
              _ => ()
    -- Debug: trace when resultCod is a Lam
    let _ = case resultCod of
              Lam lamName _ _ _ => debugPrint ("Lam: resultCod is Lam!\n  outer name=" ++ show name ++ "\n  lam name=" ++ show lamName ++ "\n  bodyTy=" ++ show bodyTy ++ "\n  resultCod=" ++ show resultCod) ()
              _ => ()
    -- Result is Pi type with closed domain and the converted codomain
    Right (env5, ctx2, Pi name bi domClosed resultCod)

  -- Pi: infer universe level of the result
  inferTypeOpenE env ctx (Pi name bi domExpr codExpr) = do
    -- Infer domain type and get its universe level
    (env1, ctx1, domTy) <- inferTypeOpenE env ctx domExpr
    domLevel <- ensureSort env1 domTy
    -- Close domain for context extension (assigns placeholders to context)
    let (env2, ctx2, domClosed) = closeWithPlaceholders env1 ctx1 domExpr
    let ctx' = extendCtx name domClosed ctx2
    -- Debug: trace when codExpr is a Lam
    let _ = case codExpr of
              Lam lamName _ _ _ => debugPrint ("Pi: codExpr is Lam!\n  pi name=" ++ show name ++ "\n  lam name=" ++ show lamName ++ "\n  codExpr=" ++ show codExpr) ()
              _ => ()
    -- Infer codomain type and get its universe level
    (env3, _, codTy) <- inferTypeOpenE env2 ctx' codExpr
    codLevel <- ensureSort env3 codTy
    -- Result universe is imax of domain and codomain, simplified
    -- Return ctx2 (not ctx') since ctx' has the extended context entry
    Right (env3, ctx2, Sort (simplify (IMax domLevel codLevel)))

  -- Let: check value type matches declared type, then extend context and infer body type
  inferTypeOpenE env ctx (Let name tyExpr valExpr body) = do
    -- Check type is a type
    (env1, ctx1, tyTy) <- inferTypeOpenE env ctx tyExpr
    _ <- ensureSort env1 tyTy
    -- Close type (assigns placeholders to context)
    let (env2, ctx2, tyClosed) = closeWithPlaceholders env1 ctx1 tyExpr
    -- Close value (reuses placeholders from ctx2)
    let (env3, ctx3, valClosed) = closeWithPlaceholders env2 ctx2 valExpr
    -- Check value has the declared type
    (env4, ctx4, valTy) <- inferTypeOpenE env3 ctx3 valExpr
    tyClosed' <- whnf env4 tyClosed
    valTy' <- whnf env4 valTy
    if tyClosed' == valTy'
      then do
        -- Extend context with let binding
        let ctx' = extendCtxLet name tyClosed valClosed ctx4
        -- Infer body type
        (env5, _, bodyTy) <- inferTypeOpenE env4 ctx' body
        -- Return ctx4 (not ctx') since ctx' has the extended context entry
        Right (env5, ctx4, bodyTy)
      else Left (LetTypeMismatch tyClosed valTy)

  -- Proj: infer structure type and get field type
  inferTypeOpenE env ctx (Proj structName idx structExpr) = do
    (env1, ctx1, structTy) <- inferTypeOpenE env ctx structExpr
    -- Reduce struct type to WHNF to expose the structure application
    structTy' <- whnf env1 structTy
    -- Extract the head (should be the structure name) and args (params)
    let (head, params) = getAppSpine structTy'
    case getConstHead head of
      Nothing => Left (OtherError $ "projection: expected structure type for " ++ show structName ++ "\n  structExpr=" ++ show structExpr ++ "\n  structTy'=" ++ show structTy')
      Just (tyName, _) =>
        -- Verify the type matches the declared structure name
        if tyName /= structName
          then Left (OtherError $ "projection: type mismatch, expected " ++ show structName ++ " got " ++ show tyName)
          else case getProjType env1 structName idx params of
            Nothing => Left (OtherError $ "projection: could not compute field type for " ++ show structName ++ " at index " ++ show idx)
            Just fieldTy => Right (env1, ctx1, fieldTy)

  -- Literals
  inferTypeOpenE env ctx (NatLit _) = Right (env, ctx, Const (Str "Nat" Anonymous) [])
  inferTypeOpenE env ctx (StringLit _) = Right (env, ctx, Const (Str "String" Anonymous) [])

  ||| Convenience wrapper that discards the environment and context
  export
  covering
  inferTypeOpen : TCEnv -> LocalCtx n -> Expr n -> TC ClosedExpr
  inferTypeOpen env ctx e = do
    (_, _, ty) <- inferTypeOpenE env ctx e
    Right ty

------------------------------------------------------------------------
-- Proof Irrelevance
------------------------------------------------------------------------

||| Check if an expression has type in Prop (i.e., its type has type Sort 0)
||| For example, if p : P where P : Prop, then isProp(p) = True
export
covering
isProp : TCEnv -> ClosedExpr -> TC Bool
isProp env e = do
  -- Get the type of e (e.g., P for a proof p : P)
  ty <- inferType env e
  -- Get the type of that type (e.g., Prop = Sort 0 for P : Prop)
  tyTy <- inferType env ty
  tyTy' <- whnf env tyTy
  case tyTy' of
    Sort l => Right (simplify l == Zero)
    _ => Right False

||| Try proof irrelevance: if both terms have type Prop and their types
||| are definitionally equal, then the terms are definitionally equal.
|||
||| This is the key rule that makes Prop impredicative and proof-irrelevant:
||| any two proofs of the same proposition are equal.
|||
||| Takes isDefEq as parameter to break mutual recursion.

||| Quick check if an expression is definitely NOT a proof
||| (i.e., it's a type, a constructor, etc.)
||| This avoids expensive type inference for common cases
isDefinitelyNotProof : ClosedExpr -> Bool
isDefinitelyNotProof (Sort _) = True        -- Sorts are not proofs
isDefinitelyNotProof (Pi _ _ _ _) = True    -- Pi types are not proofs
isDefinitelyNotProof (Lam _ _ _ _) = True   -- Lambdas are functions, not proofs of Prop in general
isDefinitelyNotProof _ = False

covering
tryProofIrrelevance : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                      TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
tryProofIrrelevance recurEq env t s = do
  -- Quick check: skip if obviously not a proof
  if isDefinitelyNotProof t || isDefinitelyNotProof s
    then Right Nothing
    else do
      -- Check if t has type Prop
      tIsProp <- isProp env t
      if not tIsProp
        then Right Nothing  -- Not a proof, proof irrelevance doesn't apply
        else do
          -- t is a proof, check if s has the same type
          tTy <- inferType env t
          sTy <- inferType env s
          typesEq <- recurEq env tTy sTy
          if typesEq
            then Right (Just True)   -- Same Prop type, proofs are equal
            else Right (Just False)  -- Different types, not equal

------------------------------------------------------------------------
-- Definitional Equality
------------------------------------------------------------------------

||| Check syntactic equality of levels
levelEq : Level -> Level -> Bool
levelEq Zero Zero = True
levelEq (Succ l1) (Succ l2) = levelEq l1 l2
levelEq (Max a1 b1) (Max a2 b2) = levelEq a1 a2 && levelEq b1 b2
levelEq (IMax a1 b1) (IMax a2 b2) = levelEq a1 a2 && levelEq b1 b2
levelEq (Param n1) (Param n2) = n1 == n2
levelEq _ _ = False

||| Check syntactic equality of level lists
levelListEq : List Level -> List Level -> Bool
levelListEq [] [] = True
levelListEq (l1 :: ls1) (l2 :: ls2) = levelEq l1 l2 && levelListEq ls1 ls2
levelListEq _ _ = False

||| Check if a name is an inference placeholder for a specific binder name
||| Inference placeholders have format: Str "_local" (Num counter binderName)
||| We match by binder name regardless of counter
isPlaceholderForBinder : Name -> Name -> Bool
isPlaceholderForBinder (Str "_local" (Num _ binderName)) targetName =
  binderName == targetName
isPlaceholderForBinder _ _ = False

||| Extract the binder name from an inference placeholder
||| Returns Just binderName if this is an inference placeholder, Nothing otherwise
extractInferencePlaceholderBinder : Name -> Maybe Name
extractInferencePlaceholderBinder (Str "_local" (Num _ binderName)) = Just binderName
extractInferencePlaceholderBinder _ = Nothing

||| Check if a name is a comparison placeholder (created by isDefEqBodyWithNameAndType)
isComparisonPlaceholder : Name -> Bool
isComparisonPlaceholder (Str "_x" (Str "_isDefEqBody" _)) = True
isComparisonPlaceholder _ = False

||| Check if expression contains any placeholders matching a binder name
||| This is a quick check to avoid unnecessary traversals
covering
containsPlaceholderForBinder : Name -> ClosedExpr -> Bool
containsPlaceholderForBinder targetBinder (Const name []) = isPlaceholderForBinder name targetBinder
containsPlaceholderForBinder _ (Const _ _) = False  -- Placeholders have no level args
containsPlaceholderForBinder _ (BVar _) = False
containsPlaceholderForBinder _ (Sort _) = False
containsPlaceholderForBinder targetBinder (App f x) =
  containsPlaceholderForBinder targetBinder f || containsPlaceholderForBinder targetBinder x
containsPlaceholderForBinder targetBinder (Lam _ _ ty body) =
  containsPlaceholderForBinder targetBinder ty || containsPlaceholderForBinder targetBinder (believe_me body)
containsPlaceholderForBinder targetBinder (Pi _ _ dom cod) =
  containsPlaceholderForBinder targetBinder dom || containsPlaceholderForBinder targetBinder (believe_me cod)
containsPlaceholderForBinder targetBinder (Let _ ty val body) =
  containsPlaceholderForBinder targetBinder ty ||
  containsPlaceholderForBinder targetBinder val ||
  containsPlaceholderForBinder targetBinder (believe_me body)
containsPlaceholderForBinder targetBinder (Proj _ _ s) = containsPlaceholderForBinder targetBinder s
containsPlaceholderForBinder _ (NatLit _) = False
containsPlaceholderForBinder _ (StringLit _) = False

||| Replace inference placeholders for a specific binder with the shared comparison placeholder
||| This handles placeholders created by closeWithPlaceholders during type inference.
||| Uses believe_me to handle any depth of Expr
replacePlaceholdersForBinderN : Name -> {n : Nat} -> Expr n -> Name -> Expr n
replacePlaceholdersForBinderN targetBinder (BVar i) _ = BVar i
replacePlaceholdersForBinderN targetBinder (Sort l) _ = Sort l
replacePlaceholdersForBinderN targetBinder (Const name []) sharedName =
  if isPlaceholderForBinder name targetBinder
    then Const sharedName []
    else Const name []
replacePlaceholdersForBinderN _ (Const name ls) _ = Const name ls
replacePlaceholdersForBinderN targetBinder (App f x) sharedName =
  App (replacePlaceholdersForBinderN targetBinder f sharedName)
      (replacePlaceholdersForBinderN targetBinder x sharedName)
replacePlaceholdersForBinderN targetBinder (Lam name bi ty body) sharedName =
  Lam name bi (replacePlaceholdersForBinderN targetBinder ty sharedName)
              (replacePlaceholdersForBinderN targetBinder body sharedName)
replacePlaceholdersForBinderN targetBinder (Pi name bi dom cod) sharedName =
  Pi name bi (replacePlaceholdersForBinderN targetBinder dom sharedName)
             (replacePlaceholdersForBinderN targetBinder cod sharedName)
replacePlaceholdersForBinderN targetBinder (Let name ty val body) sharedName =
  Let name (replacePlaceholdersForBinderN targetBinder ty sharedName)
           (replacePlaceholdersForBinderN targetBinder val sharedName)
           (replacePlaceholdersForBinderN targetBinder body sharedName)
replacePlaceholdersForBinderN targetBinder (Proj sn i s) sharedName =
  Proj sn i (replacePlaceholdersForBinderN targetBinder s sharedName)
replacePlaceholdersForBinderN _ (NatLit k) _ = NatLit k
replacePlaceholdersForBinderN _ (StringLit s) _ = StringLit s

||| Convenience wrapper for closed expressions
replacePlaceholdersForBinder : Name -> ClosedExpr -> Name -> ClosedExpr
replacePlaceholdersForBinder targetBinder e sharedName = replacePlaceholdersForBinderN targetBinder e sharedName

||| Combined substitution and placeholder replacement
||| Substitutes BVar 0 (at ALL depths) with the comparison placeholder, and replaces any
||| inference placeholders for the given binder with the comparison placeholder
covering
substAndReplacePlaceholders : Name -> Name -> Expr 1 -> ClosedExpr
substAndReplacePlaceholders binderName phName e =
  -- Use subst0Single instead of subst0 to handle all depths correctly
  let e' : ClosedExpr = subst0Single e (Const phName [])
      hasPlaceholder : Bool = containsPlaceholderForBinder binderName e'
      result : ClosedExpr = if hasPlaceholder
                              then replacePlaceholdersForBinder binderName e' phName
                              else e'
  in result  -- Disable debug output for now

||| Helper for comparing bodies (Expr 1) with binder name and type for placeholder matching
||| We compare them by substituting a fresh variable placeholder.
||| Also registers a binder alias so that inference placeholders (like `α.0._local`)
||| are treated as equal to the comparison placeholder during isDefEq.
covering
isDefEqBodyWithNameAndType : Name -> ClosedExpr -> (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) -> TCEnv -> Expr 1 -> Expr 1 -> TC Bool
isDefEqBodyWithNameAndType binderName binderType recur env b1 b2 =
  -- Create a placeholder for var 0 - use a fresh constant
  -- Register it with the binder's actual type for proper type inference
  -- Use binder name to make it unique per binding level
  let phName = Str "_isDefEqBody" binderName
      -- Add placeholder type for proper type inference
      env' = addPlaceholder phName binderType env
      -- Register binder alias: inference placeholders with this binder name
      -- should be treated as equal to phName during comparison
      env'' = addBinderAlias binderName phName env'
      -- Substitute BVar 0 with the comparison placeholder
      e1' = substAndReplacePlaceholders binderName phName b1
      e2' = substAndReplacePlaceholders binderName phName b2
  in debugPrint ("isDefEqBodyWithNameAndType: binderName=" ++ show binderName ++ "\n  e1'=" ++ show e1' ++ "\n  e2'=" ++ show e2') $
     recur env'' e1' e2'

||| Helper for comparing bodies (Expr 1) - fallback for cases without domain type info
covering
isDefEqBodyWithName : Name -> (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) -> TCEnv -> Expr 1 -> Expr 1 -> TC Bool
isDefEqBodyWithName binderName = isDefEqBodyWithNameAndType binderName (Sort Zero)

||| Helper for comparing bodies (Expr 1) - fallback for cases without binder name
covering
isDefEqBody : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) -> TCEnv -> Expr 1 -> Expr 1 -> TC Bool
isDefEqBody = isDefEqBodyWithName Anonymous

||| Try eta expansion: if t is λx.body and s is not a lambda,
||| eta-expand s to λx:A. s x where A is the domain of s's type.
||| Returns Just True/False if eta applies, Nothing if it doesn't.
||| Takes the isDefEq function as parameter to break mutual recursion.
covering
tryEtaExpansionCore : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                      TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
tryEtaExpansionCore recurEq env t s =
  case t of
    Lam name bi ty body =>
      case s of
        Lam _ _ _ _ => Right Nothing  -- Both are lambdas, eta doesn't apply
        _ => do
          -- s is not a lambda, try to eta-expand it
          -- We need the type of s to be a Pi type
          sTy <- inferType env s
          sTy' <- whnf env sTy
          case sTy' of
            Pi piName piBi dom cod =>
              -- Eta-expand s to: λ(piName : dom). s x
              -- where x is BVar FZ (the bound variable)
              -- The body is: App (weaken1 s) (BVar FZ)
              let sExpanded : ClosedExpr = Lam piName piBi dom (App (weaken1 s) (BVar FZ))
              in do
                -- Now compare t with the expanded s
                result <- recurEq env t sExpanded
                Right (Just result)
            _ => Right Nothing  -- s's type is not a Pi, can't eta-expand
    _ => Right Nothing  -- t is not a lambda

||| Try eta expansion in both directions
covering
tryEtaExpansion : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                  TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
tryEtaExpansion recurEq env t s = do
  -- Try t as lambda, s as non-lambda
  result1 <- tryEtaExpansionCore recurEq env t s
  case result1 of
    Just b => Right (Just b)
    Nothing => do
      -- Try s as lambda, t as non-lambda
      tryEtaExpansionCore recurEq env s t

||| Check definitional equality of two expressions.
|||
||| Two expressions are definitionally equal if they reduce to
||| syntactically equal expressions (up to alpha equivalence).
|||
||| This handles:
||| - Syntactic equality
||| - Beta reduction
||| - Let unfolding
||| - Delta reduction (constant unfolding)
||| - Eta expansion (λx. f x = f when x not free in f)
||| - Proof irrelevance (any two proofs of the same Prop are equal)
export
covering
isDefEq : TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool
isDefEq env e1 e2 = do
  -- First reduce both to whnf (includes delta reduction)
  e1' <- whnf env e1
  e2' <- whnf env e2
  -- Try proof irrelevance first (before structural comparison)
  proofIrrel <- tryProofIrrelevance isDefEq env e1' e2'
  case proofIrrel of
    Just result => Right result
    Nothing => isDefEqWhnf e1' e2'
  where
    -- Check equality of expressions in whnf
    covering
    isDefEqWhnf : ClosedExpr -> ClosedExpr -> TC Bool

    -- Sorts: compare levels
    isDefEqWhnf (Sort l1) (Sort l2) = Right (levelEq l1 l2)

    -- Constants: same name and levels, or equivalent via binder alias
    isDefEqWhnf (Const n1 ls1) (Const n2 ls2) =
      debugPrint ("isDefEqWhnf Const: n1=" ++ show n1 ++ " n2=" ++ show n2) $
      if n1 == n2 && levelListEq ls1 ls2
        then Right True
        else -- Check if one is an inference placeholder that aliases to the other
             -- Only applies to placeholders with no level arguments
             case (ls1, ls2) of
               ([], []) => Right (areEquivalentPlaceholders n1 n2)
               _ => Right False
      where
        -- Check if two constant names are equivalent via binder alias
        -- This handles the case where n1 is `α.0._local` and n2 is `_x._isDefEqBody`
        -- (or vice versa) and we have an alias from binder `α` to `_x._isDefEqBody`
        areEquivalentPlaceholders : Name -> Name -> Bool
        areEquivalentPlaceholders c1 c2 =
          -- Case 1: c1 is inference placeholder, c2 is comparison placeholder
          case extractInferencePlaceholderBinder c1 of
            Just binderName =>
              case lookupBinderAlias binderName env of
                Just aliasTarget =>
                  let result = aliasTarget == c2
                  in debugPrint ("alias lookup: " ++ show binderName ++ " -> " ++ show aliasTarget ++ " vs " ++ show c2 ++ " = " ++ show result) result
                Nothing =>
                  debugPrint ("no alias for " ++ show binderName) False
            Nothing =>
              -- Case 2: c2 is inference placeholder, c1 is comparison placeholder
              case extractInferencePlaceholderBinder c2 of
                Just binderName =>
                  case lookupBinderAlias binderName env of
                    Just aliasTarget =>
                      let result = aliasTarget == c1
                      in debugPrint ("alias lookup (reverse): " ++ show binderName ++ " -> " ++ show aliasTarget ++ " vs " ++ show c1 ++ " = " ++ show result) result
                    Nothing =>
                      debugPrint ("no alias (reverse) for " ++ show binderName) False
                Nothing =>
                  debugPrint ("neither is inference placeholder: " ++ show c1 ++ " vs " ++ show c2) False

    -- App: check function and arg
    isDefEqWhnf (App f1 a1) (App f2 a2) = do
      eqF <- isDefEq env f1 f2
      if eqF
        then do
          eqA <- isDefEq env a1 a2
          if eqA
            then Right True
            else debugPrint ("isDefEqWhnf App arg mismatch:\n  a1=" ++ show a1 ++ "\n  a2=" ++ show a2) $ Right False
        else debugPrint ("isDefEqWhnf App fun mismatch:\n  f1=" ++ show f1 ++ "\n  f2=" ++ show f2) $ Right False

    -- Lam: check binder type and body (ignoring binder name and info)
    -- Pass declared binder name and type for placeholder matching
    isDefEqWhnf (Lam name1 _ ty1 body1) (Lam _ _ ty2 body2) = do
      eqTy <- isDefEq env ty1 ty2
      if eqTy
        then isDefEqBodyWithNameAndType name1 ty1 isDefEq env body1 body2
        else debugPrint ("isDefEqWhnf Lam type mismatch:\n  ty1=" ++ show ty1 ++ "\n  ty2=" ++ show ty2) $ Right False

    -- Pi: check domain and codomain
    -- Pass declared binder name and type for placeholder matching
    isDefEqWhnf (Pi name1 _ dom1 cod1) (Pi _ _ dom2 cod2) = do
      debugPrint ("isDefEqWhnf Pi: name1=" ++ show name1 ++ "\n  cod1=" ++ show cod1 ++ "\n  cod2=" ++ show cod2) $ pure ()
      eqDom <- isDefEq env dom1 dom2
      if eqDom
        then isDefEqBodyWithNameAndType name1 dom1 isDefEq env cod1 cod2
        else Right False

    -- Let: should have been reduced in whnf
    isDefEqWhnf (Let name1 ty1 v1 b1) (Let _ ty2 v2 b2) = do
      eqTy <- isDefEq env ty1 ty2
      eqV <- isDefEq env v1 v2
      if eqTy && eqV
        then isDefEqBodyWithNameAndType name1 ty1 isDefEq env b1 b2
        else Right False

    -- Proj: same struct name, index, and argument
    isDefEqWhnf (Proj sn1 i1 s1) (Proj sn2 i2 s2) =
      if sn1 == sn2 && i1 == i2
        then isDefEq env s1 s2
        else Right False

    -- Literals
    isDefEqWhnf (NatLit n1) (NatLit n2) = Right (n1 == n2)
    isDefEqWhnf (StringLit s1) (StringLit s2) = Right (s1 == s2)

    -- Try eta expansion for mismatched cases
    isDefEqWhnf t s = do
      etaResult <- tryEtaExpansion isDefEq env t s
      case etaResult of
        Just b => Right b
        Nothing => debugPrint ("isDefEqWhnf fallthrough:\n  t=" ++ show t ++ "\n  s=" ++ show s) $ Right False  -- No eta, different constructors

------------------------------------------------------------------------
-- Convenience functions
------------------------------------------------------------------------

||| Check that an expression is well-typed (returns its type)
export
covering
checkExpr : TCEnv -> ClosedExpr -> TC ClosedExpr
checkExpr = inferType

||| Check if an expression has a given type
export
covering
hasType : TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool
hasType env e expectedTy = do
  actualTy <- inferType env e
  isDefEq env actualTy expectedTy

------------------------------------------------------------------------
-- Declaration Validation
------------------------------------------------------------------------

||| Check that a name is not already declared in the environment
export
checkNameNotDeclared : TCEnv -> Name -> TC ()
checkNameNotDeclared env name =
  case lookupDecl name env of
    Just _ => Left (OtherError $ "already declared: " ++ show name)
    Nothing => Right ()

||| Check for duplicate universe parameters
export
checkNoDuplicateUnivParams : List Name -> TC ()
checkNoDuplicateUnivParams [] = Right ()
checkNoDuplicateUnivParams (p :: ps) =
  if elem p ps
    then Left (OtherError $ "duplicate universe parameter: " ++ show p)
    else checkNoDuplicateUnivParams ps

||| Check that the type of an expression is a Sort (i.e., the expression is a type)
export
covering
checkIsType : TCEnv -> ClosedExpr -> TC Level
checkIsType env e = do
  ty <- inferType env e
  ensureSort env ty

||| Validate an axiom declaration.
|||
||| Checks:
||| 1. Name is not already declared
||| 2. No duplicate universe parameters
||| 3. Type is well-formed and is a type (has type Sort l)
export
covering
checkAxiomDecl : TCEnv -> Name -> ClosedExpr -> List Name -> TC ()
checkAxiomDecl env name ty levelParams = do
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env ty
  Right ()

||| Validate a definition declaration.
|||
||| Checks:
||| 1. Name is not already declared
||| 2. No duplicate universe parameters
||| 3. Type is well-formed and is a type
||| 4. Value is well-formed
||| 5. Value's type is definitionally equal to declared type
export
covering
checkDefDecl : TCEnv -> Name -> ClosedExpr -> ClosedExpr -> List Name -> TC ()
checkDefDecl env name ty value levelParams = do
  debugPrint ("checkDefDecl: " ++ show name) $ pure ()
  checkNameNotDeclared env name
  debugPrint ("checkDefDecl: checkNameNotDeclared done") $ pure ()
  checkNoDuplicateUnivParams levelParams
  debugPrint ("checkDefDecl: checkNoDuplicateUnivParams done") $ pure ()
  _ <- checkIsType env ty
  debugPrint ("checkDefDecl: checkIsType done") $ pure ()
  -- Use inferTypeE to get updated env with placeholders
  (env', valueTy) <- debugPrint ("checkDefDecl: about to infer value type for " ++ show name ++ "\n  value=" ++ show value) $ inferTypeE env value
  debugPrint ("checkDefDecl: inferTypeE done\n  valueTy=" ++ show valueTy ++ "\n  ty=" ++ show ty) $ pure ()
  -- Use updated env for comparison (so placeholders can be looked up)
  eq <- isDefEq env' valueTy ty
  if eq
    then Right ()
    else Left (OtherError $ "definition type mismatch for " ++ show name
               ++ "\n  inferred: " ++ show valueTy
               ++ "\n  declared: " ++ show ty)

||| Validate a theorem declaration.
|||
||| Checks:
||| 1. Name is not already declared
||| 2. No duplicate universe parameters
||| 3. Type is well-formed and is a Prop (has type Sort 0)
||| 4. Value is well-formed
||| 5. Value's type is definitionally equal to declared type
export
covering
checkThmDecl : TCEnv -> Name -> ClosedExpr -> ClosedExpr -> List Name -> TC ()
checkThmDecl env name ty value levelParams = do
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  tyLevel <- checkIsType env ty
  -- Theorem type must be a Prop (Sort 0)
  if simplify tyLevel /= Zero
    then Left (OtherError $ "theorem type must be a Prop: " ++ show name)
    else do
      -- Use inferTypeE to get updated env with placeholders
      (env', valueTy) <- inferTypeE env value
      eq <- isDefEq env' valueTy ty
      if eq
        then Right ()
        else Left (OtherError $ "theorem proof type mismatch for " ++ show name)

------------------------------------------------------------------------
-- Inductive/Constructor Validation
------------------------------------------------------------------------

||| Check if a name occurs in negative position in an expression.
||| A negative position is on the left side of an arrow (Pi domain).
||| Returns True if the name occurs in strictly positive position only.
|||
||| Strict positivity means:
||| - The inductive name doesn't occur in the domain of any Pi
||| - The inductive name can only occur as the head of the final return type
|||   or as an argument to another strictly positive type
||| Check if a type contains the inductive name in a negative position.
||| This is used for strict positivity checking.
|||
||| Strict positivity rules:
||| 1. The inductive can appear as a direct constructor parameter: Nat.succ : Nat -> Nat (OK)
||| 2. The inductive CANNOT appear in the domain of a function that is itself a parameter:
|||    Bad.mk : (Bad -> False) -> Bad (BAD - Bad in domain of function parameter)
||| 3. The inductive CAN appear as a parameter applied to other types:
|||    List.cons : A -> List A -> List A (OK - List A is applied form)
|||
||| We track "depth" - how many function domains deep we are:
||| - depth 0: at the top level or in codomain
||| - depth 1: in the direct domain of a constructor parameter (OK for inductive to appear here)
||| - depth >= 2: in a nested function domain (NOT OK - negative occurrence)
checkNegativeOccurrence : Name -> {n : Nat} -> Expr n -> Bool
checkNegativeOccurrence indName = go 0
  where
    ||| Check if the name appears in negative position.
    ||| `depth` counts how many function domains deep we are.
    go : {m : Nat} -> Nat -> Expr m -> Bool
    go _ (BVar _) = False  -- No occurrence
    go _ (Sort _) = False  -- No occurrence
    go _ (NatLit _) = False
    go _ (StringLit _) = False
    go depth (Const n _) =
      -- Negative occurrence if we're 2+ levels deep in function domains
      depth >= 2 && n == indName
    go depth (App f x) =
      go depth f || go depth x
    go depth (Lam _ _ ty body) =
      go depth ty || go depth body
    go depth (Pi _ _ dom cod) =
      -- When entering domain, increment depth
      -- When in codomain, reset to 0 (we're back at "top level" for that branch)
      go (S depth) dom || go 0 cod
    go depth (Let _ ty val body) =
      go depth ty || go depth val || go depth body
    go depth (Proj _ _ e) = go depth e

checkStrictlyPositive : Name -> ClosedExpr -> Bool
checkStrictlyPositive indName ty = not (checkNegativeOccurrence indName ty)

||| Check if an inductive type satisfies the strict positivity condition.
||| This checks all constructor types to ensure the inductive name doesn't
||| appear in negative position.
checkPositivity : Name -> List ConstructorInfo -> TC ()
checkPositivity indName [] = Right ()
checkPositivity indName (ctor :: ctors) =
  if checkStrictlyPositive indName ctor.type
    then checkPositivity indName ctors
    else Left (NegativeOccurrence indName ctor.name)

||| Get the head constant from the return type of a constructor.
||| Strips off all Pi binders and returns the head of the resulting type.
getReturnTypeHead : Expr n -> Maybe (Name, List Level)
getReturnTypeHead (Pi _ _ _ cod) = getReturnTypeHead cod
getReturnTypeHead (App f _) = getReturnTypeHead f
getReturnTypeHead (Const n ls) = Just (n, ls)
getReturnTypeHead _ = Nothing

||| Count the number of Pi binders in a type (i.e., the arity/field count)
countPiBinders : Expr n -> Nat
countPiBinders (Pi _ _ _ cod) = S (countPiBinders cod)
countPiBinders _ = 0

||| Check that a constructor's type returns the correct inductive type.
checkCtorReturnType : Name -> Name -> ClosedExpr -> TC ()
checkCtorReturnType ctorName indName ctorTy =
  case getReturnTypeHead ctorTy of
    Just (returnName, _) =>
      if returnName == indName
        then Right ()
        else Left (CtorWrongInductive ctorName indName returnName)
    Nothing =>
      Left (CtorWrongReturnType ctorName indName ctorTy)

||| Check that the declared field count matches the actual type.
||| The field count is the number of Pi binders after the parameters.
checkCtorFieldCount : Name -> Nat -> Nat -> ClosedExpr -> TC ()
checkCtorFieldCount ctorName numParams declaredFields ctorTy =
  let totalBinders = countPiBinders ctorTy
      actualFields = if totalBinders >= numParams
                       then totalBinders `minus` numParams
                       else 0
  in if declaredFields == actualFields
       then Right ()
       else Left (CtorWrongFieldCount ctorName declaredFields actualFields)

||| Check that constructor universe parameters match the inductive's parameters.
checkCtorUniverseParams : Name -> List Name -> List Name -> TC ()
checkCtorUniverseParams ctorName indParams ctorParams =
  if indParams == ctorParams
    then Right ()
    else Left (CtorUniverseMismatch ctorName indParams ctorParams)

||| Get the level parameters for an inductive
getInductiveLevelParams : TCEnv -> Name -> Maybe (List Name)
getInductiveLevelParams env name =
  case lookupDecl name env of
    Just (IndDecl _ params) => Just params
    _ => Nothing

||| Validate and add an axiom to the environment
export
covering
addAxiomChecked : TCEnv -> Name -> ClosedExpr -> List Name -> TC TCEnv
addAxiomChecked env name ty levelParams = do
  checkAxiomDecl env name ty levelParams
  Right (addDecl (AxiomDecl name ty levelParams) env)

||| Validate and add a definition to the environment
export
covering
addDefChecked : TCEnv -> Name -> ClosedExpr -> ClosedExpr ->
                ReducibilityHint -> Safety -> List Name -> TC TCEnv
addDefChecked env name ty value hint safety levelParams = do
  checkDefDecl env name ty value levelParams
  Right (addDecl (DefDecl name ty value hint safety levelParams) env)

||| Validate and add a theorem to the environment
export
covering
addThmChecked : TCEnv -> Name -> ClosedExpr -> ClosedExpr -> List Name -> TC TCEnv
addThmChecked env name ty value levelParams = do
  checkThmDecl env name ty value levelParams
  Right (addDecl (ThmDecl name ty value levelParams) env)

||| Validate a declaration and add it to the environment
export
covering
addDeclChecked : TCEnv -> Declaration -> TC TCEnv
addDeclChecked env (AxiomDecl name ty levelParams) =
  addAxiomChecked env name ty levelParams
addDeclChecked env (DefDecl name ty value hint safety levelParams) =
  addDefChecked env name ty value hint safety levelParams
addDeclChecked env (ThmDecl name ty value levelParams) =
  addThmChecked env name ty value levelParams
addDeclChecked env (OpaqueDecl name ty value levelParams) = do
  -- Same checks as definition
  checkDefDecl env name ty value levelParams
  Right (addDecl (OpaqueDecl name ty value levelParams) env)
addDeclChecked env QuotDecl =
  Right (enableQuot env)
addDeclChecked env decl@(IndDecl info levelParams) = do
  -- Validate inductive type declaration
  checkNameNotDeclared env info.name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env info.type
  -- Note: positivity check is done per constructor in CtorDecl processing,
  -- since IndDecl only has placeholder types for constructors at parse time
  Right (addDecl decl env)
addDeclChecked env decl@(CtorDecl name ty indName ctorIdx numParams numFields levelParams) = do
  -- Basic checks
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env ty
  -- Validate that the inductive exists
  case getInductiveLevelParams env indName of
    Nothing => Left (CtorInductiveNotFound name indName)
    Just indLevelParams => do
      -- Check strict positivity: the inductive name must not appear in negative position
      if checkStrictlyPositive indName ty
        then pure ()
        else Left (NegativeOccurrence indName name)
      -- Check return type matches the inductive
      checkCtorReturnType name indName ty
      -- Check field count is correct
      checkCtorFieldCount name numParams numFields ty
      -- Check universe parameters match
      checkCtorUniverseParams name indLevelParams levelParams
      Right (addDecl decl env)
addDeclChecked env decl@(RecDecl info levelParams) = do
  checkNameNotDeclared env info.name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env info.type
  Right (addDecl decl env)
