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
import Data.SortedMap
import Data.Fin
import Data.List
import Data.Vect

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

||| Empty environment
public export
emptyEnv : TCEnv
emptyEnv = MkTCEnv empty False

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
extendCtx name ty ctx = MkLocalEntry name ty Nothing :: ctx

||| Extend context with a let-binding (going under a let)
public export
extendCtxLet : Name -> ClosedExpr -> ClosedExpr -> LocalCtx n -> LocalCtx (S n)
extendCtxLet name ty val ctx = MkLocalEntry name ty (Just val) :: ctx

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
  ||| Other error
  OtherError : String -> TCError

export
Show TCError where
  show (TypeExpected _) = "type expected"
  show (FunctionExpected _) = "function expected"
  show (AppTypeMismatch _ _) = "application type mismatch"
  show (LetTypeMismatch _ _) = "let binding type mismatch"
  show (UnknownConst n) = "unknown constant: " ++ show n
  show (WrongNumLevels exp act n) =
    "wrong number of universe levels for " ++ show n ++
    ": expected " ++ show exp ++ ", got " ++ show act
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
unfoldConst : TCEnv -> Name -> List Level -> Maybe ClosedExpr
unfoldConst env name levels = do
  decl <- lookupDecl name env
  value <- getDeclValue decl
  let params = declLevelParams decl
  -- Check level count matches
  guard (length params == length levels)
  pure (instantiateLevelParams params levels value)

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

||| Try iota reduction on a recursor application
||| If the expression is `Rec.rec params motives minors indices (Ctor args)`,
||| reduce it using the matching recursor rule.
tryIotaReduction : TCEnv -> ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryIotaReduction env e whnfStep = do
  -- Check if head is a recursor
  let (head, args) = getAppSpine e
  (recName, recLevels) <- getConstHead head
  recInfo <- getRecursorInfo env recName

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
  let rhs = instantiateLevelParams (declLevelParams (RecDecl recInfo [])) recLevels rule.rhs

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
whnf env e = whnfFuel 1000 e
  where
    ||| Single step of whnf (beta/let reduction)
    ||| For nested applications like (((λ...) a) b), we reduce the innermost
    ||| beta-redex first.
    whnfStepCore : ClosedExpr -> Maybe ClosedExpr
    whnfStepCore (App (Lam _ _ _ body) arg) = Just (subst0 body arg)
    whnfStepCore (App f arg) =
      -- If f is reducible, reduce it and reconstruct
      case whnfStepCore f of
        Just f' => Just (App f' arg)
        Nothing => Nothing
    whnfStepCore (Let _ _ val body) = Just (subst0 body val)
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
    whnfStepCore (App (Lam _ _ _ body) arg) = Just (subst0 body arg)
    whnfStepCore (Let _ _ val body) = Just (subst0 body val)
    whnfStepCore _ = Nothing

    whnfCoreFuel : Nat -> ClosedExpr -> TC ClosedExpr
    whnfCoreFuel 0 e = Right e
    whnfCoreFuel (S k) e = case whnfStepCore e of
      Nothing => Right e
      Just e' => whnfCoreFuel k e'

||| Check if expression is a Sort
export
covering
ensureSort : TCEnv -> ClosedExpr -> TC Level
ensureSort env e = do
  e' <- whnf env e
  case e' of
    Sort l => Right l
    _      => Left (TypeExpected e)

||| Check if expression is a Pi type
export
covering
ensurePi : TCEnv -> ClosedExpr -> TC (Name, BinderInfo, ClosedExpr, Expr 1)
ensurePi env e = do
  e' <- whnf env e
  case e' of
    Pi name bi dom cod => Right (name, bi, dom, cod)
    _                  => Left (FunctionExpected e)

------------------------------------------------------------------------
-- Type Inference
------------------------------------------------------------------------

||| Close an expression by substituting all bound variables with placeholders.
||| This is used to convert Expr n to ClosedExpr for type checking purposes.
|||
||| We substitute each variable with a unique constant based on its name.
||| This is safe for type inference since we only need the *structure* of the type.
closeWithPlaceholders : LocalCtx n -> Expr n -> ClosedExpr
closeWithPlaceholders [] e = e
closeWithPlaceholders {n = S m} (entry :: ctx) e =
  -- Substitute var 0 with a placeholder, then close the rest
  let e' : Expr m = subst0 e (Const (Str "_local" entry.name) [])
  in closeWithPlaceholders ctx e'

mutual
  ||| Infer the type of a closed expression.
  ||| Delegates to inferTypeOpen with empty context for binder forms.
  export
  covering
  inferType : TCEnv -> ClosedExpr -> TC ClosedExpr

  -- Sort : Sort (succ level)
  inferType _ (Sort l) = Right (Sort (Succ l))

  -- Const: look up type in environment and instantiate levels
  inferType env (Const name levels) =
    case lookupDecl name env of
      Nothing => Left (UnknownConst name)
      Just decl => case declType decl of
        Nothing => Left (UnknownConst name)  -- QuotDecl has no direct type
        Just ty =>
          let params = declLevelParams decl in
          if length params == length levels
            then Right (instantiateLevelParams params levels ty)
            else Left (WrongNumLevels (length params) (length levels) name)

  -- App: infer function type, check it's Pi, verify arg type, instantiate with arg
  inferType env (App f arg) = do
    fTy <- inferType env f
    (_, _, dom, cod) <- ensurePi env fTy
    -- Verify argument type matches domain (basic check - full isDefEq requires mutual recursion)
    argTy <- inferType env arg
    argTy' <- whnf env argTy
    dom' <- whnf env dom
    -- Simple structural equality after reduction
    if argTy' == dom'
      then Right (subst0 cod arg)
      else Left (AppTypeMismatch dom argTy)

  -- Lam: delegate to inferTypeOpen which properly handles the body
  inferType env (Lam name bi ty body) =
    inferTypeOpen env emptyCtx (Lam name bi ty body)

  -- Pi: delegate to inferTypeOpen which properly handles the codomain
  inferType env (Pi name bi dom cod) =
    inferTypeOpen env emptyCtx (Pi name bi dom cod)

  -- Let: delegate to inferTypeOpen which properly handles the body
  inferType env (Let name ty val body) =
    inferTypeOpen env emptyCtx (Let name ty val body)

  -- Proj: for now unsupported (requires inductive types)
  inferType _ (Proj _ _ _) = Left (OtherError "projection not yet supported")

  -- NatLit: type is Nat
  inferType _ (NatLit _) = Right (Const (Str "Nat" Anonymous) [])

  -- StringLit: type is String
  inferType _ (StringLit _) = Right (Const (Str "String" Anonymous) [])

  -- BVar: should not appear in closed expressions (Fin 0 is empty)

  ------------------------------------------------------------------------
  -- Open Term Type Inference
  ------------------------------------------------------------------------

  ||| Infer the type of an open expression with a local context.
  |||
  ||| This is the general form that handles expressions with bound variables.
  ||| The result is always a closed expression (type).
  |||
  ||| Key idea: when we look up a bound variable, we return its type from context.
  ||| When we go under a binder, we extend the context with the domain type.
  export
  covering
  inferTypeOpen : TCEnv -> LocalCtx n -> Expr n -> TC ClosedExpr

  -- Sort: same as closed case
  inferTypeOpen _ _ (Sort l) = Right (Sort (Succ l))

  -- Const: same as closed case
  inferTypeOpen env _ (Const name levels) =
    case lookupDecl name env of
      Nothing => Left (UnknownConst name)
      Just decl => case declType decl of
        Nothing => Left (UnknownConst name)
        Just ty =>
          let params = declLevelParams decl in
          if length params == length levels
            then Right (instantiateLevelParams params levels ty)
            else Left (WrongNumLevels (length params) (length levels) name)

  -- BVar: look up type in local context
  inferTypeOpen _ ctx (BVar i) = Right (lookupCtx i ctx).type

  -- App: infer function type, ensure it's Pi, instantiate codomain
  inferTypeOpen env ctx (App f arg) = do
    fTy <- inferTypeOpen env ctx f
    (_, _, dom, cod) <- ensurePi env fTy
    -- Substitute the argument into the codomain
    -- We close the argument to get a ClosedExpr for substitution
    let argClosed = closeWithPlaceholders ctx arg
    Right (subst0 cod argClosed)

  -- Lam: type is Pi type
  inferTypeOpen env ctx (Lam name bi domExpr body) = do
    -- Check domain is a type
    domTy <- inferTypeOpen env ctx domExpr
    _ <- ensureSort env domTy
    -- Close the domain to use in the context
    let domClosed = closeWithPlaceholders ctx domExpr
    -- Infer body type with extended context
    let ctx' = extendCtx name domClosed ctx
    bodyTy <- inferTypeOpen env ctx' body
    -- Result is Pi type
    Right (Pi name bi domClosed (weaken1 bodyTy))

  -- Pi: infer universe level of the result
  inferTypeOpen env ctx (Pi name bi domExpr codExpr) = do
    -- Infer domain type and get its universe level
    domTy <- inferTypeOpen env ctx domExpr
    domLevel <- ensureSort env domTy
    -- Close domain for context extension
    let domClosed = closeWithPlaceholders ctx domExpr
    let ctx' = extendCtx name domClosed ctx
    -- Infer codomain type and get its universe level
    codTy <- inferTypeOpen env ctx' codExpr
    codLevel <- ensureSort env codTy
    -- Result universe is imax of domain and codomain, simplified
    Right (Sort (simplify (IMax domLevel codLevel)))

  -- Let: extend context and infer body type
  inferTypeOpen env ctx (Let name tyExpr valExpr body) = do
    -- Check type is a type
    tyTy <- inferTypeOpen env ctx tyExpr
    _ <- ensureSort env tyTy
    -- Close type and value
    let tyClosed = closeWithPlaceholders ctx tyExpr
    let valClosed = closeWithPlaceholders ctx valExpr
    -- Extend context with let binding
    let ctx' = extendCtxLet name tyClosed valClosed ctx
    -- Infer body type
    inferTypeOpen env ctx' body

  -- Proj: infer structure type and get field type
  inferTypeOpen env ctx (Proj structName idx structExpr) = do
    structTy <- inferTypeOpen env ctx structExpr
    -- For now, return an error - projection typing requires inductive type lookup
    Left (OtherError $ "projection typing not yet fully supported for " ++ show structName)

  -- Literals
  inferTypeOpen _ _ (NatLit _) = Right (Const (Str "Nat" Anonymous) [])
  inferTypeOpen _ _ (StringLit _) = Right (Const (Str "String" Anonymous) [])

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
covering
tryProofIrrelevance : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                      TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
tryProofIrrelevance recurEq env t s = do
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

||| Helper for comparing bodies (Expr 1)
||| We compare them by substituting a fresh variable placeholder
covering
isDefEqBody : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) -> TCEnv -> Expr 1 -> Expr 1 -> TC Bool
isDefEqBody recur env b1 b2 =
  -- Create a placeholder for var 0 - use a fresh constant
  let placeholder = Const (Str "_x" Anonymous) []
      e1 = subst0 b1 placeholder
      e2 = subst0 b2 placeholder
  in recur env e1 e2

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
    Nothing =>
      -- Then check structural equality
      isDefEqWhnf e1' e2'
  where
    -- Check equality of expressions in whnf
    covering
    isDefEqWhnf : ClosedExpr -> ClosedExpr -> TC Bool

    -- Sorts: compare levels
    isDefEqWhnf (Sort l1) (Sort l2) = Right (levelEq l1 l2)

    -- Constants: same name and levels
    isDefEqWhnf (Const n1 ls1) (Const n2 ls2) =
      Right (n1 == n2 && levelListEq ls1 ls2)

    -- App: check function and arg
    isDefEqWhnf (App f1 a1) (App f2 a2) = do
      eqF <- isDefEq env f1 f2
      if eqF
        then isDefEq env a1 a2
        else Right False

    -- Lam: check binder type and body (ignoring binder name and info)
    isDefEqWhnf (Lam _ _ ty1 body1) (Lam _ _ ty2 body2) = do
      eqTy <- isDefEq env ty1 ty2
      if eqTy
        then isDefEqBody isDefEq env body1 body2
        else Right False

    -- Pi: check domain and codomain
    isDefEqWhnf (Pi _ _ dom1 cod1) (Pi _ _ dom2 cod2) = do
      eqDom <- isDefEq env dom1 dom2
      if eqDom
        then isDefEqBody isDefEq env cod1 cod2
        else Right False

    -- Let: should have been reduced in whnf
    isDefEqWhnf (Let _ ty1 v1 b1) (Let _ ty2 v2 b2) = do
      eqTy <- isDefEq env ty1 ty2
      eqV <- isDefEq env v1 v2
      if eqTy && eqV
        then isDefEqBody isDefEq env b1 b2
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
        Nothing => Right False  -- No eta, different constructors

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
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env ty
  valueTy <- inferType env value
  eq <- isDefEq env valueTy ty
  if eq
    then Right ()
    else Left (OtherError $ "definition type mismatch for " ++ show name)

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
      valueTy <- inferType env value
      eq <- isDefEq env valueTy ty
      if eq
        then Right ()
        else Left (OtherError $ "theorem proof type mismatch for " ++ show name)

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
  -- Basic checks for inductive - full validation would be much more complex
  checkNameNotDeclared env info.name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env info.type
  Right (addDecl decl env)
addDeclChecked env decl@(CtorDecl name ty _ _ _ _ levelParams) = do
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env ty
  Right (addDecl decl env)
addDeclChecked env decl@(RecDecl info levelParams) = do
  checkNameNotDeclared env info.name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env info.type
  Right (addDecl decl env)
