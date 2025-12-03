||| Type checker for Lean 4 kernel
|||
||| Core operations:
||| - inferType: compute the type of an expression
||| - whnf: reduce to weak head normal form (beta, let, delta)
||| - isDefEq: check definitional equality
|||
||| For now, we only handle closed expressions (no local context).
module Lean4Idris.TypeChecker

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Subst
import Data.SortedMap
import Data.Fin
import Data.List

%default total

------------------------------------------------------------------------
-- Environment
------------------------------------------------------------------------

||| A type checking environment holds all known declarations
public export
record TCEnv where
  constructor MkTCEnv
  decls : SortedMap Name Declaration

||| Empty environment
public export
emptyEnv : TCEnv
emptyEnv = MkTCEnv empty

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
-- WHNF (Weak Head Normal Form)
------------------------------------------------------------------------

||| Reduce expression to weak head normal form.
|||
||| This performs:
||| - Beta reduction: (λx.body) arg → body[0 := arg]
||| - Let substitution: let x = v in body → body[0 := v]
||| - Delta reduction: unfold constant definitions
|||
||| We use a fuel parameter to ensure termination.
export
covering
whnf : TCEnv -> ClosedExpr -> TC ClosedExpr
whnf env e = whnfFuel 1000 e
  where
    ||| Single step of whnf (beta/let reduction)
    whnfStepCore : ClosedExpr -> Maybe ClosedExpr
    whnfStepCore (App (Lam _ _ _ body) arg) = Just (subst0 body arg)
    whnfStepCore (Let _ _ val body) = Just (subst0 body val)
    whnfStepCore _ = Nothing

    whnfFuel : Nat -> ClosedExpr -> TC ClosedExpr
    whnfFuel 0 e = Right e  -- out of fuel, return as-is
    whnfFuel (S k) e =
      -- First try beta/let reduction
      case whnfStepCore e of
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

||| Infer the type of an expression.
|||
||| For now, this only handles closed expressions.
||| Environment lookup for constants is minimal (we don't fully check yet).
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

-- App: infer function type, check it's Pi, instantiate with arg
inferType env (App f arg) = do
  fTy <- inferType env f
  (_, _, dom, cod) <- ensurePi env fTy
  -- In a full checker we'd verify: argTy <- inferType env arg; isDefEq dom argTy
  Right (subst0 cod arg)

-- Lam: type is Pi
-- We need the type annotation on the lambda to be able to infer its type
inferType env (Lam name bi ty body) = do
  -- Check that ty is a type
  _ <- inferType env ty >>= ensureSort env
  -- For the body, we need to add a local variable - but we're working with closed exprs
  -- In Milestone 2 we handle only closed terms so we return an error for now if body needs context
  -- Actually, for lambdas we can still type them: the body has access to var 0
  -- We'd need a local context for proper typing, but for demos let's approximate
  Right (Pi name bi ty body)  -- Not fully correct but works for simple cases

-- Pi: infer universe
inferType env (Pi name bi dom cod) = do
  domLevel <- inferType env dom >>= ensureSort env
  -- For cod, we need to infer with extended context
  -- For now, simplify: if cod doesn't use var 0, we can type it directly
  -- Full implementation requires local context
  Right (Sort (mkLevelMax domLevel Zero))  -- Approximation
  where
    mkLevelMax : Level -> Level -> Level
    mkLevelMax Zero l2 = l2
    mkLevelMax l1 Zero = l1
    mkLevelMax l1 l2 = Max l1 l2

-- Let: infer body type with substituted value
inferType env (Let name ty val body) = do
  _ <- inferType env ty >>= ensureSort env
  -- In full checker: valTy <- inferType env val; check isDefEq valTy ty
  Right (subst0 body val) >>= inferType env

-- Proj: for now unsupported (requires inductive types)
inferType _ (Proj _ _ _) = Left (OtherError "projection not yet supported")

-- NatLit: type is Nat
inferType _ (NatLit _) = Right (Const (Str "Nat" Anonymous) [])

-- StringLit: type is String
inferType _ (StringLit _) = Right (Const (Str "String" Anonymous) [])

-- BVar: should not appear in closed expressions
-- This case is actually impossible due to Expr 0 indexing, but we need it for coverage
-- Actually Expr 0 cannot have BVar (since Fin 0 is empty), so this is dead code

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
|||
||| Full implementation would add:
||| - Proof irrelevance
||| - Nat/String literal reduction
export
covering
isDefEq : TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool
isDefEq env e1 e2 = do
  -- First reduce both to whnf (includes delta reduction)
  e1' <- whnf env e1
  e2' <- whnf env e2
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
