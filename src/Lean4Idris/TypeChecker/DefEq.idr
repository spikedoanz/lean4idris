module Lean4Idris.TypeChecker.DefEq

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Subst
import Lean4Idris.TypeChecker.Monad
import Lean4Idris.TypeChecker.Reduction
import Lean4Idris.TypeChecker.Infer
import Data.Fin
import Data.List
import Debug.Trace

%default total

------------------------------------------------------------------------
-- NatLit/Nat constructor equality
------------------------------------------------------------------------

-- Nat constructor names
natZeroName : Name
natZeroName = Str "zero" (Str "Nat" Anonymous)

natSuccName : Name
natSuccName = Str "succ" (Str "Nat" Anonymous)

-- Convert a NatLit to Nat.zero/Nat.succ form
-- NatLit 0 -> Const Nat.zero []
-- NatLit (S n) -> App (Const Nat.succ []) (NatLit n)
natLitToNatExpr : Nat -> ClosedExpr
natLitToNatExpr Z = Const natZeroName []
natLitToNatExpr (S n) = App (Const natSuccName []) (NatLit n)

-- Try to extract a Nat from Nat.zero/Nat.succ constructors
-- Returns Just n if the expression is a valid Nat representation
-- This works recursively to handle nested succ applications
covering
getNatFromExpr : ClosedExpr -> Maybe Nat
getNatFromExpr (NatLit n) = Just n
getNatFromExpr (Const n []) = if n == natZeroName then Just 0 else Nothing
getNatFromExpr (App f arg) = case f of
  Const n [] => if n == natSuccName
                  then map S (getNatFromExpr arg)
                  else Nothing
  _ => Nothing
getNatFromExpr _ = Nothing

-- Check if a NatLit equals a constructor-based Nat representation
covering
natLitEqNatExpr : Nat -> ClosedExpr -> Bool
natLitEqNatExpr n e = case getNatFromExpr e of
  Just m => n == m
  Nothing => False

------------------------------------------------------------------------
-- Proof Irrelevance
------------------------------------------------------------------------

export covering
isProp : TCEnv -> ClosedExpr -> TC Bool
isProp env e = do
  ty <- inferType env e
  tyTy <- inferType env ty
  tyTy' <- whnf env tyTy
  case tyTy' of
    Sort l => pure (simplify l == Zero)
    _ => pure False

isDefinitelyNotProof : ClosedExpr -> Bool
isDefinitelyNotProof (Sort _) = True
isDefinitelyNotProof (Pi _ _ _ _) = True
isDefinitelyNotProof (Lam _ _ _ _) = True
isDefinitelyNotProof _ = False

covering
tryProofIrrelevance : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                      TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
tryProofIrrelevance recurEq env t s = do
  if isDefinitelyNotProof t || isDefinitelyNotProof s
    then pure Nothing
    else do
      tIsProp <- isProp env t
      if not tIsProp
        then pure Nothing
        else do
          tTy <- inferType env t
          sTy <- inferType env s
          typesEq <- recurEq env tTy sTy
          if typesEq then pure (Just True) else pure (Just False)

------------------------------------------------------------------------
-- Level Equality (using canonical form normalization)
------------------------------------------------------------------------

-- Use the canonical form normalization from Level.idr
-- This handles universe parameter equivalence correctly
covering
levelEq : Level -> Level -> Bool
levelEq = isLevelEquiv

covering
levelListEq : List Level -> List Level -> Bool
levelListEq = isLevelEquivList

------------------------------------------------------------------------
-- Body Comparison Helpers
------------------------------------------------------------------------

covering
isDefEqBodyWithDepth : Nat -> ClosedExpr -> (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                       TCEnv -> Expr 1 -> Expr 1 -> TC Bool
isDefEqBodyWithDepth depth binderType recur env b1 b2 =
  let localId = env.nextLocalId
      localVar : ClosedExpr = Local localId Anonymous
      env' = addLocalType localId binderType ({ nextLocalId := S localId } env)
      e1' : ClosedExpr = instantiate1 (believe_me b1) localVar
      e2' : ClosedExpr = instantiate1 (believe_me b2) localVar
  in recur env' e1' e2'

covering
isDefEqBodyWithNameAndType : Name -> ClosedExpr -> (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                              TCEnv -> Expr 1 -> Expr 1 -> TC Bool
isDefEqBodyWithNameAndType binderName binderType recur env b1 b2 =
  isDefEqBodyWithDepth 0 binderType recur env b1 b2

covering
isDefEqBodyWithName : Name -> (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                       TCEnv -> Expr 1 -> Expr 1 -> TC Bool
isDefEqBodyWithName binderName recur env b1 b2 =
  isDefEqBodyWithDepth 0 (Sort Zero) recur env b1 b2

covering
isDefEqBody : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
              TCEnv -> Expr 1 -> Expr 1 -> TC Bool
isDefEqBody recur env b1 b2 =
  isDefEqBodyWithDepth 0 (Sort Zero) recur env b1 b2

------------------------------------------------------------------------
-- Eta Expansion
------------------------------------------------------------------------

covering
tryEtaExpansionCore : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                      TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
tryEtaExpansionCore recurEq env t s = case t of
  Lam name bi ty body => case s of
    Lam _ _ _ _ => pure Nothing
    _ => do
      sTy <- inferType env s
      sTy' <- whnf env sTy
      case sTy' of
        Pi piName piBi dom cod =>
          let sExpanded : ClosedExpr = Lam piName piBi dom (App (weaken1 s) (BVar FZ))
          in do result <- recurEq env t sExpanded
                pure (Just result)
        _ => pure Nothing
  _ => pure Nothing

covering
tryEtaExpansion : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                  TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
tryEtaExpansion recurEq env t s = do
  result1 <- tryEtaExpansionCore recurEq env t s
  case result1 of
    Just b => pure (Just b)
    Nothing => tryEtaExpansionCore recurEq env s t

------------------------------------------------------------------------
-- Structure Eta Expansion
------------------------------------------------------------------------

-- Check if a type is a structure (single-constructor inductive)
-- Returns: (structName, ctorName, levels, numParams, numFields)
getStructureInfo : TCEnv -> ClosedExpr -> Maybe (Name, Name, List Level, Nat, Nat)
getStructureInfo env ty =
  let (head, params) = getAppSpine ty in
  case head of
    Const typeName levels =>
      case lookupDecl typeName env of
        Just (IndDecl info _) =>
          case info.constructors of
            [ctor] =>  -- Single constructor = structure
              case lookupDecl ctor.name env of
                Just (CtorDecl _ _ _ _ numParams numFields _) =>
                  Just (typeName, ctor.name, levels, numParams, numFields)
                _ => Nothing
            _ => Nothing  -- Multiple constructors = not a structure
        _ => Nothing
    _ => Nothing

-- Check if expression is a constructor application
isCtorApp : TCEnv -> ClosedExpr -> Bool
isCtorApp env e =
  let (head, _) = getAppSpine e in
  case head of
    Const name _ =>
      case lookupDecl name env of
        Just (CtorDecl _ _ _ _ _ _ _) => True
        _ => False
    _ => False

-- Build projections for structure eta expansion
-- Given struct of type T, build [Proj T 0 struct, Proj T 1 struct, ...]
buildProjections : Name -> Nat -> ClosedExpr -> List ClosedExpr
buildProjections structName numFields struct = go 0 numFields
  where
    go : Nat -> Nat -> List ClosedExpr
    go i Z = []
    go i (S remaining) = Proj structName i struct :: go (S i) remaining

-- Eta-expand a term of structure type to constructor form
-- Given e : Prod A B, returns Prod.mk A B (e.fst) (e.snd)
etaExpandStruct : Name -> List Level -> List ClosedExpr -> Nat -> ClosedExpr -> ClosedExpr
etaExpandStruct ctorName levels params numFields struct =
  let projections = buildProjections (ctorParent ctorName) numFields struct
      ctor = Const ctorName levels
  in mkApp ctor (params ++ projections)
  where
    -- Get parent type name from constructor name (e.g., Prod.mk -> Prod)
    ctorParent : Name -> Name
    ctorParent (Str _ parent) = parent
    ctorParent n = n

-- Try structure eta expansion for definitional equality
-- If one side is a constructor application and the other is not,
-- eta-expand the non-constructor side and compare.
covering
tryStructureEtaCore : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                      TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
tryStructureEtaCore recurEq env t s = do
  -- Only try if t is a ctor app and s is not
  if isCtorApp env t && not (isCtorApp env s)
    then do
      -- Get type of s to know the structure info
      sTy <- inferType env s
      sTy' <- whnf env sTy
      case getStructureInfo env sTy' of
        Just (structName, ctorName, levels, numParams, numFields) =>
          let (_, params) = getAppSpine sTy'
              -- params should have at least numParams elements
              typeParams = listTake numParams params
              sExpanded = etaExpandStruct ctorName levels typeParams numFields s
          in do result <- recurEq env t sExpanded
                pure (Just result)
        Nothing => pure Nothing
    else pure Nothing

covering
tryStructureEta : (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                  TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
tryStructureEta recurEq env t s = do
  result1 <- tryStructureEtaCore recurEq env t s
  case result1 of
    Just b => pure (Just b)
    Nothing => tryStructureEtaCore recurEq env s t

------------------------------------------------------------------------
-- Definitional Equality
------------------------------------------------------------------------

mutual
  covering
  isDefEqNormalized : TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool
  isDefEqNormalized env (Sort l1) (Sort l2) = pure (levelEq l1 l2)
  isDefEqNormalized env (Const n1 ls1) (Const n2 ls2) =
    pure (n1 == n2 && levelListEq ls1 ls2)
  isDefEqNormalized env (Local id1 _) (Local id2 _) =
    if id1 == id2
      then pure True
      else do
        -- Try comparing by types when IDs differ
        case (lookupLocalType id1 env, lookupLocalType id2 env) of
          (Just ty1, Just ty2) => isDefEq env ty1 ty2
          _ => pure False
  isDefEqNormalized env (App f1 a1) (App f2 a2) = do
    eqF <- isDefEq env f1 f2
    if eqF then isDefEq env a1 a2 else pure False
  isDefEqNormalized env (Lam name1 _ ty1 body1) (Lam _ _ ty2 body2) = do
    eqTy <- isDefEq env ty1 ty2
    if eqTy then isDefEqBodyWithNameAndType name1 ty1 isDefEq env body1 body2 else pure False
  isDefEqNormalized env (Pi name1 _ dom1 cod1) (Pi _ _ dom2 cod2) = do
    eqDom <- isDefEq env dom1 dom2
    if eqDom then isDefEqBodyWithNameAndType name1 dom1 isDefEq env cod1 cod2 else pure False
  isDefEqNormalized env (Let name1 ty1 v1 b1) (Let _ ty2 v2 b2) = do
    eqTy <- isDefEq env ty1 ty2
    eqV <- isDefEq env v1 v2
    if eqTy && eqV then isDefEqBodyWithNameAndType name1 ty1 isDefEq env b1 b2 else pure False
  isDefEqNormalized env (Proj sn1 i1 s1) (Proj sn2 i2 s2) =
    if sn1 == sn2 && i1 == i2 then isDefEq env s1 s2 else pure False
  isDefEqNormalized env (NatLit n1) (NatLit n2) = pure (n1 == n2)
  -- NatLit vs Nat.zero/Nat.succ: these should be definitionally equal
  isDefEqNormalized env (NatLit n) other = pure (natLitEqNatExpr n other)
  isDefEqNormalized env other (NatLit n) = pure (natLitEqNatExpr n other)
  isDefEqNormalized env (StringLit s1) (StringLit s2) = pure (s1 == s2)
  isDefEqNormalized env _ _ = pure False

  export covering
  isDefEq : TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool
  isDefEq env e1 e2 = do
    useFuel  -- Consume fuel to prevent infinite loops in complex equalities
    -- Fast path: syntactic equality check before any reduction
    if exprEq e1 e2
      then pure True
      else do
        e1' <- whnf env e1
        e2' <- whnf env e2
        proofIrrel <- tryProofIrrelevance isDefEq env e1' e2'
        case proofIrrel of
          Just result => pure result
          Nothing => isDefEqWhnf e1' e2'
    where
      covering
      isDefEqWhnf : ClosedExpr -> ClosedExpr -> TC Bool
      isDefEqWhnf (Sort l1) (Sort l2) = pure (levelEq l1 l2)
      isDefEqWhnf (Const n1 ls1) (Const n2 ls2) =
        pure (n1 == n2 && levelListEq ls1 ls2)
      isDefEqWhnf (Local id1 _) (Local id2 _) =
        if id1 == id2
          then pure True
          else do
            case (lookupLocalType id1 env, lookupLocalType id2 env) of
              (Just ty1, Just ty2) => isDefEq env ty1 ty2
              _ => pure False
      isDefEqWhnf (App f1 a1) (App f2 a2) = do
        eqF <- isDefEq env f1 f2
        if eqF then isDefEq env a1 a2 else pure False
      isDefEqWhnf (Lam name1 _ ty1 body1) (Lam _ _ ty2 body2) = do
        eqTy <- isDefEq env ty1 ty2
        if eqTy then isDefEqBodyWithNameAndType name1 ty1 isDefEq env body1 body2 else pure False
      isDefEqWhnf (Pi name1 _ dom1 cod1) (Pi _ _ dom2 cod2) = do
        eqDom <- isDefEq env dom1 dom2
        if eqDom then isDefEqBodyWithNameAndType name1 dom1 isDefEq env cod1 cod2 else pure False
      isDefEqWhnf (Let name1 ty1 v1 b1) (Let _ ty2 v2 b2) = do
        eqTy <- isDefEq env ty1 ty2
        eqV <- isDefEq env v1 v2
        if eqTy && eqV then isDefEqBodyWithNameAndType name1 ty1 isDefEq env b1 b2 else pure False
      isDefEqWhnf (Proj sn1 i1 s1) (Proj sn2 i2 s2) =
        if sn1 == sn2 && i1 == i2 then isDefEq env s1 s2 else pure False
      isDefEqWhnf (NatLit n1) (NatLit n2) = pure (n1 == n2)
      -- NatLit vs Nat.zero/Nat.succ: these should be definitionally equal
      isDefEqWhnf (NatLit n) other = pure (natLitEqNatExpr n other)
      isDefEqWhnf other (NatLit n) = pure (natLitEqNatExpr n other)
      isDefEqWhnf (StringLit s1) (StringLit s2) = pure (s1 == s2)
      isDefEqWhnf t s = do
        etaResult <- tryEtaExpansion isDefEq env t s
        case etaResult of
          Just b => pure b
          Nothing => do
            -- Try structure eta expansion
            structEtaResult <- tryStructureEta isDefEq env t s
            case structEtaResult of
              Just b => pure b
              Nothing => do
                -- WHNF structural comparison failed, try full normalization as fallback
                t' <- normalizeType env t
                s' <- normalizeType env s
                -- Check if normalization made progress
                if exprEq t t' && exprEq s s'
                  then pure False  -- No progress, give up
                  else isDefEqNormalized env t' s'

------------------------------------------------------------------------
-- Convenience Functions
------------------------------------------------------------------------

export covering
checkExpr : TCEnv -> ClosedExpr -> TC ClosedExpr
checkExpr = inferType

export covering
hasType : TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool
hasType env e expectedTy = do
  actualTy <- inferType env e
  isDefEq env actualTy expectedTy
