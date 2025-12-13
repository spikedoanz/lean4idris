module Lean4Idris.TypeChecker.DefEq

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Subst
import Lean4Idris.TypeChecker.Monad
import Lean4Idris.TypeChecker.Reduction
import Lean4Idris.TypeChecker.Infer
import Lean4Idris.Pretty
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
natLitToNatExpr : Nat -> Expr
natLitToNatExpr Z = Const natZeroName []
natLitToNatExpr (S n) = App (Const natSuccName []) (NatLit n)

-- Try to extract a Nat from Nat.zero/Nat.succ constructors
covering
getNatFromExpr : Expr -> Maybe Nat
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
natLitEqNatExpr : Nat -> Expr -> Bool
natLitEqNatExpr n e = case getNatFromExpr e of
  Just m => n == m
  Nothing => False

------------------------------------------------------------------------
-- Proof Irrelevance
------------------------------------------------------------------------

export covering
isProp : TCEnv -> Expr -> TC Bool
isProp env e = do
  ty <- inferType env e
  tyTy <- inferType env ty
  tyTy' <- whnf env tyTy
  case tyTy' of
    Sort l => pure (simplify l == Zero)
    _ => pure False

isDefinitelyNotProof : Expr -> Bool
isDefinitelyNotProof (Sort _) = True
isDefinitelyNotProof (Pi _ _ _ _) = True
isDefinitelyNotProof (Lam _ _ _ _) = True
isDefinitelyNotProof _ = False

covering
tryProofIrrelevance : (TCEnv -> Expr -> Expr -> TC Bool) ->
                      TCEnv -> Expr -> Expr -> TC (Maybe Bool)
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
-- Level Equality
------------------------------------------------------------------------

flattenMax : Level -> List Level
flattenMax (Max a b) = flattenMax a ++ flattenMax b
flattenMax l = [l]

sortLevels : List Level -> List Level
sortLevels = sortBy (\a, b => if levelLt a b then LT else if a == b then EQ else GT)

covering
levelEqCore : Level -> Level -> Bool

covering
levelListEqCore : List Level -> List Level -> Bool
levelListEqCore [] [] = True
levelListEqCore (x :: xs) (y :: ys) = levelEqCore x y && levelListEqCore xs ys
levelListEqCore _ _ = False

levelEqCore Zero Zero = True
levelEqCore (Succ l1) (Succ l2) = levelEqCore l1 l2
levelEqCore l1@(Max _ _) l2@(Max _ _) =
  let terms1 = sortLevels (flattenMax l1)
      terms2 = sortLevels (flattenMax l2)
  in levelListEqCore terms1 terms2
levelEqCore (IMax a1 b1) (IMax a2 b2) = levelEqCore a1 a2 && levelEqCore b1 b2
levelEqCore (Param n1) (Param n2) = n1 == n2
levelEqCore _ _ = False

covering
levelEq : Level -> Level -> Bool
levelEq l1 l2 = let l1' = simplify l1
                    l2' = simplify l2
                in levelEqCore l1' l2'

covering
levelListEq : List Level -> List Level -> Bool
levelListEq [] [] = True
levelListEq (l1 :: ls1) (l2 :: ls2) = levelEq l1 l2 && levelListEq ls1 ls2
levelListEq _ _ = False

------------------------------------------------------------------------
-- Body Comparison Helpers
------------------------------------------------------------------------

covering
isDefEqBodyWithDepth : Nat -> Expr -> (TCEnv -> Expr -> Expr -> TC Bool) ->
                       TCEnv -> Expr -> Expr -> TC Bool
isDefEqBodyWithDepth depth binderType recur env b1 b2 =
  let localId = env.nextLocalId
      localVar : Expr = Local localId Anonymous
      env' = addLocalType localId binderType ({ nextLocalId := S localId } env)
      e1' : Expr = instantiate1 b1 localVar
      e2' : Expr = instantiate1 b2 localVar
  in recur env' e1' e2'

covering
isDefEqBodyWithNameAndType : Name -> Expr -> (TCEnv -> Expr -> Expr -> TC Bool) ->
                              TCEnv -> Expr -> Expr -> TC Bool
isDefEqBodyWithNameAndType binderName binderType recur env b1 b2 =
  isDefEqBodyWithDepth 0 binderType recur env b1 b2

covering
isDefEqBodyWithName : Name -> (TCEnv -> Expr -> Expr -> TC Bool) ->
                       TCEnv -> Expr -> Expr -> TC Bool
isDefEqBodyWithName binderName recur env b1 b2 =
  isDefEqBodyWithDepth 0 (Sort Zero) recur env b1 b2

covering
isDefEqBody : (TCEnv -> Expr -> Expr -> TC Bool) ->
              TCEnv -> Expr -> Expr -> TC Bool
isDefEqBody recur env b1 b2 =
  isDefEqBodyWithDepth 0 (Sort Zero) recur env b1 b2

------------------------------------------------------------------------
-- Eta Expansion
------------------------------------------------------------------------

covering
tryEtaExpansionCore : (TCEnv -> Expr -> Expr -> TC Bool) ->
                      TCEnv -> Expr -> Expr -> TC (Maybe Bool)
tryEtaExpansionCore recurEq env t s = case t of
  Lam name bi ty body => case s of
    Lam _ _ _ _ => pure Nothing
    _ => do
      sTy <- inferType env s
      sTy' <- whnf env sTy
      case sTy' of
        Pi piName piBi dom cod =>
          -- Eta-expand s: λx. s x (with s lifted by 1)
          let sLifted = liftLooseBVars 0 1 s
              sExpanded : Expr = Lam piName piBi dom (App sLifted (BVar 0))
          in do result <- recurEq env t sExpanded
                pure (Just result)
        _ => pure Nothing
  _ => pure Nothing

covering
tryEtaExpansion : (TCEnv -> Expr -> Expr -> TC Bool) ->
                  TCEnv -> Expr -> Expr -> TC (Maybe Bool)
tryEtaExpansion recurEq env t s = do
  result1 <- tryEtaExpansionCore recurEq env t s
  case result1 of
    Just b => pure (Just b)
    Nothing => tryEtaExpansionCore recurEq env s t

------------------------------------------------------------------------
-- Structure Eta Expansion
------------------------------------------------------------------------

-- Check if a type is a structure (single-constructor inductive)
getStructureInfo : TCEnv -> Expr -> Maybe (Name, Name, List Level, Nat, Nat)
getStructureInfo env ty =
  let (head, params) = getAppSpine ty in
  case head of
    Const typeName levels =>
      case lookupDecl typeName env of
        Just (IndDecl info _) =>
          case info.constructors of
            [ctor] =>
              case lookupDecl ctor.name env of
                Just (CtorDecl _ _ _ _ numParams numFields _) =>
                  Just (typeName, ctor.name, levels, numParams, numFields)
                _ => Nothing
            _ => Nothing
        _ => Nothing
    _ => Nothing

-- Check if expression is a constructor application
isCtorApp : TCEnv -> Expr -> Bool
isCtorApp env e =
  let (head, _) = getAppSpine e in
  case head of
    Const name _ =>
      case lookupDecl name env of
        Just (CtorDecl _ _ _ _ _ _ _) => True
        _ => False
    _ => False

-- Build projections for structure eta expansion
buildProjections : Name -> Nat -> Expr -> List Expr
buildProjections structName numFields struct = go 0 numFields
  where
    go : Nat -> Nat -> List Expr
    go i Z = []
    go i (S remaining) = Proj structName i struct :: go (S i) remaining

-- Eta-expand a term of structure type to constructor form
etaExpandStruct : Name -> List Level -> List Expr -> Nat -> Expr -> Expr
etaExpandStruct ctorName levels params numFields struct =
  let projections = buildProjections (ctorParent ctorName) numFields struct
      ctor = Const ctorName levels
  in mkApp ctor (params ++ projections)
  where
    ctorParent : Name -> Name
    ctorParent (Str _ parent) = parent
    ctorParent n = n

covering
tryStructureEtaCore : (TCEnv -> Expr -> Expr -> TC Bool) ->
                      TCEnv -> Expr -> Expr -> TC (Maybe Bool)
tryStructureEtaCore recurEq env t s = do
  if isCtorApp env t && not (isCtorApp env s)
    then do
      sTy <- inferType env s
      sTy' <- whnf env sTy
      case getStructureInfo env sTy' of
        Just (structName, ctorName, levels, numParams, numFields) =>
          let (_, params) = getAppSpine sTy'
              typeParams = listTake numParams params
              sExpanded = etaExpandStruct ctorName levels typeParams numFields s
          in do result <- recurEq env t sExpanded
                pure (Just result)
        Nothing => pure Nothing
    else pure Nothing

covering
tryStructureEta : (TCEnv -> Expr -> Expr -> TC Bool) ->
                  TCEnv -> Expr -> Expr -> TC (Maybe Bool)
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
  isDefEqNormalized : TCEnv -> Expr -> Expr -> TC Bool
  isDefEqNormalized env (Sort l1) (Sort l2) = pure (levelEq l1 l2)
  isDefEqNormalized env (Const n1 ls1) (Const n2 ls2) =
    pure (n1 == n2 && levelListEq ls1 ls2)
  isDefEqNormalized env (Local id1 _) (Local id2 _) =
    if id1 == id2
      then pure True
      else do
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
  isDefEqNormalized env (NatLit n) other = pure (natLitEqNatExpr n other)
  isDefEqNormalized env other (NatLit n) = pure (natLitEqNatExpr n other)
  isDefEqNormalized env (StringLit s1) (StringLit s2) = pure (s1 == s2)
  isDefEqNormalized env _ _ = pure False

  export covering
  isDefEq : TCEnv -> Expr -> Expr -> TC Bool
  isDefEq env e1 e2 = do
    useFuel
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
      isDefEqWhnf : Expr -> Expr -> TC Bool
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
      isDefEqWhnf (NatLit n) other = pure (natLitEqNatExpr n other)
      isDefEqWhnf other (NatLit n) = pure (natLitEqNatExpr n other)
      isDefEqWhnf (StringLit s1) (StringLit s2) = pure (s1 == s2)
      isDefEqWhnf t s = do
        etaResult <- tryEtaExpansion isDefEq env t s
        case etaResult of
          Just b => pure b
          Nothing => do
            structEtaResult <- tryStructureEta isDefEq env t s
            case structEtaResult of
              Just b => pure b
              Nothing => do
                t' <- normalizeType env t
                s' <- normalizeType env s
                if exprEq t t' && exprEq s s'
                  then pure False
                  else isDefEqNormalized env t' s'

------------------------------------------------------------------------
-- Convenience Functions
------------------------------------------------------------------------

export covering
checkExpr : TCEnv -> Expr -> TC Expr
checkExpr = inferType

export covering
hasType : TCEnv -> Expr -> Expr -> TC Bool
hasType env e expectedTy = do
  actualTy <- inferType env e
  isDefEq env actualTy expectedTy
