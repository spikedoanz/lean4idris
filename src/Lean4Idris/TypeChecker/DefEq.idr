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
-- Placeholder Matching
------------------------------------------------------------------------

isPlaceholderForBinder : Name -> Name -> Bool
isPlaceholderForBinder (Str "_local" (Num _ binderName)) targetName = binderName == targetName
isPlaceholderForBinder (Str "_isDefEqBody" (Str _ binderName)) targetName = binderName == targetName
isPlaceholderForBinder _ _ = False

isComparisonPlaceholder : Name -> Bool
isComparisonPlaceholder (Str "_x" (Str "_isDefEqBody" _)) = True
isComparisonPlaceholder (Str "_isDefEqBody" _) = True
isComparisonPlaceholder _ = False

covering
containsPlaceholderForBinder : Name -> ClosedExpr -> Bool
containsPlaceholderForBinder targetBinder (Const name []) = isPlaceholderForBinder name targetBinder
containsPlaceholderForBinder _ (Const _ _) = False
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

replacePlaceholdersForBinderN : Name -> {n : Nat} -> Expr n -> Name -> Expr n
replacePlaceholdersForBinderN targetBinder (BVar i) _ = BVar i
replacePlaceholdersForBinderN targetBinder (Sort l) _ = Sort l
replacePlaceholdersForBinderN targetBinder (Const name []) sharedName =
  if isPlaceholderForBinder name targetBinder then Const sharedName [] else Const name []
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

replacePlaceholdersForBinder : Name -> ClosedExpr -> Name -> ClosedExpr
replacePlaceholdersForBinder targetBinder e sharedName = replacePlaceholdersForBinderN targetBinder e sharedName

------------------------------------------------------------------------
-- Body Comparison Helpers
------------------------------------------------------------------------

covering
isDefEqBodyWithDepth : Nat -> ClosedExpr -> (TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool) ->
                       TCEnv -> Expr 1 -> Expr 1 -> TC Bool
isDefEqBodyWithDepth depth binderType recur env b1 b2 =
  let counter = env.nextPlaceholder
      phName = Str "_isDefEqBody" (Num counter (Num depth Anonymous))
      env' = addPlaceholder phName binderType ({ nextPlaceholder := S counter } env)
      e1' : ClosedExpr = instantiate1 (believe_me b1) (Const phName [])
      e2' : ClosedExpr = instantiate1 (believe_me b2) (Const phName [])
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
-- Definitional Equality
------------------------------------------------------------------------

export covering
isDefEq : TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool
isDefEq env e1 e2 = do
  -- Substitute let-placeholders with their values BEFORE whnf
  -- This is done once at each isDefEq call, not in the whnf hot loop
  let e1s = substLetPlaceholders env e1
  let e2s = substLetPlaceholders env e2
  e1' <- whnf env e1s
  e2' <- whnf env e2s
  proofIrrel <- tryProofIrrelevance isDefEq env e1' e2'
  case proofIrrel of
    Just result => pure result
    Nothing => isDefEqWhnf e1' e2'
  where
    areEquivalentPlaceholders : Name -> Name -> Bool
    areEquivalentPlaceholders c1 c2 =
      let compDepth1 = extractComparisonPlaceholderDepth c1
          compDepth2 = extractComparisonPlaceholderDepth c2
          infDepth1 = extractInferencePlaceholderDepth c1
          infDepth2 = extractInferencePlaceholderDepth c2
          depth1 = compDepth1 <|> infDepth1
          depth2 = compDepth2 <|> infDepth2
      in case (depth1, depth2) of
           (Just d1, Just d2) => d1 == d2
           _ => case (extractPlaceholderBase c1, extractPlaceholderBase c2) of
                  (Just base1, Just base2) => base1 == base2
                  _ => False

    covering
    isDefEqWhnf : ClosedExpr -> ClosedExpr -> TC Bool
    isDefEqWhnf (Sort l1) (Sort l2) = pure (levelEq l1 l2)
    isDefEqWhnf (Const n1 ls1) (Const n2 ls2) =
      if n1 == n2 && levelListEq ls1 ls2 then pure True
      else case (ls1, ls2) of
             ([], []) => pure (areEquivalentPlaceholders n1 n2)
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
    isDefEqWhnf (StringLit s1) (StringLit s2) = pure (s1 == s2)
    isDefEqWhnf t s = do
      etaResult <- tryEtaExpansion isDefEq env t s
      case etaResult of
        Just b => pure b
        Nothing => pure False

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
