module Lean4Idris.TypeChecker.Infer

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Subst
import Lean4Idris.Pretty
import Lean4Idris.TypeChecker.Monad
import Lean4Idris.TypeChecker.Reduction
import Data.SortedMap
import Data.Vect
import Data.List
import Debug.Trace

%default total

------------------------------------------------------------------------
-- Ensure Sort/Pi
------------------------------------------------------------------------

mutual
  covering
  ensureSortOfApp : TCEnv -> Expr -> List Expr -> TC Level
  ensureSortOfApp env' ty [] = ensureSortWhnf env' ty
  ensureSortOfApp env' (Pi _ _ dom cod) (arg :: args) =
    ensureSortOfApp env' (instantiate1 cod arg) args
  ensureSortOfApp env' ty args = case ty of
    Sort l => pure l
    Pi _ _ _ cod => pure Zero
    Const name levels => case lookupDecl name env' of
      Just decl => case declType decl of
        Just dty =>
          let params = declLevelParams decl
              dty' = instantiateLevelParams params levels dty
          in ensureSortOfApp env' dty' args
        Nothing => throw (OtherError $ "ensureSort: const " ++ show name ++ " has no type")
      Nothing => throw (OtherError $ "ensureSort: unknown const " ++ show name)
    App _ _ => case getAppHead ty of
      Just (name, levels, innerArgs) => case lookupDecl name env' of
        Just decl => case declType decl of
          Just dty =>
            let params = declLevelParams decl
                dty' = instantiateLevelParams params levels dty
            in ensureSortOfApp env' dty' (innerArgs ++ args)
          Nothing => throw (TypeExpected ty)
        Nothing => throw (TypeExpected ty)
      Nothing => throw (TypeExpected ty)
    _ => throw (OtherError $ "ensureSort: exhausted Pis")

  covering
  ensureSortWhnf : TCEnv -> Expr -> TC Level
  ensureSortWhnf env' (Sort l) = pure l
  ensureSortWhnf env' (Local id _) =
    case lookupLocalType id env' of
      Just ty => ensureSortWhnf env' ty
      Nothing => throw (OtherError $ "ensureSortWhnf: Local " ++ show id ++ " type not found")
  ensureSortWhnf env' expr@(App _ _) = case getAppHead expr of
    Just (name, levels, args) => case lookupDecl name env' of
      Just decl => case declType decl of
        Just ty =>
          let params = declLevelParams decl
              ty' = instantiateLevelParams params levels ty
          in ensureSortOfApp env' ty' args
        Nothing => throw (TypeExpected expr)
      Nothing => throw (OtherError $ "ensureSort: stuck App with unknown head " ++ show name)
    Nothing => throw (TypeExpected expr)
  ensureSortWhnf _ (Pi _ _ _ _) = pure Zero
  ensureSortWhnf _ other = throw (TypeExpected other)

export covering
ensureSort : TCEnv -> Expr -> TC Level
ensureSort env e = do
  e' <- whnf env e
  ensureSortWhnf env e'

mutual
  covering
  ensurePiOfApp : TCEnv -> Expr -> List Expr -> TC (Name, BinderInfo, Expr, Expr)
  ensurePiOfApp env' ty [] = ensurePiWhnf env' ty
  ensurePiOfApp env' (Pi _ _ dom cod) (arg :: args) = do
    let resultTy = instantiate1 cod arg
    resultTy' <- whnf env' resultTy
    ensurePiOfApp env' resultTy' args
  ensurePiOfApp env' ty args =
    throw (OtherError $ "ensurePi: exhausted Pi types with " ++ show (length args) ++ " args remaining")

  covering
  ensurePiWhnf : TCEnv -> Expr -> TC (Name, BinderInfo, Expr, Expr)
  ensurePiWhnf env' expr = case expr of
    Pi name bi dom cod => pure (name, bi, dom, cod)
    Local id _ =>
      case lookupLocalType id env' of
        Just ty => ensurePiWhnf env' ty
        Nothing => throw (OtherError $ "ensurePiWhnf: Local " ++ show id ++ " type not found")
    Const name levels => case lookupDecl name env' of
      Just decl => case getDeclValue decl of
        Just val =>
          let unfolded = instantiateLevelParams (declLevelParams decl) levels val
          in ensurePiWhnf env' unfolded
        Nothing => throw (FunctionExpected expr)
      Nothing => throw (OtherError $ "ensurePiWhnf Const: " ++ show name ++ " not found")
    App _ _ => case getAppHead expr of
      Just (name, levels, args) => case lookupDecl name env' of
        Just decl => case declType decl of
          Just ty =>
            let params = declLevelParams decl
                ty' = instantiateLevelParams params levels ty
            in ensurePiOfApp env' ty' args
          Nothing => throw (FunctionExpected expr)
        Nothing => throw (OtherError $ "ensurePi: stuck App with unknown head " ++ show name)
      Nothing => throw (FunctionExpected expr)
    Sort l => throw (FunctionExpected expr)
    Lam _ _ _ _ => throw (OtherError $ "ensurePiWhnf: expected Pi, got Lam")
    Let _ _ _ _ => throw (OtherError $ "ensurePiWhnf: expected Pi, got Let")
    BVar _ => throw (OtherError $ "ensurePiWhnf: expected Pi, got BVar")
    Proj _ _ _ => throw (OtherError $ "ensurePiWhnf: expected Pi, got Proj")
    NatLit _ => throw (OtherError $ "ensurePiWhnf: expected Pi, got NatLit")
    StringLit _ => throw (OtherError $ "ensurePiWhnf: expected Pi, got StringLit")

export covering
ensurePi : TCEnv -> Expr -> TC (Name, BinderInfo, Expr, Expr)
ensurePi env e = do
  e' <- whnf env e
  ensurePiWhnf env e'

export covering
buildPlaceholders : TCEnv -> LocalCtx -> (TCEnv, LocalCtx, List Expr)
buildPlaceholders env ctx = buildWithDepth env ctx 0
  where
    buildWithDepth : TCEnv -> LocalCtx -> Nat -> (TCEnv, LocalCtx, List Expr)
    buildWithDepth env [] _ = (env, [], [])
    buildWithDepth env (entry :: rest) depth = case entry.placeholder of
      Just ph =>
        let (env', rest', phs) = buildWithDepth env rest (S depth)
        in (env', entry :: rest', ph :: phs)
      Nothing =>
        let localId = env.nextLocalId
            env' = { nextLocalId := S localId } env
            env'' = addLocalType localId entry.type env'
            ph : Expr = Local localId entry.name
            entry' = { placeholder := Just ph } entry
            (env''', rest', phs) = buildWithDepth env'' rest (S depth)
        in (env''', entry' :: rest', ph :: phs)

export covering
closeWithPlaceholders : TCEnv -> LocalCtx -> Expr -> (TCEnv, LocalCtx, Expr)
closeWithPlaceholders env ctx e =
  let (env', ctx', placeholders) = buildPlaceholders env ctx
      -- Apply placeholders to close the expression
      closed = goSubstAllList 0 placeholders e
  in (env', ctx', closed)
  where
    -- Like goSubstAll but using List
    goSubstAllList : Nat -> List Expr -> Expr -> Expr
    goSubstAllList depth args (BVar idx) =
      if idx < depth
        then BVar idx
        else case getAt (minus idx depth) args of
               Just replacement => replacement
               Nothing => BVar idx
    goSubstAllList depth args (Local id name) = Local id name
    goSubstAllList depth args (Sort l) = Sort l
    goSubstAllList depth args (Const name lvls) = Const name lvls
    goSubstAllList depth args (App f x) = App (goSubstAllList depth args f) (goSubstAllList depth args x)
    goSubstAllList depth args (Lam name bi ty body) =
      Lam name bi (goSubstAllList depth args ty) (goSubstAllList (S depth) args body)
    goSubstAllList depth args (Pi name bi ty body) =
      Pi name bi (goSubstAllList depth args ty) (goSubstAllList (S depth) args body)
    goSubstAllList depth args (Let name ty val body) =
      Let name (goSubstAllList depth args ty) (goSubstAllList depth args val) (goSubstAllList (S depth) args body)
    goSubstAllList depth args (Proj sname fieldIdx s) = Proj sname fieldIdx (goSubstAllList depth args s)
    goSubstAllList depth args (NatLit k) = NatLit k
    goSubstAllList depth args (StringLit s) = StringLit s

-- Extract the Local ID from a placeholder if present
getLocalId : Maybe Expr -> Maybe Nat
getLocalId (Just (Local id _)) = Just id
getLocalId _ = Nothing

-- Substitute a let-bound placeholder in the body type with its value
covering
substLetPlaceholder : LocalCtx -> Expr -> Expr -> Expr
substLetPlaceholder [] valClosed bodyTy = bodyTy
substLetPlaceholder (entry :: _) valClosed bodyTy =
  case getLocalId entry.placeholder of
    Just localId => substLocal localId valClosed bodyTy
    Nothing => bodyTy

findLocalIdx : List LocalEntry -> Nat -> Nat -> Maybe Nat
findLocalIdx [] _ _ = Nothing
findLocalIdx (entry :: rest) targetId idx = case entry.placeholder of
  Just (Local id _) =>
    if id == targetId then Just idx else findLocalIdx rest targetId (S idx)
  _ => findLocalIdx rest targetId (S idx)

makeBVarFromNat : Nat -> Expr
makeBVarFromNat k = BVar k

covering
replaceLocalsWithBVars : List LocalEntry -> Nat -> Expr -> Expr
replaceLocalsWithBVars entries depth (Sort l) = Sort l
replaceLocalsWithBVars entries depth (BVar i) = BVar i
replaceLocalsWithBVars entries depth (Local id name) =
  case findLocalIdx entries id 0 of
    Just idx => makeBVarFromNat (idx + depth)
    Nothing => Local id name
replaceLocalsWithBVars entries depth (Const name ls) = Const name ls
replaceLocalsWithBVars entries depth (App f x) =
  App (replaceLocalsWithBVars entries depth f) (replaceLocalsWithBVars entries depth x)
replaceLocalsWithBVars entries depth (Lam name bi ty body) =
  Lam name bi (replaceLocalsWithBVars entries depth ty)
              (replaceLocalsWithBVars entries (S depth) body)
replaceLocalsWithBVars entries depth (Pi name bi dom cod) =
  Pi name bi (replaceLocalsWithBVars entries depth dom)
             (replaceLocalsWithBVars entries (S depth) cod)
replaceLocalsWithBVars entries depth (Let name ty val body) =
  Let name (replaceLocalsWithBVars entries depth ty)
           (replaceLocalsWithBVars entries depth val)
           (replaceLocalsWithBVars entries (S depth) body)
replaceLocalsWithBVars entries depth (Proj sn i s) =
  Proj sn i (replaceLocalsWithBVars entries depth s)
replaceLocalsWithBVars entries depth (NatLit k) = NatLit k
replaceLocalsWithBVars entries depth (StringLit s) = StringLit s

export covering
replaceAllPlaceholdersWithBVars' : List LocalEntry -> Expr -> Expr
replaceAllPlaceholdersWithBVars' entries e = replaceLocalsWithBVars entries 0 e

export covering
replaceAllPlaceholdersWithBVars : LocalCtx -> Expr -> Expr
replaceAllPlaceholdersWithBVars ctx e = replaceLocalsWithBVars ctx 0 e

-- Replace BVars that reference context entries with placeholders
covering
replaceBVarsWithPlaceholders : List LocalEntry -> Nat -> Expr -> Expr
replaceBVarsWithPlaceholders entries depth (Sort l) = Sort l
replaceBVarsWithPlaceholders entries depth (BVar i) =
  if i >= depth
    then case getPlaceholderAt entries (minus i depth) of
           Just ph => ph
           Nothing => BVar i
    else BVar i
  where
    getPlaceholderAt : List LocalEntry -> Nat -> Maybe Expr
    getPlaceholderAt [] _ = Nothing
    getPlaceholderAt (e :: es) Z = e.placeholder
    getPlaceholderAt (e :: es) (S k) = getPlaceholderAt es k
replaceBVarsWithPlaceholders entries depth (Local id name) = Local id name
replaceBVarsWithPlaceholders entries depth (Const name ls) = Const name ls
replaceBVarsWithPlaceholders entries depth (App f x) =
  App (replaceBVarsWithPlaceholders entries depth f) (replaceBVarsWithPlaceholders entries depth x)
replaceBVarsWithPlaceholders entries depth (Lam name bi ty body) =
  Lam name bi (replaceBVarsWithPlaceholders entries depth ty)
              (replaceBVarsWithPlaceholders entries (S depth) body)
replaceBVarsWithPlaceholders entries depth (Pi name bi dom cod) =
  Pi name bi (replaceBVarsWithPlaceholders entries depth dom)
             (replaceBVarsWithPlaceholders entries (S depth) cod)
replaceBVarsWithPlaceholders entries depth (Let name ty val body) =
  Let name (replaceBVarsWithPlaceholders entries depth ty)
           (replaceBVarsWithPlaceholders entries depth val)
           (replaceBVarsWithPlaceholders entries (S depth) body)
replaceBVarsWithPlaceholders entries depth (Proj sn i s) =
  Proj sn i (replaceBVarsWithPlaceholders entries depth s)
replaceBVarsWithPlaceholders entries depth (NatLit k) = NatLit k
replaceBVarsWithPlaceholders entries depth (StringLit s) = StringLit s

export covering
closeBVarsInType : List LocalEntry -> Expr -> Expr
closeBVarsInType entries e = replaceBVarsWithPlaceholders entries 0 e

------------------------------------------------------------------------
-- Structure/Projection Helpers
------------------------------------------------------------------------

export
getInductiveInfo : TCEnv -> Name -> Maybe InductiveInfo
getInductiveInfo env name = case lookupDecl name env of
  Just (IndDecl info _) => Just info
  _ => Nothing

||| Get inductive info along with its level parameters
export
getInductiveInfoWithLevels : TCEnv -> Name -> Maybe (InductiveInfo, List Name)
getInductiveInfoWithLevels env name = case lookupDecl name env of
  Just (IndDecl info levelParams) => Just (info, levelParams)
  _ => Nothing

export
getStructCtor : TCEnv -> Name -> Maybe ConstructorInfo
getStructCtor env structName = do
  indInfo <- getInductiveInfo env structName
  case indInfo.constructors of
    [ctorInfo] => case lookupDecl ctorInfo.name env of
      Just (CtorDecl name ty _ _ _ _ _) => Just (MkConstructorInfo name ty)
      _ => Just ctorInfo
    _ => Nothing

||| Build projections of earlier fields for substitution.
buildFieldProjections : Name -> Nat -> Expr -> List Expr
buildFieldProjections structName idx structExpr =
  map (\i => Proj structName i structExpr) [0 .. (minus idx 1)]

export covering
getProjType : TCEnv -> Name -> Nat -> List Expr -> Maybe Expr
getProjType env structName idx structParams = do
  indInfo <- getInductiveInfo env structName
  let numParams = indInfo.numParams
  ctor <- getStructCtor env structName
  getNthPiDomSubst (numParams + idx) structParams ctor.type

||| Get the type of a projection, accounting for dependent fields.
||| For dependent fields (like Subtype.property), the field type may depend
||| on projections of earlier fields.
|||
||| @levels The universe levels from the structure type (e.g., from `Applicative.{u_1, u_2}`)
export covering
getProjTypeWithStruct : TCEnv -> Name -> Nat -> List Level -> List ClosedExpr -> ClosedExpr -> Maybe ClosedExpr
getProjTypeWithStruct env structName idx typeLevels structParams structExpr = do
  (indInfo, levelParams) <- getInductiveInfoWithLevels env structName
  let numParams = indInfo.numParams
  ctor <- getStructCtor env structName
  let fieldProjs = buildFieldProjections structName idx structExpr
  -- First, instantiate the constructor type with the actual universe levels
  let ctorTyInstantiated = instantiateLevelParams levelParams typeLevels ctor.type
  -- Then substitute type parameters AND earlier field projections
  getNthPiDomSubst (numParams + idx) (structParams ++ fieldProjs) ctorTyInstantiated

------------------------------------------------------------------------
-- Normalization
------------------------------------------------------------------------

covering
betaReduceN : Expr -> Maybe Expr
betaReduceN (App (Lam _ _ _ body) arg) = Just (instantiate1 body arg)
betaReduceN _ = Nothing

getAppSpineN : Expr -> (Expr, List Expr)
getAppSpineN e = go e []
  where
    go : Expr -> List Expr -> (Expr, List Expr)
    go (App f x) args = go f (x :: args)
    go e args = (e, args)

mkAppN : Expr -> List Expr -> Expr
mkAppN f [] = f
mkAppN f (x :: xs) = mkAppN (App f x) xs

covering
unfoldConstN : TCEnv -> Name -> List Level -> Maybe Expr
unfoldConstN env name levels = do
  decl <- lookupDecl name env
  value <- getDeclValue decl
  let params = declLevelParams decl
  guard (length params == length levels)
  let instantiated = instantiateLevelParams params levels value
  Just instantiated

covering
tryDeltaOpenN : TCEnv -> Expr -> Maybe Expr
tryDeltaOpenN env e =
  let (head, args) = getAppSpineN e
  in case head of
    Const name levels => do
      unfolded <- unfoldConstN env name levels
      Just (mkAppN unfolded args)
    _ => Nothing

tryProjReductionN : TCEnv -> Expr -> Maybe Expr
tryProjReductionN env (Proj structName idx struct) = do
  let (head, args) = getAppSpineN struct
  case head of
    Const ctorName _ => do
      (_, _, numParams, numFields) <- getConstructorInfo env ctorName
      guard (idx < numFields)
      listNth args (numParams + idx)
    _ => Nothing
tryProjReductionN _ _ = Nothing

tryNatRecIota : Expr -> Maybe Expr
tryNatRecIota e =
  let (head, args) = getAppSpineN e
  in case head of
    Const name [u] =>
      if name == Str "rec" (Str "Nat" Anonymous)
        then case args of
          [motive, zeroCase, succCase, major] => case major of
            Const zeroName [] =>
              if zeroName == Str "zero" (Str "Nat" Anonymous)
                then Just zeroCase else Nothing
            App (Const succName []) innerN =>
              if succName == Str "succ" (Str "Nat" Anonymous)
                then let recCall = mkAppN (Const name [u]) [motive, zeroCase, succCase, innerN]
                     in Just (App (App succCase innerN) recCall)
                else Nothing
            _ => Nothing
          _ => Nothing
        else Nothing
    _ => Nothing

export covering
normalizeTypeOpenWithEnv : TCEnv -> Expr -> TC Expr
normalizeTypeOpenWithEnv env e = do
  useFuel
  case betaReduceN e of
    Just e' => normalizeTypeOpenWithEnv env e'
    Nothing => case e of
      Pi name bi dom cod => do
        dom' <- normalizeTypeOpenWithEnv env dom
        cod' <- normalizeTypeOpenWithEnv env cod
        pure (Pi name bi dom' cod')
      Lam name bi ty body => do
        ty' <- normalizeTypeOpenWithEnv env ty
        body' <- normalizeTypeOpenWithEnv env body
        pure (Lam name bi ty' body')
      App f arg => do
        f' <- normalizeTypeOpenWithEnv env f
        arg' <- normalizeTypeOpenWithEnv env arg
        let app = App f' arg'
        case betaReduceN app of
          Just reduced => normalizeTypeOpenWithEnv env reduced
          Nothing => case tryNatRecIota app of
            Just reduced => normalizeTypeOpenWithEnv env reduced
            Nothing => case tryDeltaOpenN env app of
              Just reduced => normalizeTypeOpenWithEnv env reduced
              Nothing => case tryProjReductionN env f' of
                Just fReduced => normalizeTypeOpenWithEnv env (App fReduced arg')
                Nothing => pure app
      Let name ty val body => normalizeTypeOpenWithEnv env (instantiate1 body val)
      Proj n i e => do
        e' <- normalizeTypeOpenWithEnv env e
        let proj = Proj n i e'
        case tryProjReductionN env proj of
          Just reduced => normalizeTypeOpenWithEnv env reduced
          Nothing => pure proj
      Sort l => pure (Sort (simplify l))
      Const name levels => case unfoldConstN env name levels of
        Just unfolded => normalizeTypeOpenWithEnv env unfolded
        Nothing => pure (Const name levels)
      e => pure e

export covering
normalizeType : TCEnv -> Expr -> TC Expr
normalizeType env e = do
  e' <- whnf env e
  normalizeDeep e'
  where
    covering
    normalizeDeep : Expr -> TC Expr
    normalizeDeep (Pi name bi dom cod) = do
      useFuel
      dom' <- normalizeType env dom
      cod' <- normalizeTypeOpenWithEnv env cod
      pure (Pi name bi dom' cod')
    normalizeDeep (Lam name bi ty body) = do
      useFuel
      ty' <- normalizeType env ty
      body' <- normalizeTypeOpenWithEnv env body
      pure (Lam name bi ty' body')
    normalizeDeep (App f arg) = do
      useFuel
      f' <- normalizeType env f
      arg' <- normalizeType env arg
      let app = App f' arg'
      app' <- whnf env app
      case app' of
        App _ _ => pure app'
        _ => normalizeDeep app'
    normalizeDeep (Let name ty val body) = do
      useFuel
      ty' <- normalizeType env ty
      val' <- normalizeType env val
      body' <- normalizeTypeOpenWithEnv env body
      pure (Let name ty' val' body')
    normalizeDeep (Proj n i e) = do
      useFuel
      e' <- normalizeType env e
      pure (Proj n i e')
    normalizeDeep (Sort l) = pure (Sort (simplify l))
    normalizeDeep e = pure e

------------------------------------------------------------------------
-- Alpha Equivalence
------------------------------------------------------------------------

export covering
alphaEq : Expr -> Expr -> Bool
alphaEq = go
  where
    covering
    go : Expr -> Expr -> Bool
    go (Sort l1) (Sort l2) = simplify l1 == simplify l2
    go (Const n1 ls1) (Const n2 ls2) = n1 == n2 && map simplify ls1 == map simplify ls2
    go (BVar i1) (BVar i2) = i1 == i2
    go (Local id1 _) (Local id2 _) = id1 == id2
    go (App f1 a1) (App f2 a2) = go f1 f2 && go a1 a2
    go (Lam _ _ ty1 body1) (Lam _ _ ty2 body2) = go ty1 ty2 && go body1 body2
    go (Pi _ _ dom1 cod1) (Pi _ _ dom2 cod2) = go dom1 dom2 && go cod1 cod2
    go (Let _ ty1 v1 b1) (Let _ ty2 v2 b2) = go ty1 ty2 && go v1 v2 && go b1 b2
    go (Proj sn1 i1 s1) (Proj sn2 i2 s2) = sn1 == sn2 && i1 == i2 && go s1 s2
    go (NatLit n1) (NatLit n2) = n1 == n2
    go (StringLit s1) (StringLit s2) = s1 == s2
    go _ _ = False

------------------------------------------------------------------------
-- Level Equality (for isDefEqSimple)
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
-- Simple Definitional Equality (without proof irrelevance)
------------------------------------------------------------------------

-- Body comparison helper for binders
covering
isDefEqBodySimple : Expr -> (TCEnv -> Expr -> Expr -> TC Bool) ->
                    TCEnv -> Expr -> Expr -> TC Bool
isDefEqBodySimple binderType recur env b1 b2 =
  let localId = env.nextLocalId
      localVar : Expr = Local localId Anonymous
      env' = addLocalType localId binderType ({ nextLocalId := S localId } env)
      e1' : Expr = instantiate1 b1 localVar
      e2' : Expr = instantiate1 b2 localVar
  in recur env' e1' e2'

-- Eta expansion for lambdas
covering
tryEtaExpansionSimple : (TCEnv -> Expr -> Expr -> TC Bool) ->
                        TCEnv -> Expr -> Expr -> TC (Maybe Bool)
tryEtaExpansionSimple recurEq env t s = case t of
  Lam name bi ty body => case s of
    Lam _ _ _ _ => pure Nothing
    _ => do
      -- Eta-expand s: λx. s x
      -- With flat Expr, we need to lift s manually
      let sLifted = liftLooseBVars 0 1 s
      let sExpanded : Expr = Lam name bi ty (App sLifted (BVar 0))
      result <- recurEq env t sExpanded
      pure (Just result)
  _ => case s of
    Lam name bi ty body => do
      -- Eta-expand t: λx. t x
      let tLifted = liftLooseBVars 0 1 t
      let tExpanded : Expr = Lam name bi ty (App tLifted (BVar 0))
      result <- recurEq env tExpanded s
      pure (Just result)
    _ => pure Nothing

-- Simple definitional equality: WHNF + structural comparison
export covering
isDefEqSimple : TCEnv -> Expr -> Expr -> TC Bool
isDefEqSimple env e1 e2 =
  if exprEq e1 e2
    then pure True
    else do
      e1' <- whnf env e1
      e2' <- whnf env e2
      isDefEqWhnf e1' e2'
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
            (Just ty1, Just ty2) => isDefEqSimple env ty1 ty2
            _ => pure False
    isDefEqWhnf (App f1 a1) (App f2 a2) = do
      eqF <- isDefEqSimple env f1 f2
      if eqF then isDefEqSimple env a1 a2 else pure False
    isDefEqWhnf (Lam name1 _ ty1 body1) (Lam _ _ ty2 body2) = do
      eqTy <- isDefEqSimple env ty1 ty2
      if eqTy then isDefEqBodySimple ty1 isDefEqSimple env body1 body2 else pure False
    isDefEqWhnf (Pi name1 _ dom1 cod1) (Pi _ _ dom2 cod2) = do
      eqDom <- isDefEqSimple env dom1 dom2
      if eqDom then isDefEqBodySimple dom1 isDefEqSimple env cod1 cod2 else pure False
    isDefEqWhnf (Let name1 ty1 v1 b1) (Let _ ty2 v2 b2) = do
      eqTy <- isDefEqSimple env ty1 ty2
      eqV <- isDefEqSimple env v1 v2
      if eqTy && eqV then isDefEqBodySimple ty1 isDefEqSimple env b1 b2 else pure False
    isDefEqWhnf (Proj sn1 i1 s1) (Proj sn2 i2 s2) =
      if sn1 == sn2 && i1 == i2 then isDefEqSimple env s1 s2 else pure False
    isDefEqWhnf (NatLit n1) (NatLit n2) = pure (n1 == n2)
    isDefEqWhnf (StringLit s1) (StringLit s2) = pure (s1 == s2)
    isDefEqWhnf t s = do
      etaResult <- tryEtaExpansionSimple isDefEqSimple env t s
      case etaResult of
        Just b => pure b
        Nothing => pure False

------------------------------------------------------------------------
-- Type Inference
------------------------------------------------------------------------

showNameStructure : Name -> String
showNameStructure Anonymous = "Anonymous"
showNameStructure (Str s parent) = "Str \"" ++ s ++ "\" (" ++ showNameStructure parent ++ ")"
showNameStructure (Num n parent) = "Num " ++ show n ++ " (" ++ showNameStructure parent ++ ")"

mutual
  export covering
  inferTypeE : TCEnv -> Expr -> TC (TCEnv, Expr)
  inferTypeE env (Sort l) = pure (env, Sort (Succ l))
  inferTypeE env (Const name levels) =
    case (if env.quotInit then getQuotType name else Nothing) of
      Just (ty, params) =>
        if length params /= length levels
          then throw (WrongNumLevels (length params) (length levels) name)
          else pure (env, instantiateLevelParams params levels ty)
      Nothing => case lookupDecl name env of
        Nothing => throw (OtherError $ "unknown constant: " ++ show name ++
                        "\n  Name structure: " ++ showNameStructure name)
        Just decl => case declType decl of
          Nothing => throw (UnknownConst name)
          Just ty =>
            let params = declLevelParams decl in
            if length params /= length levels
              then throw (WrongNumLevels (length params) (length levels) name)
              else pure (env, instantiateLevelParams params levels ty)
  inferTypeE env (App f arg) = do
    (env1, fTy) <- inferTypeE env f
    (_, _, dom, cod) <- ensurePi env1 fTy
    (env2, argTy) <- inferTypeE env1 arg
    eq <- isDefEqSimple env2 argTy dom
    if eq
      then do
        let resultTy = instantiate1 cod arg
        resultTy' <- whnf env2 resultTy
        pure (env2, resultTy')
      else do
        argTy' <- normalizeType env2 argTy
        dom' <- normalizeType env2 dom
        eq' <- isDefEqSimple env2 argTy' dom'
        if eq'
          then do
            let resultTy = instantiate1 cod arg
            resultTy' <- whnf env2 resultTy
            pure (env2, resultTy')
          else throw (AppTypeMismatch dom' argTy')
  inferTypeE env (Lam name bi ty body) = do
    (env', _, resultTy) <- inferTypeOpenE env emptyCtx (Lam name bi ty body)
    pure (env', resultTy)
  inferTypeE env (Pi name bi dom cod) = do
    (env', _, resultTy) <- inferTypeOpenE env emptyCtx (Pi name bi dom cod)
    pure (env', resultTy)
  inferTypeE env (Let name ty val body) = do
    (env', _, resultTy) <- inferTypeOpenE env emptyCtx (Let name ty val body)
    pure (env', resultTy)
  inferTypeE env (Proj structName idx structExpr) = do
    (env', _, resultTy) <- inferTypeOpenE env emptyCtx (Proj structName idx structExpr)
    pure (env', resultTy)
  inferTypeE env (NatLit _) = pure (env, Const (Str "Nat" Anonymous) [])
  inferTypeE env (StringLit _) = pure (env, Const (Str "String" Anonymous) [])
  inferTypeE env (BVar i) =
    throw (OtherError $ "inferTypeE: unexpected BVar " ++ show i ++ " in closed expression")
  inferTypeE env (Local id name) =
    case lookupLocalType id env of
      Just ty => pure (env, ty)
      Nothing => throw (OtherError $ "inferTypeE: Local " ++ show id ++ " (" ++ show name ++ ") type not found")

  export covering
  inferType : TCEnv -> Expr -> TC Expr
  inferType env e = do
    (_, ty) <- inferTypeE env e
    pure ty

  export covering
  inferTypeOpenE : TCEnv -> LocalCtx -> Expr -> TC (TCEnv, LocalCtx, Expr)
  inferTypeOpenE env ctx (Sort l) = pure (env, ctx, Sort (Succ l))
  inferTypeOpenE env ctx (Const name levels) =
    case (if env.quotInit then getQuotType name else Nothing) of
      Just (ty, params) =>
        if length params /= length levels
          then throw (WrongNumLevels (length params) (length levels) name)
          else pure (env, ctx, instantiateLevelParams params levels ty)
      Nothing => case lookupDecl name env of
        Nothing => throw (OtherError $ "unknown constant (inferTypeOpenE): " ++ show name)
        Just decl => case declType decl of
          Nothing => throw (UnknownConst name)
          Just ty =>
            let params = declLevelParams decl in
            if length params /= length levels
              then throw (WrongNumLevels (length params) (length levels) name)
              else pure (env, ctx, instantiateLevelParams params levels ty)
  inferTypeOpenE env ctx (BVar i) =
    case lookupCtx i ctx of
      Just entry => pure (env, ctx, entry.type)
      Nothing => throw (OtherError $ "inferTypeOpenE: BVar " ++ show i ++ " out of scope")
  inferTypeOpenE env ctx (Local id name) =
    case lookupLocalType id env of
      Just ty => pure (env, ctx, ty)
      Nothing => throw (OtherError $ "inferTypeOpenE: Local " ++ show id ++ " (" ++ show name ++ ") type not found")
  inferTypeOpenE env ctx (App f arg) = do
    (env1, ctx1, fTy) <- inferTypeOpenE env ctx f
    (_, _, dom, cod) <- ensurePi env1 fTy
    let (env2, ctx2, argClosed) = closeWithPlaceholders env1 ctx1 arg
    let resultTy = instantiate1 cod argClosed
    resultTy' <- whnf env2 resultTy
    pure (env2, ctx2, resultTy')
  inferTypeOpenE env ctx (Lam name bi domExpr body) = do
    (env1, ctx1, domTy) <- inferTypeOpenE env ctx domExpr
    _ <- ensureSort env1 domTy
    let (env2, ctx2, domClosed) = closeWithPlaceholders env1 ctx1 domExpr
    let localId = env2.nextLocalId
        env3 = { nextLocalId := S localId } env2
        env4 = addLocalType localId domClosed env3
        ph : Expr = Local localId name
        newEntry = MkLocalEntry name domClosed Nothing (Just ph)
        ctx' : LocalCtx = newEntry :: ctx2
    (env5, ctx'', bodyTy) <- inferTypeOpenE env4 ctx' body
    let bodyCodOpen = replaceAllPlaceholdersWithBVars' ctx'' bodyTy
    pure (env5, ctx2, Pi name bi domClosed bodyCodOpen)
  inferTypeOpenE env ctx (Pi name bi domExpr codExpr) = do
    (env1, ctx1, domTy) <- inferTypeOpenE env ctx domExpr
    domLevel <- ensureSort env1 domTy
    let (env2, ctx2, domClosed) = closeWithPlaceholders env1 ctx1 domExpr
    let ctx' = extendCtx name domClosed ctx2
    (env3, _, codTy) <- inferTypeOpenE env2 ctx' codExpr
    codLevel <- ensureSort env3 codTy
    pure (env3, ctx2, Sort (simplify (IMax domLevel codLevel)))
  inferTypeOpenE env ctx (Let name tyExpr valExpr body) = do
    (env1, ctx1, tyTy) <- inferTypeOpenE env ctx tyExpr
    _ <- ensureSort env1 tyTy
    let (env2, ctx2, tyClosed) = closeWithPlaceholders env1 ctx1 tyExpr
    (env3, ctx3, valTy) <- inferTypeOpenE env2 ctx2 valExpr
    let (env4, ctx4, valClosed) = closeWithPlaceholders env3 ctx3 valExpr
    let valTyClosed = closeBVarsInType ctx4 valTy
    eq <- isDefEqSimple env4 tyClosed valTyClosed
    if eq
      then do
        let ctx' = extendCtxLet name tyClosed valClosed ctx4
        (env5, ctx'', bodyTy) <- inferTypeOpenE env4 ctx' body
        let bodyTy' = substLetPlaceholder ctx'' valClosed bodyTy
        pure (env5, ctx4, bodyTy')
      else do
        tyClosed' <- normalizeType env4 tyClosed
        valTy' <- normalizeType env4 valTy
        eq' <- isDefEqSimple env4 tyClosed' valTy'
        if eq'
          then do
            let ctx' = extendCtxLet name tyClosed valClosed ctx4
            (env5, ctx'', bodyTy) <- inferTypeOpenE env4 ctx' body
            let bodyTy' = substLetPlaceholder ctx'' valClosed bodyTy
            pure (env5, ctx4, bodyTy')
          else throw (LetTypeMismatch tyClosed' valTy')
  inferTypeOpenE env ctx (Proj structName idx structExpr) = do
    (env1, ctx1, structTy) <- inferTypeOpenE env ctx structExpr
    structTy' <- whnf env1 structTy
    let (head, params) = getAppSpine structTy'
    case getConstHead head of
      Nothing => throw (OtherError $ "projection: expected structure type for " ++ show structName)
      Just (tyName, typeLevels) =>
        if tyName /= structName
          then throw (OtherError $ "projection: type mismatch, expected " ++ show structName ++ " got " ++ show tyName)
          else
            -- Use getProjTypeWithStruct to handle dependent fields properly.
            -- Cast the open structExpr to ClosedExpr since the runtime representation is the same.
            let structClosed : ClosedExpr = believe_me structExpr
            in case getProjTypeWithStruct env1 structName idx typeLevels params structClosed of
              Nothing => throw (OtherError $ "projection: could not compute field type")
              Just fieldTy => pure (env1, ctx1, fieldTy)
  inferTypeOpenE env ctx (NatLit _) = pure (env, ctx, Const (Str "Nat" Anonymous) [])
  inferTypeOpenE env ctx (StringLit _) = pure (env, ctx, Const (Str "String" Anonymous) [])

  export covering
  inferTypeOpen : TCEnv -> LocalCtx -> Expr -> TC Expr
  inferTypeOpen env ctx e = do
    (_, _, ty) <- inferTypeOpenE env ctx e
    pure ty
