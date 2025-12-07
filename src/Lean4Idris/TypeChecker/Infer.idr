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
import System.File
import Debug.Trace

%default total

debugFile : File
debugFile = unsafePerformIO $ do
  Right f <- openFile "/tmp/typecheck_debug.txt" Append
    | Left _ => pure stdin
  pure f

debugPrint : String -> a -> a
debugPrint msg x = unsafePerformIO $ do
  Right () <- fPutStrLn debugFile (msg ++ "\n")
    | Left _ => pure x
  fflush debugFile
  pure x

------------------------------------------------------------------------
-- Ensure Sort/Pi
------------------------------------------------------------------------

mutual
  covering
  ensureSortOfApp : TCEnv -> ClosedExpr -> List ClosedExpr -> TC Level
  ensureSortOfApp env' ty [] = ensureSortWhnf env' ty
  ensureSortOfApp env' (Pi _ _ dom cod) (arg :: args) =
    ensureSortOfApp env' (instantiate1 (believe_me cod) arg) args
  ensureSortOfApp env' ty args = case ty of
    Sort l => pure l
    Pi _ _ _ cod => pure Zero
    Const name _ => case lookupDecl name env' of
      Just decl => case declType decl of
        Just dty => ensureSortOfApp env' dty args
        Nothing => throw (OtherError $ "ensureSort: const " ++ show name ++ " has no type")
      Nothing => throw (OtherError $ "ensureSort: unknown const " ++ show name)
    App _ _ => case getAppHead ty of
      Just (name, innerArgs) => case lookupDecl name env' of
        Just decl => case declType decl of
          Just dty => ensureSortOfApp env' dty (innerArgs ++ args)
          Nothing => throw (TypeExpected ty)
        Nothing => throw (TypeExpected ty)
      Nothing => throw (TypeExpected ty)
    _ => throw (OtherError $ "ensureSort: exhausted Pis")

  covering
  ensureSortWhnf : TCEnv -> ClosedExpr -> TC Level
  ensureSortWhnf env' (Sort l) = pure l
  ensureSortWhnf env' (Local id _) =
    case lookupLocalType id env' of
      Just ty => ensureSortWhnf env' ty
      Nothing => throw (OtherError $ "ensureSortWhnf: Local " ++ show id ++ " type not found")
  ensureSortWhnf env' expr@(App _ _) = case getAppHead expr of
    Just (name, args) => case lookupDecl name env' of
      Just decl => case declType decl of
        Just ty => ensureSortOfApp env' ty args
        Nothing => throw (TypeExpected expr)
      Nothing => throw (OtherError $ "ensureSort: stuck App with unknown head " ++ show name)
    Nothing => throw (TypeExpected expr)
  ensureSortWhnf _ (Pi _ _ _ _) = pure Zero
  ensureSortWhnf _ other = throw (TypeExpected other)

export covering
ensureSort : TCEnv -> ClosedExpr -> TC Level
ensureSort env e = do
  e' <- whnf env e
  ensureSortWhnf env e'

mutual
  covering
  ensurePiOfApp : TCEnv -> ClosedExpr -> List ClosedExpr -> TC (Name, BinderInfo, ClosedExpr, Expr 1)
  ensurePiOfApp env' ty [] = ensurePiWhnf env' ty
  ensurePiOfApp env' (Pi _ _ dom cod) (arg :: args) = do
    let resultTy = instantiate1 (believe_me cod) arg
    resultTy' <- whnf env' resultTy
    ensurePiOfApp env' resultTy' args
  ensurePiOfApp env' ty args =
    throw (OtherError $ "ensurePi: exhausted Pi types with " ++ show (length args) ++ " args remaining")

  covering
  ensurePiWhnf : TCEnv -> ClosedExpr -> TC (Name, BinderInfo, ClosedExpr, Expr 1)
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
      Just (name, args) => case lookupDecl name env' of
        Just decl => case declType decl of
          Just ty => ensurePiOfApp env' ty args
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
ensurePi : TCEnv -> ClosedExpr -> TC (Name, BinderInfo, ClosedExpr, Expr 1)
ensurePi env e = do
  e' <- whnf env e
  ensurePiWhnf env e'

export covering
buildPlaceholders : TCEnv -> LocalCtx n -> (TCEnv, LocalCtx n, Vect n ClosedExpr)
buildPlaceholders env ctx = buildWithDepth env ctx 0
  where
    buildWithDepth : TCEnv -> LocalCtx m -> Nat -> (TCEnv, LocalCtx m, Vect m ClosedExpr)
    buildWithDepth env [] _ = (env, [], [])
    buildWithDepth env (entry :: rest) depth = case entry.placeholder of
      Just ph =>
        let (env', rest', phs) = buildWithDepth env rest (S depth)
        in (env', entry :: rest', ph :: phs)
      Nothing =>
        let localId = env.nextLocalId
            env' = { nextLocalId := S localId } env
            env'' = addLocalType localId entry.type env'
            ph : ClosedExpr = Local localId entry.name
            entry' = { placeholder := Just ph } entry
            (env''', rest', phs) = buildWithDepth env'' rest (S depth)
        in (env''', entry' :: rest', ph :: phs)

export covering
closeWithPlaceholders : TCEnv -> LocalCtx n -> Expr n -> (TCEnv, LocalCtx n, ClosedExpr)
closeWithPlaceholders env ctx e =
  let (env', ctx', placeholders) = buildPlaceholders env ctx
  in (env', ctx', substAll placeholders e)

findLocalIdx : List LocalEntry -> Nat -> Nat -> Maybe Nat
findLocalIdx [] _ _ = Nothing
findLocalIdx (entry :: rest) targetId idx = case entry.placeholder of
  Just (Local id _) =>
    if id == targetId then Just idx else findLocalIdx rest targetId (S idx)
  _ => findLocalIdx rest targetId (S idx)

makeBVarFromNat : Nat -> ClosedExpr
makeBVarFromNat k = believe_me (BVar {n = S k} (natToFin k))
  where
    natToFin : (n : Nat) -> Fin (S n)
    natToFin Z = FZ
    natToFin (S m) = FS (natToFin m)

covering
replaceLocalsWithBVars : List LocalEntry -> Nat -> ClosedExpr -> ClosedExpr
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
              (believe_me (replaceLocalsWithBVars entries (S depth) (believe_me body)))
replaceLocalsWithBVars entries depth (Pi name bi dom cod) =
  Pi name bi (replaceLocalsWithBVars entries depth dom)
             (believe_me (replaceLocalsWithBVars entries (S depth) (believe_me cod)))
replaceLocalsWithBVars entries depth (Let name ty val body) =
  Let name (replaceLocalsWithBVars entries depth ty)
           (replaceLocalsWithBVars entries depth val)
           (believe_me (replaceLocalsWithBVars entries (S depth) (believe_me body)))
replaceLocalsWithBVars entries depth (Proj sn i s) =
  Proj sn i (replaceLocalsWithBVars entries depth s)
replaceLocalsWithBVars entries depth (NatLit k) = NatLit k
replaceLocalsWithBVars entries depth (StringLit s) = StringLit s

export covering
replaceAllPlaceholdersWithBVars' : List LocalEntry -> ClosedExpr -> ClosedExpr
replaceAllPlaceholdersWithBVars' entries e = replaceLocalsWithBVars entries 0 e

export covering
replaceAllPlaceholdersWithBVars : {n : Nat} -> LocalCtx n -> ClosedExpr -> Expr n
replaceAllPlaceholdersWithBVars {n} ctx e = believe_me (replaceLocalsWithBVars (toList ctx) 0 e)

------------------------------------------------------------------------
-- Structure/Projection Helpers
------------------------------------------------------------------------

export
getInductiveInfo : TCEnv -> Name -> Maybe InductiveInfo
getInductiveInfo env name = case lookupDecl name env of
  Just (IndDecl info _) => Just info
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

export covering
getProjType : TCEnv -> Name -> Nat -> List ClosedExpr -> Maybe ClosedExpr
getProjType env structName idx structParams = do
  indInfo <- getInductiveInfo env structName
  let numParams = indInfo.numParams
  ctor <- getStructCtor env structName
  getNthPiDomSubst (numParams + idx) structParams ctor.type

------------------------------------------------------------------------
-- Normalization
------------------------------------------------------------------------

covering
betaReduceN : {n : Nat} -> Expr n -> Maybe (Expr n)
betaReduceN (App (Lam _ _ _ body) arg) = Just (instantiate1N body arg)
betaReduceN _ = Nothing

getAppSpineN : {m : Nat} -> Expr m -> (Expr m, List (Expr m))
getAppSpineN e = go e []
  where
    go : Expr m -> List (Expr m) -> (Expr m, List (Expr m))
    go (App f x) args = go f (x :: args)
    go e args = (e, args)

mkAppN : {m : Nat} -> Expr m -> List (Expr m) -> Expr m
mkAppN f [] = f
mkAppN f (x :: xs) = mkAppN (App f x) xs

covering
unfoldConstN : TCEnv -> {n : Nat} -> Name -> List Level -> Maybe (Expr n)
unfoldConstN env name levels = do
  decl <- lookupDecl name env
  value <- getDeclValue decl
  let params = declLevelParams decl
  guard (length params == length levels)
  let instantiated = instantiateLevelParams params levels value
  Just (believe_me instantiated)

covering
tryDeltaOpenN : TCEnv -> {n : Nat} -> Expr n -> Maybe (Expr n)
tryDeltaOpenN env e =
  let (head, args) = getAppSpineN e
  in case head of
    Const name levels => do
      unfolded <- unfoldConstN env name levels
      Just (mkAppN unfolded args)
    _ => Nothing

tryProjReductionN : TCEnv -> {n : Nat} -> Expr n -> Maybe (Expr n)
tryProjReductionN env (Proj structName idx struct) = do
  let (head, args) = getAppSpineN struct
  case head of
    Const ctorName _ => do
      (_, _, numParams, numFields) <- getConstructorInfo env ctorName
      guard (idx < numFields)
      listNth args (numParams + idx)
    _ => Nothing
tryProjReductionN _ _ = Nothing

tryNatRecIota : {n : Nat} -> Expr n -> Maybe (Expr n)
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
normalizeTypeOpenWithEnv : TCEnv -> {n : Nat} -> Expr n -> TC (Expr n)
normalizeTypeOpenWithEnv env e = case betaReduceN e of
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
    Let name ty val body => normalizeTypeOpenWithEnv env (instantiate1N body val)
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
normalizeType : TCEnv -> ClosedExpr -> TC ClosedExpr
normalizeType env e = do
  e' <- whnf env e
  normalizeDeep e'
  where
    covering
    normalizeDeep : ClosedExpr -> TC ClosedExpr
    normalizeDeep (Pi name bi dom cod) = do
      dom' <- normalizeType env dom
      cod' <- normalizeTypeOpenWithEnv env cod
      pure (Pi name bi dom' cod')
    normalizeDeep (Lam name bi ty body) = do
      ty' <- normalizeType env ty
      body' <- normalizeTypeOpenWithEnv env body
      pure (Lam name bi ty' body')
    normalizeDeep (App f arg) = do
      f' <- normalizeType env f
      arg' <- normalizeType env arg
      pure (App f' arg')
    normalizeDeep (Let name ty val body) = do
      ty' <- normalizeType env ty
      val' <- normalizeType env val
      body' <- normalizeTypeOpenWithEnv env body
      pure (Let name ty' val' body')
    normalizeDeep (Proj n i e) = do
      e' <- normalizeType env e
      pure (Proj n i e')
    normalizeDeep (Sort l) = pure (Sort (simplify l))
    normalizeDeep e = pure e

------------------------------------------------------------------------
-- Alpha Equivalence
------------------------------------------------------------------------

export covering
alphaEq : ClosedExpr -> ClosedExpr -> Bool
alphaEq = go
  where
    covering
    go : ClosedExpr -> ClosedExpr -> Bool
    go (Sort l1) (Sort l2) = simplify l1 == simplify l2
    go (Const n1 ls1) (Const n2 ls2) = n1 == n2 && map simplify ls1 == map simplify ls2
    go (BVar i1) (BVar i2) = i1 == i2
    go (Local id1 _) (Local id2 _) = id1 == id2
    go (App f1 a1) (App f2 a2) = go f1 f2 && go a1 a2
    go (Lam _ _ ty1 body1) (Lam _ _ ty2 body2) =
      go ty1 ty2 && go (believe_me body1) (believe_me body2)
    go (Pi _ _ dom1 cod1) (Pi _ _ dom2 cod2) =
      go dom1 dom2 && go (believe_me cod1) (believe_me cod2)
    go (Let _ ty1 v1 b1) (Let _ ty2 v2 b2) =
      go ty1 ty2 && go v1 v2 && go (believe_me b1) (believe_me b2)
    go (Proj sn1 i1 s1) (Proj sn2 i2 s2) = sn1 == sn2 && i1 == i2 && go s1 s2
    go (NatLit n1) (NatLit n2) = n1 == n2
    go (StringLit s1) (StringLit s2) = s1 == s2
    go _ _ = False

------------------------------------------------------------------------
-- Type Inference
------------------------------------------------------------------------

showNameStructure : Name -> String
showNameStructure Anonymous = "Anonymous"
showNameStructure (Str s parent) = "Str \"" ++ s ++ "\" (" ++ showNameStructure parent ++ ")"
showNameStructure (Num n parent) = "Num " ++ show n ++ " (" ++ showNameStructure parent ++ ")"

mutual
  export covering
  inferTypeE : TCEnv -> ClosedExpr -> TC (TCEnv, ClosedExpr)
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
    -- Lazy normalization: try WHNF comparison first before full normalization
    argTyWhnf <- whnf env2 argTy
    domWhnf <- whnf env2 dom
    if alphaEq argTyWhnf domWhnf
      then do
        let resultTy = instantiate1 (believe_me cod) arg
        resultTy' <- whnf env2 resultTy
        pure (env2, resultTy')
      else do
        -- WHNF comparison failed, try full normalization
        argTy' <- normalizeType env2 argTyWhnf
        dom' <- normalizeType env2 domWhnf
        if alphaEq argTy' dom'
          then do
            let resultTy = instantiate1 (believe_me cod) arg
            resultTy' <- whnf env2 resultTy
            pure (env2, resultTy')
          else debugPrint ("inferTypeE App mismatch:\n  f=" ++ show f ++ "\n  arg=" ++ show arg ++ "\n  fTy=" ++ show fTy ++ "\n  dom (before whnf)=" ++ show dom ++ "\n  domWhnf=" ++ show domWhnf ++ "\n  dom' (after normalize)=" ++ show dom' ++ "\n  argTy (before whnf)=" ++ show argTy ++ "\n  argTyWhnf=" ++ show argTyWhnf ++ "\n  argTy' (after normalize)=" ++ show argTy') $
               throw (AppTypeMismatch dom' argTy')
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
    throw (OtherError $ "inferTypeE: unexpected BVar " ++ show (finToNat i) ++ " in closed expression")
  inferTypeE env (Local id name) =
    case lookupLocalType id env of
      Just ty => pure (env, ty)
      Nothing => throw (OtherError $ "inferTypeE: Local " ++ show id ++ " (" ++ show name ++ ") type not found")

  export covering
  inferType : TCEnv -> ClosedExpr -> TC ClosedExpr
  inferType env e = do
    (_, ty) <- inferTypeE env e
    pure ty

  export covering
  inferTypeOpenE : TCEnv -> LocalCtx n -> Expr n -> TC (TCEnv, LocalCtx n, ClosedExpr)
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
  inferTypeOpenE env ctx (BVar i) = pure (env, ctx, (lookupCtx i ctx).type)
  inferTypeOpenE env ctx (Local id name) =
    case lookupLocalType id env of
      Just ty => pure (env, ctx, ty)
      Nothing => throw (OtherError $ "inferTypeOpenE: Local " ++ show id ++ " (" ++ show name ++ ") type not found")
  inferTypeOpenE env ctx (App f arg) = do
    (env1, ctx1, fTy) <- inferTypeOpenE env ctx f
    (_, _, dom, cod) <- ensurePi env1 fTy
    let (env2, ctx2, argClosed) = closeWithPlaceholders env1 ctx1 arg
    let resultTy = instantiate1 (believe_me cod) argClosed
    resultTy' <- whnf env2 resultTy
    pure (env2, ctx2, resultTy')
  inferTypeOpenE env ctx (Lam name bi domExpr body) = do
    (env1, ctx1, domTy) <- inferTypeOpenE env ctx domExpr
    _ <- ensureSort env1 domTy
    let (env2, ctx2, domClosed) = closeWithPlaceholders env1 ctx1 domExpr
    let localId = env2.nextLocalId
        env3 = { nextLocalId := S localId } env2
        env4 = addLocalType localId domClosed env3
        ph : ClosedExpr = Local localId name
        newEntry = MkLocalEntry name domClosed Nothing (Just ph)
        ctx' : LocalCtx (S n) = newEntry :: ctx2
    (env5, ctx'', bodyTy) <- inferTypeOpenE env4 ctx' body
    let bodyCodOpen = replaceAllPlaceholdersWithBVars' (toList ctx'') bodyTy
    let resultCod : Expr 1 = believe_me bodyCodOpen
    pure (env5, ctx2, Pi name bi domClosed resultCod)
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
    let (env3, ctx3, valClosed) = closeWithPlaceholders env2 ctx2 valExpr
    (env4, ctx4, valTy) <- inferTypeOpenE env3 ctx3 valExpr
    -- Lazy normalization: try WHNF comparison first
    tyClosedWhnf <- whnf env4 tyClosed
    valTyWhnf <- whnf env4 valTy
    let tyWithBVarsWhnf = replaceAllPlaceholdersWithBVars' (toList ctx4) tyClosedWhnf
    if alphaEq tyWithBVarsWhnf valTyWhnf
      then do
        let ctx' = extendCtxLet name tyClosed valClosed ctx4
        (env5, _, bodyTy) <- inferTypeOpenE env4 ctx' body
        pure (env5, ctx4, bodyTy)
      else do
        -- WHNF comparison failed, try full normalization
        tyClosed' <- normalizeType env4 tyClosedWhnf
        valTy' <- normalizeType env4 valTyWhnf
        let tyWithBVars = replaceAllPlaceholdersWithBVars' (toList ctx4) tyClosed'
        if alphaEq tyWithBVars valTy'
          then do
            let ctx' = extendCtxLet name tyClosed valClosed ctx4
            (env5, _, bodyTy) <- inferTypeOpenE env4 ctx' body
            pure (env5, ctx4, bodyTy)
          else throw (LetTypeMismatch tyClosed' valTy')
  inferTypeOpenE env ctx (Proj structName idx structExpr) = do
    (env1, ctx1, structTy) <- inferTypeOpenE env ctx structExpr
    structTy' <- whnf env1 structTy
    let (head, params) = getAppSpine structTy'
    case getConstHead head of
      Nothing => throw (OtherError $ "projection: expected structure type for " ++ show structName)
      Just (tyName, _) =>
        if tyName /= structName
          then throw (OtherError $ "projection: type mismatch, expected " ++ show structName ++ " got " ++ show tyName)
          else case getProjType env1 structName idx params of
            Nothing => throw (OtherError $ "projection: could not compute field type")
            Just fieldTy => pure (env1, ctx1, fieldTy)
  inferTypeOpenE env ctx (NatLit _) = pure (env, ctx, Const (Str "Nat" Anonymous) [])
  inferTypeOpenE env ctx (StringLit _) = pure (env, ctx, Const (Str "String" Anonymous) [])

  export covering
  inferTypeOpen : TCEnv -> LocalCtx n -> Expr n -> TC ClosedExpr
  inferTypeOpen env ctx e = do
    (_, _, ty) <- inferTypeOpenE env ctx e
    pure ty
