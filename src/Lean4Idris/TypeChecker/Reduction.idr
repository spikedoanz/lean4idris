module Lean4Idris.TypeChecker.Reduction

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Subst
import Lean4Idris.TypeChecker.Monad
import Data.List

%default total

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

export
getAppSpine : ClosedExpr -> (ClosedExpr, List ClosedExpr)
getAppSpine e = go e []
  where
    go : ClosedExpr -> List ClosedExpr -> (ClosedExpr, List ClosedExpr)
    go (App f x) args = go f (x :: args)
    go head args = (head, args)

export
listNth : List a -> Nat -> Maybe a
listNth [] _ = Nothing
listNth (x :: _) Z = Just x
listNth (_ :: xs) (S n) = listNth xs n

export
listDrop : Nat -> List a -> List a
listDrop Z xs = xs
listDrop (S n) [] = []
listDrop (S n) (_ :: xs) = listDrop n xs

export
listTake : Nat -> List a -> List a
listTake Z _ = []
listTake (S n) [] = []
listTake (S n) (x :: xs) = x :: listTake n xs

------------------------------------------------------------------------
-- Delta Reduction
------------------------------------------------------------------------

export
getDeclValue : Declaration -> Maybe ClosedExpr
getDeclValue (DefDecl _ _ value hint _ _) = case hint of
  Opaq => Nothing
  _    => Just value
getDeclValue (ThmDecl _ _ value _) = Just value
getDeclValue _ = Nothing

export covering
unfoldConst : TCEnv -> Name -> List Level -> Maybe ClosedExpr
unfoldConst env name levels = do
  decl <- lookupDecl name env
  value <- getDeclValue decl
  let params = declLevelParams decl
  guard (length params == length levels)
  Just (instantiateLevelParams params levels value)

export
getAppConst : ClosedExpr -> Maybe (Name, List Level, List ClosedExpr)
getAppConst e = go e []
  where
    go : ClosedExpr -> List ClosedExpr -> Maybe (Name, List Level, List ClosedExpr)
    go (App f x) args = go f (x :: args)
    go (Const name levels) args = Just (name, levels, args)
    go _ _ = Nothing

export covering
unfoldHead : TCEnv -> ClosedExpr -> Maybe ClosedExpr
unfoldHead env e =
  case getAppConst e of
    Just (name, levels, args) =>
      case unfoldConst env name levels of
        Just value => Just (mkApp value args)
        Nothing => Nothing
    Nothing => case e of
      Const name levels => unfoldConst env name levels
      _ => Nothing

------------------------------------------------------------------------
-- Iota Reduction
------------------------------------------------------------------------

export
getRecursorInfo : TCEnv -> Name -> Maybe RecursorInfo
getRecursorInfo env name = case lookupDecl name env of
  Just (RecDecl info _) => Just info
  _ => Nothing

export
getRecursorInfoWithLevels : TCEnv -> Name -> Maybe (RecursorInfo, List Name)
getRecursorInfoWithLevels env name = case lookupDecl name env of
  Just (RecDecl info params) => Just (info, params)
  _ => Nothing

export
getConstructorInfo : TCEnv -> Name -> Maybe (Name, Nat, Nat, Nat)
getConstructorInfo env name = case lookupDecl name env of
  Just (CtorDecl _ _ indName ctorIdx numParams numFields _) => Just (indName, ctorIdx, numParams, numFields)
  _ => Nothing

findRecRule : List RecursorRule -> Name -> Maybe RecursorRule
findRecRule [] _ = Nothing
findRecRule (rule :: rules) ctorName =
  if rule.ctorName == ctorName then Just rule else findRecRule rules ctorName

getMajorIdx : RecursorInfo -> Nat
getMajorIdx info = info.numParams + info.numMotives + info.numMinors + info.numIndices

export
iterWhnfStep : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Nat -> ClosedExpr
iterWhnfStep step m 0 = m
iterWhnfStep step m (S fuel) = case step m of
  Just m' => iterWhnfStep step m' fuel
  Nothing => m

export
getConstHead : ClosedExpr -> Maybe (Name, List Level)
getConstHead (Const n ls) = Just (n, ls)
getConstHead _ = Nothing

export
substArgs : {n : Nat} -> List (Expr n) -> Expr n -> Expr n
substArgs [] ty = ty
substArgs {n} (arg :: args) (Pi _ _ _ cod) = substArgs args (subst0 cod arg)
substArgs _ ty = ty

export covering
getNthPiDomSubst : {n : Nat} -> Nat -> List (Expr n) -> Expr n -> Maybe (Expr n)
getNthPiDomSubst Z _ (Pi _ _ dom _) = Just dom
getNthPiDomSubst (S k) [] (Pi _ _ _ cod) = getNthPiDomSubst k [] (believe_me cod)
getNthPiDomSubst (S k) (arg :: args) (Pi _ _ _ cod) =
  let result = instantiate1 (believe_me cod) (believe_me arg) in
  getNthPiDomSubst k args (believe_me result)
getNthPiDomSubst _ _ _ = Nothing

export covering
tryIotaReduction : TCEnv -> ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryIotaReduction env e whnfStep = do
  let (head, args) = getAppSpine e
  (recName, recLevels) <- getConstHead head
  (recInfo, recLevelParams) <- getRecursorInfoWithLevels env recName
  let majorIdx = getMajorIdx recInfo
  major <- listNth args majorIdx
  let major' = iterWhnfStep whnfStep major 100
  let (majorHead, majorArgs) = getAppSpine major'
  (ctorName, _) <- getConstHead majorHead
  (_, _, ctorNumParams, ctorNumFields) <- getConstructorInfo env ctorName
  rule <- findRecRule recInfo.rules ctorName
  guard (length majorArgs >= ctorNumParams + ctorNumFields)
  let firstIndexIdx = recInfo.numParams + recInfo.numMotives + recInfo.numMinors
  let rhs = instantiateLevelParams recLevelParams recLevels rule.rhs
  let rhsWithParamsMotivesMinors = mkApp rhs (listTake firstIndexIdx args)
  let ctorFields = listDrop ctorNumParams majorArgs
  let rhsWithFields = mkApp rhsWithParamsMotivesMinors ctorFields
  let remainingArgs = listDrop (majorIdx + 1) args
  pure (mkApp rhsWithFields remainingArgs)

------------------------------------------------------------------------
-- Projection Reduction
------------------------------------------------------------------------

export
tryProjReduction : TCEnv -> ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryProjReduction env (Proj structName idx struct) whnfStep = do
  let struct' = iterWhnfStep whnfStep struct 100
  let (head, args) = getAppSpine struct'
  (ctorName, _) <- getConstHead head
  (_, _, numParams, numFields) <- getConstructorInfo env ctorName
  guard (idx < numFields)
  listNth args (numParams + idx)
tryProjReduction _ _ _ = Nothing

------------------------------------------------------------------------
-- Quotient Reduction
------------------------------------------------------------------------

export quotName : Name
quotName = Str "Quot" Anonymous

export quotMkName : Name
quotMkName = Str "mk" (Str "Quot" Anonymous)

export quotLiftName : Name
quotLiftName = Str "lift" (Str "Quot" Anonymous)

export quotIndName : Name
quotIndName = Str "ind" (Str "Quot" Anonymous)

mkQBVar : Nat -> ClosedExpr
mkQBVar n = believe_me (the (Expr 1) (BVar (believe_me n)))

mkQPi : Name -> BinderInfo -> ClosedExpr -> ClosedExpr -> ClosedExpr
mkQPi name bi ty body = believe_me (the (Expr 0) (Pi name bi (believe_me ty) (believe_me body)))

export
getQuotType : Name -> Maybe (ClosedExpr, List Name)
getQuotType name =
  let uName = Str "u" Anonymous
      vName = Str "v" Anonymous
      alphaName = Str "α" Anonymous
      rName = Str "r" Anonymous
      betaName = Str "β" Anonymous
      fName = Str "f" Anonymous
      hName = Str "h" Anonymous
      qName = Str "q" Anonymous
  in if name == quotName then
    let u = Param uName
        sortU = Sort u
        prop = Sort Zero
        rTy = mkQPi (Str "_" Anonymous) Default (mkQBVar 0) (mkQPi (Str "_" Anonymous) Default (mkQBVar 1) prop)
        quotTy = mkQPi alphaName Implicit sortU (mkQPi rName Default rTy sortU)
    in Just (quotTy, [uName])
  else if name == quotMkName then
    let u = Param uName
        sortU = Sort u
        prop = Sort Zero
        rTy = mkQPi (Str "_" Anonymous) Default (mkQBVar 0) (mkQPi (Str "_" Anonymous) Default (mkQBVar 1) prop)
        quotR = App (App (Const quotName [u]) (mkQBVar 2)) (mkQBVar 1)
        mkTy = mkQPi alphaName Implicit sortU
                 (mkQPi rName Implicit rTy
                   (mkQPi (Str "_" Anonymous) Default (mkQBVar 1) quotR))
    in Just (mkTy, [uName])
  else if name == quotLiftName then
    let u = Param uName
        v = Param vName
        sortU = Sort u
        sortV = Sort v
        prop = Sort Zero
        rTy = mkQPi (Str "_" Anonymous) Default (mkQBVar 0) (mkQPi (Str "_" Anonymous) Default (mkQBVar 1) prop)
        liftTy = mkQPi alphaName Implicit sortU
                   (mkQPi rName Implicit rTy
                     (mkQPi betaName Implicit sortV
                       (mkQPi fName Default (mkQPi (Str "_" Anonymous) Default (mkQBVar 2) (mkQBVar 1))
                         (mkQPi hName Default
                           (mkQPi (Str "a" Anonymous) Default (mkQBVar 4)
                             (mkQPi (Str "b" Anonymous) Default (mkQBVar 5)
                               (mkQPi (Str "_" Anonymous) Default
                                 (App (App (mkQBVar 4) (mkQBVar 1)) (mkQBVar 0))
                                 (App (App (App (Const (Str "Eq" Anonymous) [v]) (mkQBVar 4))
                                           (App (mkQBVar 3) (mkQBVar 2)))
                                      (App (mkQBVar 3) (mkQBVar 1))))))
                           (mkQPi (Str "_" Anonymous) Default
                             (App (App (Const quotName [u]) (mkQBVar 5)) (mkQBVar 4))
                             (mkQBVar 3))))))
    in Just (liftTy, [uName, vName])
  else if name == quotIndName then
    let u = Param uName
        sortU = Sort u
        prop = Sort Zero
        rTy = mkQPi (Str "_" Anonymous) Default (mkQBVar 0) (mkQPi (Str "_" Anonymous) Default (mkQBVar 1) prop)
        betaTy = mkQPi (Str "_" Anonymous) Default (App (App (Const quotName [u]) (mkQBVar 1)) (mkQBVar 0)) prop
        hTy = mkQPi (Str "a" Anonymous) Default (mkQBVar 3)
                (App (mkQBVar 1) (App (App (App (Const quotMkName [u]) (mkQBVar 4)) (mkQBVar 3)) (mkQBVar 0)))
        indTy = mkQPi alphaName Implicit sortU
                  (mkQPi rName Implicit rTy
                    (mkQPi betaName Implicit betaTy
                      (mkQPi hName Default hTy
                        (mkQPi qName Default (App (App (Const quotName [u]) (mkQBVar 4)) (mkQBVar 3))
                          (App (mkQBVar 2) (mkQBVar 0))))))
    in Just (indTy, [uName])
  else Nothing

export
tryQuotReduction : ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryQuotReduction e whnfStep = do
  let (head, args) = getAppSpine e
  (fnName, _) <- getConstHead head
  (mkPos, argPos) <- the (Maybe (Nat, Nat)) $
    if fnName == quotLiftName then Just (5, 3)
    else if fnName == quotIndName then Just (4, 3)
    else Nothing
  guard (List.length args > mkPos)
  mkArg <- listNth args mkPos
  let mkArg' = iterWhnfStep whnfStep mkArg 100
  let (mkHead, mkArgs) = getAppSpine mkArg'
  (mkName, _) <- getConstHead mkHead
  guard (mkName == quotMkName && List.length mkArgs == 3)
  a <- listNth mkArgs 2
  fOrH <- listNth args argPos
  let result = App fOrH a
  let remainingArgs = listDrop (mkPos + 1) args
  pure (mkApp result remainingArgs)

------------------------------------------------------------------------
-- Let Placeholder Unfolding
------------------------------------------------------------------------

||| Try to unfold a let-bound placeholder constant to its value
||| This is similar to lean4lean's whnfFVar which unfolds let-bound free variables
export
tryUnfoldLetPlaceholder : TCEnv -> ClosedExpr -> Maybe ClosedExpr
tryUnfoldLetPlaceholder env e =
  let (head, args) = getAppSpine e
  in case head of
    Const name _ => case lookupLetValue name env of
      Just val => Just (mkApp val args)
      Nothing => Nothing
    _ => Nothing

------------------------------------------------------------------------
-- WHNF
------------------------------------------------------------------------

export covering
whnf : TCEnv -> ClosedExpr -> TC ClosedExpr
whnf env e = do
  useFuel
  pure (whnfPure 20 e)
  where
    whnfStepCore : ClosedExpr -> Maybe ClosedExpr
    whnfStepCore (App (Lam _ _ _ body) arg) = Just (instantiate1 (believe_me body) arg)
    whnfStepCore (App f arg) = case whnfStepCore f of
      Just f' => Just (App f' arg)
      Nothing => Nothing
    whnfStepCore (Let _ _ val body) = Just (instantiate1 (believe_me body) val)
    whnfStepCore _ = Nothing

    whnfStepWithDelta : ClosedExpr -> Maybe ClosedExpr
    whnfStepWithDelta e = case whnfStepCore e of
      Just e' => Just e'
      Nothing => case tryUnfoldLetPlaceholder env e of
        Just e' => Just e'
        Nothing => unfoldHead env e

    reduceAppHead : ClosedExpr -> Maybe ClosedExpr
    reduceAppHead (App f arg) = case reduceAppHead f of
      Just f' => Just (App f' arg)
      Nothing => case tryProjReduction env f whnfStepWithDelta of
        Just f' => Just (App f' arg)
        Nothing => case tryUnfoldLetPlaceholder env f of
          Just f' => Just (App f' arg)
          Nothing => case unfoldHead env f of
            Just f' => Just (App f' arg)
            Nothing => Nothing
    reduceAppHead _ = Nothing

    whnfPure : Nat -> ClosedExpr -> ClosedExpr
    whnfPure 0 e = e
    whnfPure (S k) e = case whnfStepCore e of
      Just e' => whnfPure k e'
      Nothing => case tryUnfoldLetPlaceholder env e of
        Just e' => whnfPure k e'
        Nothing => case reduceAppHead e of
          Just e' => whnfPure k e'
          Nothing => case tryProjReduction env e whnfStepWithDelta of
            Just e' => whnfPure k e'
            Nothing => case (if env.quotInit then tryQuotReduction e whnfStepWithDelta else Nothing) of
              Just e' => whnfPure k e'
              Nothing => case tryIotaReduction env e whnfStepWithDelta of
                Just e' => whnfPure k e'
                Nothing => case unfoldHead env e of
                  Just e' => whnfPure k e'
                  Nothing => e

export covering
whnfCore : ClosedExpr -> TC ClosedExpr
whnfCore e = pure (whnfCorePure 1000 e)
  where
    whnfStepCore : ClosedExpr -> Maybe ClosedExpr
    whnfStepCore (App (Lam _ _ _ body) arg) = Just (instantiate1 (believe_me body) arg)
    whnfStepCore (Let _ _ val body) = Just (instantiate1 (believe_me body) val)
    whnfStepCore _ = Nothing

    whnfCorePure : Nat -> ClosedExpr -> ClosedExpr
    whnfCorePure 0 e = e
    whnfCorePure (S k) e = case whnfStepCore e of
      Nothing => e
      Just e' => whnfCorePure k e'

export
getAppHead : ClosedExpr -> Maybe (Name, List ClosedExpr)
getAppHead expr = go expr []
  where
    go : ClosedExpr -> List ClosedExpr -> Maybe (Name, List ClosedExpr)
    go (App f' arg) args = go f' (arg :: args)
    go (Const name _) args = Just (name, args)
    go _ _ = Nothing
