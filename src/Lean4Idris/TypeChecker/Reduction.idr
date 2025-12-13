module Lean4Idris.TypeChecker.Reduction

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Subst
import Lean4Idris.TypeChecker.Monad
import Lean4Idris.TypeChecker.NativeReduction
import Lean4Idris.Pretty
import Data.List
import Debug.Trace

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

debugUnfold : Bool
debugUnfold = False

covering
unfoldHead : TCEnv -> ClosedExpr -> Maybe ClosedExpr
unfoldHead env e =
  case getAppConst e of
    Just (name, levels, args) =>
      case unfoldConst env name levels of
        Just value =>
          let _ = if debugUnfold && show name == "UInt64.size" then trace "UNFOLD: \{show name} -> ..." () else ()
          in Just (mkApp value args)
        Nothing => Nothing
    Nothing => case e of
      Const name levels =>
        let result = unfoldConst env name levels
            _ = if debugUnfold && show name == "UInt64.size" then trace "UNFOLD-CONST: \{show name}" () else ()
        in result
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

export covering
getNthPiDomSubst : Nat -> List Expr -> Expr -> Maybe Expr
getNthPiDomSubst Z _ (Pi _ _ dom _) = Just dom
getNthPiDomSubst (S k) [] (Pi _ _ _ cod) = getNthPiDomSubst k [] cod
getNthPiDomSubst (S k) (arg :: args) (Pi _ _ _ cod) =
  let result = instantiate1 cod arg in
  getNthPiDomSubst k args result
getNthPiDomSubst _ _ _ = Nothing

-- Debug flag: set to True to enable tracing
debugIota : Bool
debugIota = False

-- Debug flag for whnf steps
debugWhnf : Bool
debugWhnf = False

-- Names for Nat constructors (used in iota reduction for NatLit handling)
iotaNatName : Name
iotaNatName = Str "Nat" Anonymous

iotaNatZeroName : Name
iotaNatZeroName = Str "zero" iotaNatName

iotaNatSuccName : Name
iotaNatSuccName = Str "succ" iotaNatName

-- Helper: extract constructor info from major premise head
-- Handles NatLit as Nat.zero/Nat.succ
-- Returns: (ctorName, ctorLevels, ctorArgs for fields only)
getCtorFromMajor : ClosedExpr -> List ClosedExpr -> Maybe (Name, List Level, List ClosedExpr)
getCtorFromMajor (NatLit Z) args = Just (iotaNatZeroName, [], [])
getCtorFromMajor (NatLit (S n)) args = Just (iotaNatSuccName, [], [NatLit n])
getCtorFromMajor (Const name levels) args = Just (name, levels, args)
getCtorFromMajor _ _ = Nothing

-- Name for Eq.refl constructor (for K-like reduction)
eqReflName : Name
eqReflName = Str "refl" (Str "Eq" Anonymous)

------------------------------------------------------------------------
-- Structure Eta Expansion for Iota Reduction
------------------------------------------------------------------------

-- Get the inductive name from a recursor name (e.g., Prod.rec -> Prod)
getInductiveFromRecursor : Name -> Name
getInductiveFromRecursor (Str "rec" parent) = parent
getInductiveFromRecursor (Str "recOn" parent) = parent
getInductiveFromRecursor (Str "casesOn" parent) = parent
getInductiveFromRecursor n = n  -- Fallback

-- Get the result sort of a type (skip past all Pi binders)
-- Since we're traversing a well-formed type, this always terminates
covering
getResultSort : Expr -> Maybe Level
getResultSort (Pi name bi dom cod) = getResultSort cod
getResultSort (Sort l) = Just l
getResultSort _ = Nothing

-- Check if the result sort is Prop (Sort Zero)
covering
isPropResult : ClosedExpr -> Bool
isPropResult ty = case getResultSort ty of
  Just l => simplify l == Zero
  Nothing => False

-- Check if an inductive is structure-like (single constructor, not recursive, NOT Prop)
-- Returns: (ctorName, numParams, numFields, levelParams)
-- Important: We skip Prop types since their proofs should be handled by K-like reduction
-- or proof irrelevance, not structure eta expansion
covering
getStructureLikeInfo : TCEnv -> Name -> Maybe (Name, Nat, Nat, List Name)
getStructureLikeInfo env indName = case lookupDecl indName env of
  Just (IndDecl info levelParams) =>
    -- Skip Prop types - they should use K-like reduction or proof irrelevance
    if isPropResult info.type
      then Nothing
      else case info.constructors of
        [ctor] =>
          -- Single constructor - this is structure-like
          case lookupDecl ctor.name env of
            Just (CtorDecl _ _ _ _ numParams numFields _) =>
              Just (ctor.name, numParams, numFields, levelParams)
            _ => Nothing
        _ => Nothing  -- Multiple or zero constructors
  _ => Nothing

-- Check if expression head is already a constructor
isConstructorHead : TCEnv -> ClosedExpr -> Bool
isConstructorHead env (Const name _) = case getConstructorInfo env name of
  Just _ => True
  Nothing => False
isConstructorHead _ (NatLit _) = True
isConstructorHead _ _ = False

-- Try to eta-expand a major premise that is of structure-like type
-- Takes the recursor's levels and first numParams args to construct the eta-expanded form
-- Returns: (ctorName, ctorLevels, projections)
-- Only expands if major is NOT already a constructor application
-- Note: Constructor levels are taken from the inductive's level params, using recursor levels
covering
tryStructEtaExpand : TCEnv -> Name -> List Level -> List ClosedExpr -> ClosedExpr -> Maybe (Name, List Level, List ClosedExpr)
tryStructEtaExpand env inductName recLevels typeParams major =
  let (majorHead, _) = getAppSpine major
  in if isConstructorHead env majorHead
     then Nothing  -- Already a constructor, don't eta-expand
     else
       -- Check if inductName is structure-like
       case getStructureLikeInfo env inductName of
         Nothing => Nothing
         Just (ctorName, numParams, numFields, ctorLevelParams) =>
           -- major is not a constructor app, so eta-expand it
           -- Build just the projections: (Proj inductName 0 major) (Proj inductName 1 major) ...
           -- The constructor levels are the first (length ctorLevelParams) levels from recLevels
           -- Note: We only return the field projections, NOT the type params - those are handled
           -- separately by tryIotaReduction when building rhsWithParamsMotivesMinors
           let ctorLevels = listTake (length ctorLevelParams) recLevels
               projections = buildProjs inductName 0 numFields
           in Just (ctorName, ctorLevels, projections)
  where
    buildProjs : Name -> Nat -> Nat -> List ClosedExpr
    buildProjs _ _ Z = []
    buildProjs structName i (S remaining) = Proj structName i major :: buildProjs structName (S i) remaining

-- Try K-like reduction for Eq.rec when a == b in Eq α a b
-- This allows reduction even when the proof isn't a visible Eq.refl constructor
tryKLikeReduction : RecursorInfo -> List Level -> List ClosedExpr ->
                   (ClosedExpr -> Maybe ClosedExpr) -> Maybe (Name, List Level, List ClosedExpr)
tryKLikeReduction recInfo recLevels args whnfStep =
  if not recInfo.isK then Nothing
  else if length args <= recInfo.numParams + recInfo.numMotives + recInfo.numMinors + recInfo.numIndices then Nothing
  else case listNth args 0 of
    Nothing => Nothing
    Just alpha => case listNth args 1 of
      Nothing => Nothing
      Just a => case listNth args (recInfo.numParams + recInfo.numMotives + recInfo.numMinors) of
        Nothing => Nothing
        Just b =>
          let a' = iterWhnfStep whnfStep a 100
              b' = iterWhnfStep whnfStep b 100
          in if exprEq a' b'
             then Just (eqReflName, recLevels, [alpha, a])
             else Nothing

export covering
tryIotaReduction : TCEnv -> ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryIotaReduction env e whnfStep = do
  let (head, args) = getAppSpine e
  (recName, recLevels) <- getConstHead head
  (recInfo, recLevelParams) <- getRecursorInfoWithLevels env recName
  let majorIdx = getMajorIdx recInfo
  let _ = if debugIota then trace "IOTA: recursor=\{show recName} majorIdx=\{show majorIdx} numArgs=\{show (length args)}" () else ()
  major <- listNth args majorIdx
  let major' = iterWhnfStep whnfStep major 100
  let _ = if debugIota then trace "IOTA: major after whnf=\{ppClosedExpr major'}" () else ()
  let (majorHead, majorArgs) = getAppSpine major'
  let _ = if debugIota then trace "IOTA: majorHead=\{ppClosedExpr majorHead} majorArgs=\{show (length majorArgs)}" () else ()
  -- First try direct constructor, then K-like reduction for Eq.rec, then structure eta expansion
  -- Note: We do NOT synthesize Acc.intro for Acc.rec - if the major premise doesn't
  -- reduce to Acc.intro, we leave the term unreduced and let proof irrelevance
  -- handle it in DefEq. This matches lean4lean's approach.
  -- The third element of the tuple indicates whether the fields are already extracted (True) or need extraction from majorArgs (False)
  let ctorFromMajor = getCtorFromMajor majorHead majorArgs
  let kLike = tryKLikeReduction recInfo recLevels args whnfStep
  -- Get inductive name and type params for structure eta expansion
  let inductName = getInductiveFromRecursor recName
  let typeParams = listTake recInfo.numParams args
  let structEta = tryStructEtaExpand env inductName recLevels typeParams major'
  let _ = if debugIota then trace "IOTA: inductName=\{show inductName} typeParams count=\{show (length typeParams)}" () else ()
  -- The <|> chain tries each alternative in order
  -- ctorFromMajor: Check if the whnf'd major is directly a constructor
  -- kLike: For K-like recursors (like Eq.rec), synthesize the constructor
  -- structEta: For structure-like types, eta-expand the major to a constructor
  (ctorName, _, ctorFieldArgs, fieldsProvided) <-
    (do (n, l, a) <- ctorFromMajor
        -- Verify this is actually a constructor, not just any Const
        _ <- getConstructorInfo env n
        -- For NatLit, fields are already provided; for Const, need to extract
        let provided = case majorHead of
                         NatLit _ => True
                         _ => False
        Just (n, l, a, provided)) <|>
    (do (n, l, a) <- kLike
        Just (n, l, a, True)) <|>
    (do (n, l, a) <- structEta
        Just (n, l, a, True))
  (_, ctorIdx, ctorNumParams, ctorNumFields) <- getConstructorInfo env ctorName
  let ruleResult = findRecRule recInfo.rules ctorName
  rule <- ruleResult
  -- For synthesized constructors (K-like, NatLit, struct eta), ctorFieldArgs already contains the fields
  -- For regular constructor from majorArgs, we need to drop params
  let ctorFields = if fieldsProvided
                     then ctorFieldArgs
                     else listDrop ctorNumParams majorArgs
  guard (length ctorFields >= ctorNumFields)
  let firstIndexIdx = recInfo.numParams + recInfo.numMotives + recInfo.numMinors
  let rhs = instantiateLevelParams recLevelParams recLevels rule.rhs
  let rhsWithParamsMotivesMinors = mkApp rhs (listTake firstIndexIdx args)
  let rhsWithFields = mkApp rhsWithParamsMotivesMinors ctorFields
  let remainingArgs = listDrop (majorIdx + 1) args
  pure (mkApp rhsWithFields remainingArgs)

------------------------------------------------------------------------
-- Projection Reduction
------------------------------------------------------------------------

-- Debug flag for projection reduction
debugProj : Bool
debugProj = False

export covering
tryProjReduction : TCEnv -> ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryProjReduction env (Proj structName idx struct) whnfStep = do
  let struct' = iterWhnfStep whnfStep struct 100
  let _ = if debugProj then trace "PROJ: struct=\{show structName} idx=\{show idx}" () else ()
  let _ = if debugProj then trace "PROJ: struct'=\{ppClosedExpr struct'}" () else ()
  let (head, args) = getAppSpine struct'
  let _ = if debugProj then trace "PROJ: head=\{ppClosedExpr head} args=\{show (length args)}" () else ()
  (ctorName, _) <- getConstHead head
  let _ = if debugProj then trace "PROJ: ctorName=\{show ctorName}" () else ()
  (_, _, numParams, numFields) <- getConstructorInfo env ctorName
  let _ = if debugProj then trace "PROJ: numParams=\{show numParams} numFields=\{show numFields}" () else ()
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

mkQBVar : Nat -> Expr
mkQBVar n = BVar n

mkQPi : Name -> BinderInfo -> Expr -> Expr -> Expr
mkQPi name bi ty body = Pi name bi ty body

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
        -- rTy: at depth 1 (after α), so α = BVar 0
        rTy = mkQPi (Str "_" Anonymous) Default (mkQBVar 0) (mkQPi (Str "_" Anonymous) Default (mkQBVar 1) prop)
        -- fTy domain: at depth 3 (after α, r, β), so α = BVar 2, r = BVar 1, β = BVar 0
        -- fTy body: at depth 4 (after α, r, β, _), so β = BVar 1
        fTy = mkQPi (Str "_" Anonymous) Default (mkQBVar 2) (mkQBVar 1)
        -- hTy: at depth 4 (after α, r, β, f)
        -- hTy "a" domain: α = BVar 3
        -- hTy "b" domain (depth 5): α = BVar 4
        -- hTy "_" domain (depth 6): r = BVar 4, a = BVar 1, b = BVar 0
        -- hTy "_" body (depth 7): Eq (f a) (f b), β = BVar 4, f = BVar 3, a = BVar 2, b = BVar 1
        hTy = mkQPi (Str "a" Anonymous) Default (mkQBVar 3)
                (mkQPi (Str "b" Anonymous) Default (mkQBVar 4)
                  (mkQPi (Str "_" Anonymous) Default
                    (App (App (mkQBVar 4) (mkQBVar 1)) (mkQBVar 0))
                    (App (App (App (Const (Str "Eq" Anonymous) [v]) (mkQBVar 4))
                              (App (mkQBVar 3) (mkQBVar 2)))
                         (App (mkQBVar 3) (mkQBVar 1)))))
        -- qTy domain: at depth 5 (after α, r, β, f, h), so α = BVar 4, r = BVar 3
        -- qTy body: at depth 6 (after α, r, β, f, h, _), so β = BVar 3
        liftTy = mkQPi alphaName Implicit sortU
                   (mkQPi rName Implicit rTy
                     (mkQPi betaName Implicit sortV
                       (mkQPi fName Default fTy
                         (mkQPi hName Default hTy
                           (mkQPi (Str "_" Anonymous) Default
                             (App (App (Const quotName [u]) (mkQBVar 4)) (mkQBVar 3))
                             (mkQBVar 3))))))
    in Just (liftTy, [uName, vName])
  else if name == quotIndName then
    let u = Param uName
        sortU = Sort u
        prop = Sort Zero
        -- rTy: at depth 1 (after α), so α = BVar 0
        rTy = mkQPi (Str "_" Anonymous) Default (mkQBVar 0) (mkQPi (Str "_" Anonymous) Default (mkQBVar 1) prop)
        -- betaTy: at depth 2 (after α, r), so α = BVar 1, r = BVar 0
        betaTy = mkQPi (Str "_" Anonymous) Default (App (App (Const quotName [u]) (mkQBVar 1)) (mkQBVar 0)) prop
        -- hTy domain: at depth 3 (after α, r, β), so α = BVar 2, r = BVar 1, β = BVar 0
        -- hTy body: at depth 4 (after α, r, β, a), so α = BVar 3, r = BVar 2, β = BVar 1, a = BVar 0
        hTy = mkQPi (Str "a" Anonymous) Default (mkQBVar 2)
                (App (mkQBVar 1) (App (App (App (Const quotMkName [u]) (mkQBVar 3)) (mkQBVar 2)) (mkQBVar 0)))
        -- qTy domain: at depth 4 (after α, r, β, h), so α = BVar 3, r = BVar 2, β = BVar 1, h = BVar 0
        -- result: at depth 5 (after α, r, β, h, q), so α = BVar 4, r = BVar 3, β = BVar 2, h = BVar 1, q = BVar 0
        indTy = mkQPi alphaName Implicit sortU
                  (mkQPi rName Implicit rTy
                    (mkQPi betaName Implicit betaTy
                      (mkQPi hName Default hTy
                        (mkQPi qName Default (App (App (Const quotName [u]) (mkQBVar 3)) (mkQBVar 2))
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
-- WHNF
------------------------------------------------------------------------

export covering
whnf : TCEnv -> ClosedExpr -> TC ClosedExpr
whnf env e = do
  useFuel
  pure (whnfPure 1000 e)
  where
    whnfStepCore : ClosedExpr -> Maybe ClosedExpr
    whnfStepCore (App (Lam _ _ _ body) arg) = Just (instantiate1 body arg)
    whnfStepCore (App f arg) = case whnfStepCore f of
      Just f' => Just (App f' arg)
      Nothing => Nothing
    whnfStepCore (Let _ _ val body) = Just (instantiate1 body val)
    whnfStepCore _ = Nothing

    whnfStepWithDelta : ClosedExpr -> Maybe ClosedExpr
    whnfStepWithDelta e = case whnfStepCore e of
      Just e' => Just e'
      Nothing => unfoldHead env e

    -- Full step function that includes native evaluation, iota and projection reduction
    -- This is passed to native eval functions so they can reduce arguments
    -- IMPORTANT: tryNativeEval comes BEFORE tryProjReduction so that functions like
    -- Nat.ble can be natively evaluated before being unfolded
    -- Note: reduceAppHead is NOT called here to avoid infinite loop - it's only called from whnfPure
    whnfStepFull : ClosedExpr -> Maybe ClosedExpr
    whnfStepFull e = case whnfStepCore e of
      Just e' => Just e'
      Nothing => case tryNativeEval e whnfStepFull of
        Just e' => Just e'
        Nothing => case tryProjReduction env e whnfStepWithDelta of
          Just e' => Just e'
          Nothing => case tryIotaReduction env e whnfStepFull of
            Just e' => Just e'
            Nothing => unfoldHead env e

    reduceAppHead : ClosedExpr -> Maybe ClosedExpr
    reduceAppHead (App f arg) = case reduceAppHead f of
      Just f' => Just (App f' arg)
      Nothing => case tryProjReduction env f whnfStepFull of
        Just f' => Just (App f' arg)
        Nothing => case unfoldHead env f of
          Just f' => Just (App f' arg)
          Nothing => Nothing
    reduceAppHead _ = Nothing

    whnfPure : Nat -> ClosedExpr -> ClosedExpr
    whnfPure 0 e =
      let _ = if debugWhnf then trace "WHNF: fuel exhausted on \{ppClosedExpr e}" () else ()
      in e
    whnfPure (S k) e = case whnfStepCore e of
      Just e' =>
        let _ = if debugWhnf then trace "WHNF-core: \{ppClosedExpr e} -> ..." () else ()
        in whnfPure k e'
      -- Try native eval BEFORE unfolding heads, so we can catch
      -- Decidable.decide, UInt32.decLt etc before they unfold
      Nothing => case tryNativeEval e whnfStepFull of
        Just e' =>
          let _ = if debugWhnf then trace "WHNF-native: \{ppClosedExpr e} -> ..." () else ()
          in whnfPure k e'
        Nothing => case reduceAppHead e of
          Just e' =>
            let _ = if debugWhnf then trace "WHNF-apphead: \{ppClosedExpr e} -> ..." () else ()
            in whnfPure k e'
          Nothing => case tryProjReduction env e whnfStepFull of
            Just e' =>
              let _ = if debugWhnf then trace "WHNF-proj: \{ppClosedExpr e} -> ..." () else ()
              in whnfPure k e'
            Nothing => case (if env.quotInit then tryQuotReduction e whnfStepFull else Nothing) of
              Just e' =>
                let _ = if debugWhnf then trace "WHNF-quot: \{ppClosedExpr e} -> ..." () else ()
                in whnfPure k e'
              Nothing => case tryIotaReduction env e whnfStepFull of
                Just e' =>
                  let _ = if debugWhnf then trace "WHNF-iota: \{ppClosedExpr e} -> ..." () else ()
                  in whnfPure k e'
                Nothing => case tryIotaReduction env e whnfStepWithDelta of
                  Just e' =>
                    let _ = if debugWhnf then trace "WHNF-iota-delta: \{ppClosedExpr e} -> ..." () else ()
                    in whnfPure k e'
                  Nothing => case unfoldHead env e of
                    Just e' =>
                      let _ = if debugWhnf then trace "WHNF-unfold: \{ppClosedExpr e} -> ..." () else ()
                      in whnfPure k e'
                    Nothing => e

export covering
whnfCore : ClosedExpr -> TC ClosedExpr
whnfCore e = pure (whnfCorePure 1000 e)
  where
    whnfStepCore : ClosedExpr -> Maybe ClosedExpr
    whnfStepCore (App (Lam _ _ _ body) arg) = Just (instantiate1 body arg)
    whnfStepCore (Let _ _ val body) = Just (instantiate1 body val)
    whnfStepCore _ = Nothing

    whnfCorePure : Nat -> ClosedExpr -> ClosedExpr
    whnfCorePure 0 e = e
    whnfCorePure (S k) e = case whnfStepCore e of
      Nothing => e
      Just e' => whnfCorePure k e'

export
getAppHead : ClosedExpr -> Maybe (Name, List Level, List ClosedExpr)
getAppHead expr = go expr []
  where
    go : ClosedExpr -> List ClosedExpr -> Maybe (Name, List Level, List ClosedExpr)
    go (App f' arg) args = go f' (arg :: args)
    go (Const name levels) args = Just (name, levels, args)
    go _ _ = Nothing
