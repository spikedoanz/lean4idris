module Lean4Idris.TypeChecker.Reduction

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Subst
import Lean4Idris.TypeChecker.Monad
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
-- Native Evaluation (for native_decide support)
------------------------------------------------------------------------

-- Lean name constructors for Nat operations
natName : Name
natName = Str "Nat" Anonymous

natBleName : Name
natBleName = Str "ble" natName

natBltName : Name
natBltName = Str "blt" natName

natBeqName : Name
natBeqName = Str "beq" natName

natDecLeName : Name
natDecLeName = Str "decLe" natName

natDecEqName : Name
natDecEqName = Str "decEq" natName

natAddName : Name
natAddName = Str "add" natName

natSubName : Name
natSubName = Str "sub" natName

natMulName : Name
natMulName = Str "mul" natName

natDivName : Name
natDivName = Str "div" natName

natModName : Name
natModName = Str "mod" natName

-- Bool constructors
boolName : Name
boolName = Str "Bool" Anonymous

boolTrueName : Name
boolTrueName = Str "true" boolName

boolFalseName : Name
boolFalseName = Str "false" boolName

-- Decidable constructors
decidableName : Name
decidableName = Str "Decidable" Anonymous

isTrue : Name
isTrue = Str "isTrue" decidableName

isFalse : Name
isFalse = Str "isFalse" decidableName

-- String operations
stringName : Name
stringName = Str "String" Anonymous

stringDecEqName : Name
stringDecEqName = Str "decEq" stringName

stringBeqName : Name
stringBeqName = Str "beq" stringName

stringAppendName : Name
stringAppendName = Str "append" stringName

stringLengthName : Name
stringLengthName = Str "length" stringName

-- Helper to extract Nat from NatLit
getNatLit : ClosedExpr -> Maybe Nat
getNatLit (NatLit n) = Just n
getNatLit _ = Nothing

-- Helper to extract String from StringLit
getStringLit : ClosedExpr -> Maybe String
getStringLit (StringLit s) = Just s
getStringLit _ = Nothing

-- Make Bool constant
mkBool : Bool -> ClosedExpr
mkBool True = Const boolTrueName []
mkBool False = Const boolFalseName []

-- Try to reduce Nat.ble n m to true/false
-- Nat.ble : Nat → Nat → Bool
tryNatBle : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatBle args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = mkBool (n <= m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.blt n m to true/false
-- Nat.blt : Nat → Nat → Bool
tryNatBlt : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatBlt args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = mkBool (n < m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.beq n m to true/false
-- Nat.beq : Nat → Nat → Bool
tryNatBeq : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatBeq args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = mkBool (n == m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.add n m to a NatLit
-- Nat.add : Nat → Nat → Nat
tryNatAdd : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatAdd args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (n + m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.sub n m to a NatLit (truncated subtraction)
-- Nat.sub : Nat → Nat → Nat
tryNatSub : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatSub args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (minus n m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.mul n m to a NatLit
-- Nat.mul : Nat → Nat → Nat
tryNatMul : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatMul args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (n * m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Helper: Nat division (Lean-style: div by 0 returns 0)
natDiv : Nat -> Nat -> Nat
natDiv n Z = Z
natDiv n (S m) = go n (S m) n
  where
    go : Nat -> Nat -> Nat -> Nat
    go Z _ _ = Z
    go (S fuel) d acc = if acc < d then Z else S (go fuel d (minus acc d))

-- Helper: Nat modulo (Lean-style: mod by 0 returns n)
natMod : Nat -> Nat -> Nat
natMod n Z = n
natMod n (S m) = go n (S m) n
  where
    go : Nat -> Nat -> Nat -> Nat
    go Z _ acc = acc
    go (S fuel) d acc = if acc < d then acc else go fuel d (minus acc d)

-- Try to reduce Nat.div n m to a NatLit
-- Nat.div : Nat → Nat → Nat
tryNatDiv : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatDiv args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (natDiv n m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.mod n m to a NatLit
-- Nat.mod : Nat → Nat → Nat
tryNatMod : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatMod args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (natMod n m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- HMod class and method
hModClassName : Name
hModClassName = Str "HMod" Anonymous

hModHModName : Name
hModHModName = Str "hMod" hModClassName

-- HPow class and method
hPowClassName : Name
hPowClassName = Str "HPow" Anonymous

hPowHPowName : Name
hPowHPowName = Str "hPow" hPowClassName

-- Nat.pow
natPowName : Name
natPowName = Str "pow" natName

-- Helper: Nat power
natPow : Nat -> Nat -> Nat
natPow _ Z = 1
natPow b (S e) = b * natPow b e

-- Try to reduce Nat.pow b e to a NatLit
-- Nat.pow : Nat → Nat → Nat
tryNatPow : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatPow args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  b <- getNatLit arg0'
  e <- getNatLit arg1'
  let result = NatLit (natPow b e)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce HPow.hPow when applied to Nat arguments
-- HPow.hPow : {α β γ} → [inst] → α → β → γ
-- For Nat, this is Nat.pow
tryHPowHPow : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryHPowHPow args whnfStep = do
  -- HPow.hPow has 6 args: 3 implicit types + instance + 2 operands
  guard (length args >= 6)
  arg4 <- listNth args 4  -- base
  arg5 <- listNth args 5  -- exponent
  let arg4' = iterWhnfStep whnfStep arg4 100
  let arg5' = iterWhnfStep whnfStep arg5 100
  b <- getNatLit arg4'
  e <- getNatLit arg5'
  let result = NatLit (natPow b e)
  let remaining = listDrop 6 args
  pure (mkApp result remaining)

-- Try to reduce HMod.hMod when applied to Nat arguments
-- HMod.hMod : {α β γ} → [inst] → α → β → γ
-- For Nat, this is just Nat.mod
tryHModHMod : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryHModHMod args whnfStep = do
  -- HMod.hMod has 6 args: 3 implicit types + instance + 2 operands
  guard (length args >= 6)
  arg4 <- listNth args 4  -- first operand
  arg5 <- listNth args 5  -- second operand
  let arg4' = iterWhnfStep whnfStep arg4 100
  let arg5' = iterWhnfStep whnfStep arg5 100
  n <- getNatLit arg4'
  m <- getNatLit arg5'
  let result = NatLit (natMod n m)
  let remaining = listDrop 6 args
  pure (mkApp result remaining)

-- Try to reduce String.beq s1 s2 to true/false
-- String.beq : String → String → Bool
tryStringBeq : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryStringBeq args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  s1 <- getStringLit arg0'
  s2 <- getStringLit arg1'
  let result = mkBool (s1 == s2)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce String.append s1 s2 to a StringLit
-- String.append : String → String → String
tryStringAppend : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryStringAppend args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  s1 <- getStringLit arg0'
  s2 <- getStringLit arg1'
  let result = StringLit (s1 ++ s2)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce String.length s to a NatLit
-- String.length : String → Nat
tryStringLength : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryStringLength args whnfStep = do
  guard (length args >= 1)
  arg0 <- listNth args 0
  let arg0' = iterWhnfStep whnfStep arg0 100
  s <- getStringLit arg0'
  let result = NatLit (length s)
  let remaining = listDrop 1 args
  pure (mkApp result remaining)

-- Fin operations
finName : Name
finName = Str "Fin" Anonymous

finValName : Name
finValName = Str "val" finName

-- Try to reduce Fin.val to extract the underlying Nat
-- Fin.val : Fin n → Nat
-- Fin values are often constructed as ⟨natVal, proof⟩
tryFinVal : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryFinVal args whnfStep = do
  guard (length args >= 2)  -- n and the Fin value
  finVal <- listNth args 1
  let finVal' = iterWhnfStep whnfStep finVal 100
  -- Try to extract from constructor application
  case getAppConst finVal' of
    Just (ctorName, _, ctorArgs) => do
      -- Fin.mk n val proof -> val is first arg after the type param
      guard (length ctorArgs >= 2)
      valArg <- listNth ctorArgs 1
      let valArg' = iterWhnfStep whnfStep valArg 100
      case valArg' of
        NatLit n =>
          let remaining = listDrop 2 args
          in pure (mkApp (NatLit n) remaining)
        _ => Nothing
    Nothing => Nothing

-- BitVec operations
bitVecName : Name
bitVecName = Str "BitVec" Anonymous

bitVecToNatName : Name
bitVecToNatName = Str "toNat" bitVecName

bitVecOfNatName : Name
bitVecOfNatName = Str "ofNat" bitVecName

-- Try to reduce BitVec.toNat
tryBitVecToNat : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryBitVecToNat args whnfStep = do
  guard (length args >= 2)  -- width and the BitVec value
  bvVal <- listNth args 1
  let bvVal' = iterWhnfStep whnfStep bvVal 100
  case getAppConst bvVal' of
    Just (name, _, bvArgs) =>
      -- If it's BitVec.ofNat w n, return n mod 2^w
      if name == bitVecOfNatName then do
        guard (length bvArgs >= 2)
        nArg <- listNth bvArgs 1
        let nArg' = iterWhnfStep whnfStep nArg 100
        n <- getNatLit nArg'
        -- For simplicity, just return n (assuming it's in range)
        let remaining = listDrop 2 args
        pure (mkApp (NatLit n) remaining)
      else Nothing
    Nothing => Nothing

-- UInt32 operations
uint32Name : Name
uint32Name = Str "UInt32" Anonymous

uint32ToNatName : Name
uint32ToNatName = Str "toNat" uint32Name

uint32OfNatName : Name
uint32OfNatName = Str "ofNat" uint32Name

-- decide function (both Decidable.decide and the top-level decide)
decidableDecideName : Name
decidableDecideName = Str "decide" decidableName

decideFnName : Name
decideFnName = Str "decide" Anonymous

-- Nat.decLt and Nat.decLe
natDecLtName : Name
natDecLtName = Str "decLt" natName

-- instDecidableLtNat (for Nat < comparison)
instDecidableLtNatName : Name
instDecidableLtNatName = Str "instDecidableLtNat" Anonymous

-- instDecidableLtBitVec
instDecidableLtBitVecName : Name
instDecidableLtBitVecName = Str "instDecidableLtBitVec" Anonymous

-- UInt32.decLt
uint32DecLtName : Name
uint32DecLtName = Str "decLt" uint32Name

-- Try to reduce UInt32.toNat
tryUInt32ToNat : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryUInt32ToNat args whnfStep = do
  guard (length args >= 1)
  uVal <- listNth args 0
  let uVal' = iterWhnfStep whnfStep uVal 100
  case getAppConst uVal' of
    Just (name, _, uArgs) =>
      if name == uint32OfNatName then do
        guard (length uArgs >= 2)
        nArg <- listNth uArgs 1
        let nArg' = iterWhnfStep whnfStep nArg 100
        n <- getNatLit nArg'
        let remaining = listDrop 1 args
        pure (mkApp (NatLit n) remaining)
      else Nothing
    Nothing => Nothing

-- OfNat class and ofNat function
ofNatClassName : Name
ofNatClassName = Str "OfNat" Anonymous

ofNatOfNatName : Name
ofNatOfNatName = Str "ofNat" ofNatClassName

-- UInt32.ofBitVec name
uint32OfBitVecName : Name
uint32OfBitVecName = Str "ofBitVec" uint32Name

-- BitVec.ofFin name
bitVecOfFinName : Name
bitVecOfFinName = Str "ofFin" bitVecName

-- Helper: try to extract Nat from possible HPow projection
-- Handles (Proj HPow 0 inst) base expo -> base^expo
covering
tryGetNatFromPossiblePow : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Maybe Nat
tryGetNatFromPossiblePow whnfStep e' =
  case getNatLit e' of
    Just n => Just n
    Nothing =>
      -- Try to handle HPow projection: (Proj HPow 0 inst) arg1 arg2
      let (h, s) = getAppSpine e'
      in case h of
           Proj psn _ _ =>
             if psn == hPowClassName then do
               guard (length s >= 2)
               base <- listNth s 0
               expo <- listNth s 1
               let base' = iterWhnfStep whnfStep base 100
               let expo' = iterWhnfStep whnfStep expo 100
               b <- getNatLit base'
               e <- getNatLit expo'
               trace ("        HPow: " ++ show b ++ "^" ++ show e ++ " = " ++ show (natPow b e)) $
                 Just (natPow b e)
             else Nothing
           _ => Nothing

-- Helper: try to extract a Nat from a Fin expression
-- Fin values are structured as ⟨n, proof⟩ where we want to extract n
covering
tryGetFinAsNat : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Maybe Nat
tryGetFinAsNat whnfStep e =
  let e' = iterWhnfStep whnfStep e 100
  in trace "      tryGetFinAsNat: \{case getAppConst e' of Just (name, _, args) => "head=" ++ show name ++ " with " ++ show (length args) ++ " args"; Nothing => "not app const"}" $
     case getAppConst e' of
    Just (name, _, args) =>
      -- Fin.mk n proof -> args would be [bound, n, proof] or similar
      -- For Fin.mk : {n : Nat} -> (val : Nat) -> val < n -> Fin n
      -- Actually Fin is typically represented structurally
      -- Try projection: Fin.val fin
      let finMkName = Str "mk" finName
      in trace "      comparing name=\{show name} vs finMkName=\{show finMkName}" $
      if name == finMkName then do
        trace "      matched Fin.mk with \{show (length args)} args" $ guard (length args >= 2)
        valArg <- listNth args 1  -- val is the second arg (after implicit bound)
        -- Try more iterations and trace the raw valArg too
        trace "      raw valArg: \{case getAppConst valArg of Just (n, _, a) => show n ++ " args=" ++ show (length a); Nothing => "not const app"}" $ do
        let valArg' = iterWhnfStep whnfStep valArg 500
        let headStr = case getAppConst valArg' of
                        Just (n, _, a) => "head=" ++ show n ++ " with " ++ show (length a) ++ " args"
                        Nothing => case valArg' of
                                     NatLit n => "NatLit " ++ show n
                                     BVar _ => "BVar (impossible for closed)"
                                     Sort _ => "Sort"
                                     Lam _ _ _ _ => "Lam"
                                     Pi _ _ _ _ => "Pi"
                                     Let _ _ _ _ => "Let"
                                     Proj sn i _ => "Proj " ++ show sn ++ " " ++ show i
                                     StringLit _ => "StringLit"
                                     Const n _ => "Const " ++ show n
                                     App f x => let (head, spine) = getAppSpine (App f x)
                                                 in "App head=" ++ (case head of
                                                      Const n _ => show n
                                                      Lam _ _ _ _ => "Lam"
                                                      Proj sn i struct => "Proj " ++ show sn ++ "." ++ show i ++ " on struct=" ++
                                                                          (case getAppConst struct of
                                                                             Just (sn', _, sargs) => show sn' ++ " with " ++ show (length sargs) ++ " args"
                                                                             Nothing => "non-const")
                                                      NatLit n => "NatLit " ++ show n
                                                      Let _ _ _ _ => "Let"
                                                      BVar _ => "BVar"
                                                      Sort _ => "Sort"
                                                      Pi _ _ _ _ => "Pi"
                                                      _ => "unknown") ++ " with " ++ show (length spine) ++ " args"
                                     _ => "other"
        -- First try getNatLit directly
        case getNatLit valArg' of
          Just n => trace ("      valArg' direct NatLit: " ++ show n) $ Just n
          Nothing =>
            -- Try to handle HMod projection pattern: (Proj HMod 0 inst) arg1 arg2
            let (head, spine) = getAppSpine valArg'
            in case head of
                 Proj sn _ _ =>
                   -- Check if this is HMod.0 projection (the hMod method)
                   if sn == hModClassName then
                     trace ("      found HMod projection, spine length=" ++ show (length spine)) $ do
                     guard (length spine >= 2)
                     operand1 <- listNth spine 0
                     operand2 <- listNth spine 1
                     let operand1' = iterWhnfStep whnfStep operand1 100
                     let operand2' = iterWhnfStep whnfStep operand2 100
                     let op1Str = case getAppConst operand1' of
                                    Just (n, _, a) => show n ++ " with " ++ show (length a) ++ " args"
                                    Nothing => case operand1' of
                                                 NatLit n => "NatLit " ++ show n
                                                 _ => "other"
                     let op2Str = case getAppConst operand2' of
                                    Just (n, _, a) => show n ++ " with " ++ show (length a) ++ " args"
                                    Nothing => case operand2' of
                                                 NatLit n => "NatLit " ++ show n
                                                 Const n _ => "Const " ++ show n
                                                 App f x => let (h, s) = getAppSpine (App f x) in
                                                            "App head=" ++ (case h of
                                                              Const n _ => show n
                                                              Proj sn i _ => "Proj " ++ show sn ++ "." ++ show i
                                                              _ => "unknown") ++ " spine=" ++ show (length s)
                                                 _ => "other type"
                     trace ("      operand1=" ++ op1Str ++ ", operand2=" ++ op2Str) $
                     -- Short-circuit: 0 % m = 0 for any m
                     case getNatLit operand1' of
                       Just 0 => trace "      short-circuit: 0 % anything = 0" $ Just 0
                       Just n => do
                         m <- tryGetNatFromPossiblePow whnfStep operand2'
                         trace ("      HMod operands: " ++ show n ++ " % " ++ show m ++ " = " ++ show (natMod n m)) $
                           Just (natMod n m)
                       Nothing => Nothing
                   else trace ("      Proj on " ++ show sn ++ ", not HMod") Nothing
                 _ => trace ("      valArg' " ++ headStr ++ ", not NatLit or HMod proj") Nothing
      else trace "      Fin head doesn't match Fin.mk" Nothing
    -- Try to get from Proj expression (Fin.val projection)
    Nothing => case e' of
      Proj _ idx structVal =>
        if idx == 0 then do  -- val is typically field 0
          trace "      found Proj, recursing" $ do
          let structVal' = iterWhnfStep whnfStep structVal 100
          tryGetFinAsNat whnfStep structVal'
        else trace "      Proj but wrong index" Nothing
      -- If it's a NatLit directly, return it
      NatLit n => trace "      found NatLit \{show n}" $ Just n
      _ => trace "      not Proj or NatLit" Nothing

-- Helper: try to extract a Nat from a BitVec expression
covering
tryGetBitVecAsNat : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Maybe Nat
tryGetBitVecAsNat whnfStep e =
  let e' = iterWhnfStep whnfStep e 100
  in trace "    tryGetBitVecAsNat: head=\{case getAppConst e' of Just (name, _, args) => show name ++ " with " ++ show (length args) ++ " args"; Nothing => "not app const"}" $
     case getAppConst e' of
    Just (name, _, args) =>
      -- BitVec.ofNat w n -> n (args: [w, n])
      if name == bitVecOfNatName then do
        guard (length args >= 2)
        nArg <- listNth args 1
        let nArg' = iterWhnfStep whnfStep nArg 100
        getNatLit nArg'
      -- BitVec.ofFin w fin -> extract from Fin
      else if name == bitVecOfFinName then do
        trace "    matched BitVec.ofFin" $ guard (length args >= 2)
        finArg <- listNth args 1
        tryGetFinAsNat whnfStep finArg
      else trace "    doesn't match BitVec.ofNat or BitVec.ofFin" Nothing
    Nothing => Nothing

-- Helper: try to extract a Nat from a UInt32 expression
-- UInt32 values can be constructed as:
-- 1. OfNat.ofNat UInt32 n inst
-- 2. UInt32.ofNat inst n
-- 3. UInt32.ofBitVec (BitVec.ofNat 32 n)
covering
tryGetUInt32AsNat : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Maybe Nat
tryGetUInt32AsNat whnfStep e =
  let e' = iterWhnfStep whnfStep e 100
  in trace "  tryGetUInt32AsNat: head=\{case getAppConst e' of Just (name, _, args) => show name ++ " with " ++ show (length args) ++ " args"; Nothing => "not app const"}" $
     case getAppConst e' of
    Just (name, _, args) =>
      -- OfNat.ofNat ty n inst -> n (args: [ty, n, inst])
      if name == ofNatOfNatName then do
        guard (length args >= 2)
        nArg <- listNth args 1
        let nArg' = iterWhnfStep whnfStep nArg 100
        getNatLit nArg'
      -- UInt32.ofNat inst n -> n
      else if name == uint32OfNatName then do
        guard (length args >= 2)
        nArg <- listNth args 1
        let nArg' = iterWhnfStep whnfStep nArg 100
        getNatLit nArg'
      -- UInt32.ofBitVec bv -> extract from BitVec.ofNat
      else if name == uint32OfBitVecName then do
        trace "  matched UInt32.ofBitVec" $ guard (length args >= 1)
        bvArg <- listNth args 0
        -- BitVec argument, try to extract as BitVec.ofNat w n
        trace "  calling tryGetBitVecAsNat" $ tryGetBitVecAsNat whnfStep bvArg
      else Nothing
    Nothing => Nothing

-- Make isTrue/isFalse Decidable constructors
-- Note: We need to apply them to the proposition and proof, but for native_decide
-- the proof is erased, so we can use a placeholder
mkIsTrue : ClosedExpr
mkIsTrue = Const isTrue []

mkIsFalse : ClosedExpr
mkIsFalse = Const isFalse []

-- Try to reduce UInt32.decLt to isTrue/isFalse
covering
tryUInt32DecLt : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryUInt32DecLt args whnfStep =
  trace "tryUInt32DecLt called with \{show (length args)} args" $ do
  guard (length args >= 2)
  a <- listNth args 0
  b <- listNth args 1
  na <- trace "  trying to get first nat" $ tryGetUInt32AsNat whnfStep a
  nb <- trace "  got first: \{show na}, trying second" $ tryGetUInt32AsNat whnfStep b
  -- Return isTrue or isFalse (the proof args are implicit/erased)
  let result = trace "  got both: \{show na} < \{show nb}" $
               if na < nb then mkIsTrue else mkIsFalse
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.decLt to isTrue/isFalse
tryNatDecLt : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatDecLt args whnfStep = do
  guard (length args >= 2)
  a <- listNth args 0
  b <- listNth args 1
  let a' = iterWhnfStep whnfStep a 100
  let b' = iterWhnfStep whnfStep b 100
  na <- getNatLit a'
  nb <- getNatLit b'
  let result = if na < nb then mkIsTrue else mkIsFalse
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.decLe to isTrue/isFalse
tryNatDecLeNative : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatDecLeNative args whnfStep = do
  guard (length args >= 2)
  a <- listNth args 0
  b <- listNth args 1
  let a' = iterWhnfStep whnfStep a 100
  let b' = iterWhnfStep whnfStep b 100
  na <- getNatLit a'
  nb <- getNatLit b'
  let result = if na <= nb then mkIsTrue else mkIsFalse
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce decide when applied to numeric decidability instances
-- Decidable.decide inst -> true/false based on inst
-- decide P inst -> true/false based on inst
-- The instance might be Nat.decLt a b, UInt32.decLt a b, etc.
-- Or it might have already been reduced to isTrue/isFalse
covering
tryDecide : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryDecide args whnfStep = do
  guard (length args >= 1)
  -- For Decidable.decide: args[0] is the Decidable instance (p is implicit)
  -- For decide: args[0] is p, args[1] is the instance
  -- Try both positions
  instArg <- (if length args >= 2 then listNth args 1 else listNth args 0)
              <|> listNth args 0
  let instArg' = iterWhnfStep whnfStep instArg 100
  case getAppConst instArg' of
    Just (name, _, instArgs) =>
      -- If already reduced to isTrue, return true
      if name == isTrue then do
        let remaining = listDrop 2 args
        pure (mkApp (mkBool True) remaining)
      -- If already reduced to isFalse, return false
      else if name == isFalse then do
        let remaining = listDrop 2 args
        pure (mkApp (mkBool False) remaining)
      -- Nat.decLt a b
      else if name == natDecLtName then do
        guard (length instArgs >= 2)
        a <- listNth instArgs 0
        b <- listNth instArgs 1
        let a' = iterWhnfStep whnfStep a 100
        let b' = iterWhnfStep whnfStep b 100
        na <- getNatLit a'
        nb <- getNatLit b'
        let result = mkBool (na < nb)
        let remaining = listDrop 2 args
        pure (mkApp result remaining)
      -- UInt32.decLt a b (may have more args due to implicit params)
      else if name == uint32DecLtName then do
        -- UInt32.decLt takes 2 UInt32 args (a and b)
        guard (length instArgs >= 2)
        a <- listNth instArgs 0
        b <- listNth instArgs 1
        na <- tryGetUInt32AsNat whnfStep a
        nb <- tryGetUInt32AsNat whnfStep b
        let result = mkBool (na < nb)
        -- For Decidable.decide, remaining args start after the decide arg
        let remaining = listDrop 2 args
        pure (mkApp result remaining)
      -- instDecidableLtBitVec w a b
      else if name == instDecidableLtBitVecName then do
        guard (length instArgs >= 3)
        a <- listNth instArgs 1
        b <- listNth instArgs 2
        na <- tryGetBitVecAsNat whnfStep a
        nb <- tryGetBitVecAsNat whnfStep b
        let result = mkBool (na < nb)
        let remaining = listDrop 2 args
        pure (mkApp result remaining)
      -- Nat.decLe a b
      else if name == natDecLeName then do
        guard (length instArgs >= 2)
        a <- listNth instArgs 0
        b <- listNth instArgs 1
        let a' = iterWhnfStep whnfStep a 100
        let b' = iterWhnfStep whnfStep b 100
        na <- getNatLit a'
        nb <- getNatLit b'
        let result = mkBool (na <= nb)
        let remaining = listDrop 2 args
        pure (mkApp result remaining)
      else Nothing
    Nothing => Nothing

-- Main native evaluation dispatcher
export covering
tryNativeEval : ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNativeEval e whnfStep = do
  (name, _, args) <- getAppConst e
  tryNativeEvalName name args whnfStep
  where
    tryNativeEvalName : Name -> List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
    -- Nat operations
    tryNativeEvalName name args step =
      if name == natBleName then tryNatBle args step
      else if name == natBltName then tryNatBlt args step
      else if name == natBeqName then tryNatBeq args step
      else if name == natAddName then tryNatAdd args step
      else if name == natSubName then tryNatSub args step
      else if name == natMulName then tryNatMul args step
      else if name == natDivName then tryNatDiv args step
      else if name == natModName then tryNatMod args step
      else if name == hModHModName then tryHModHMod args step
      else if name == natPowName then tryNatPow args step
      else if name == hPowHPowName then tryHPowHPow args step
      -- String operations
      else if name == stringBeqName then tryStringBeq args step
      else if name == stringAppendName then tryStringAppend args step
      else if name == stringLengthName then tryStringLength args step
      -- Fin operations
      else if name == finValName then tryFinVal args step
      -- BitVec operations
      else if name == bitVecToNatName then tryBitVecToNat args step
      -- UInt32 operations
      else if name == uint32ToNatName then tryUInt32ToNat args step
      -- Decidability instances - return isTrue/isFalse directly
      else if name == uint32DecLtName then trace "dispatch: UInt32.decLt" $ tryUInt32DecLt args step
      else if name == natDecLtName then trace "dispatch: Nat.decLt" $ tryNatDecLt args step
      else if name == natDecLeName then trace "dispatch: Nat.decLe" $ tryNatDecLeNative args step
      -- decide with decidability instances (both Decidable.decide and decide)
      else if name == decideFnName then trace "dispatch: decide" $ tryDecide args step
      else if name == decidableDecideName then trace "dispatch: Decidable.decide" $ tryDecide args step
      else case name of
             Str s _ => if s == "decide" || s == "decLt"
                          then trace "unmatched name with decide/decLt string: \{show name}" Nothing
                          else Nothing
             _ => Nothing

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
    whnfStepCore (App (Lam _ _ _ body) arg) = Just (instantiate1 (believe_me body) arg)
    whnfStepCore (App f arg) = case whnfStepCore f of
      Just f' => Just (App f' arg)
      Nothing => Nothing
    whnfStepCore (Let _ _ val body) = Just (instantiate1 (believe_me body) val)
    whnfStepCore _ = Nothing

    whnfStepWithDelta : ClosedExpr -> Maybe ClosedExpr
    whnfStepWithDelta e = case whnfStepCore e of
      Just e' => Just e'
      Nothing => unfoldHead env e

    -- Full step function that includes native evaluation
    -- This is passed to native eval functions so they can reduce arguments
    whnfStepFull : ClosedExpr -> Maybe ClosedExpr
    whnfStepFull e = case whnfStepCore e of
      Just e' => Just e'
      Nothing => case tryProjReduction env e whnfStepWithDelta of
        Just e' => Just e'
        Nothing => case tryNativeEval e whnfStepFull of
          Just e' => Just e'
          Nothing => case tryIotaReduction env e whnfStepWithDelta of
            Just e' => Just e'
            Nothing => unfoldHead env e

    reduceAppHead : ClosedExpr -> Maybe ClosedExpr
    reduceAppHead (App f arg) = case reduceAppHead f of
      Just f' => Just (App f' arg)
      Nothing => case tryProjReduction env f whnfStepWithDelta of
        Just f' => Just (App f' arg)
        Nothing => case unfoldHead env f of
          Just f' => Just (App f' arg)
          Nothing => Nothing
    reduceAppHead _ = Nothing

    whnfPure : Nat -> ClosedExpr -> ClosedExpr
    whnfPure 0 e = e
    whnfPure (S k) e = case whnfStepCore e of
      Just e' => whnfPure k e'
      -- Try native eval BEFORE unfolding heads, so we can catch
      -- Decidable.decide, UInt32.decLt etc before they unfold
      Nothing =>
        let _ = case getAppConst e of
                  Just (name, _, _) => case name of
                    Str s _ => if s == "decide" || s == "decLt"
                                 then trace "whnfPure sees \{show name}" ()
                                 else ()
                    _ => ()
                  Nothing => ()
        in case tryNativeEval e whnfStepFull of
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
