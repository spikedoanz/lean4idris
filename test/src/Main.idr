module Main

import Lean4Idris
import Lean4Idris.Export.Token
import Lean4Idris.Export.Parser
import Lean4Idris.Export.Lexer
import Lean4Idris.Pretty
import Lean4Idris.Subst
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import Data.Fin
import Data.List
import System
import System.File

--------------------------------------------------------------------------------
-- Test Framework
--------------------------------------------------------------------------------

||| Result of a single test assertion
record TestResult where
  constructor MkTestResult
  name : String
  passed : Bool
  message : String  -- shown on failure or in verbose mode

||| Command-line options
record Options where
  constructor MkOptions
  verbose : Bool

||| Assert a boolean condition
assert : String -> Bool -> TestResult
assert name True = MkTestResult name True ""
assert name False = MkTestResult name False "Assertion failed"

||| Assert equality
assertEq : (Show a, Eq a) => String -> (expected : a) -> (actual : a) -> TestResult
assertEq name expected actual =
  if expected == actual
    then MkTestResult name True ""
    else MkTestResult name False $ "Expected: " ++ show expected ++ ", Got: " ++ show actual

||| Assert an Either is Right and satisfies a predicate
assertRight : Show e => String -> Either e a -> (a -> Bool) -> TestResult
assertRight name (Left err) _ = MkTestResult name False $ "Got Left: " ++ show err
assertRight name (Right val) pred =
  if pred val
    then MkTestResult name True ""
    else MkTestResult name False "Predicate failed on Right value"

||| Assert an Either is Right and equals expected value
assertRightEq : (Show e, Show a, Eq a) => String -> Either e a -> a -> TestResult
assertRightEq name (Left err) _ = MkTestResult name False $ "Got Left: " ++ show err
assertRightEq name (Right actual) expected =
  if actual == expected
    then MkTestResult name True ""
    else MkTestResult name False $ "Expected: " ++ show expected ++ ", Got: " ++ show actual

||| Assert an Either is Left (expecting failure)
assertLeft : String -> Either e a -> TestResult
assertLeft name (Left _) = MkTestResult name True ""
assertLeft name (Right _) = MkTestResult name False "Expected Left, got Right"

||| Assert a TC computation succeeds and satisfies a predicate
assertTC : String -> TC a -> (a -> Bool) -> TestResult
assertTC name tc pred = assertRight name (runTC tc) pred

||| Assert a TC computation succeeds and equals expected value
assertTCEq : (Show a, Eq a) => String -> TC a -> a -> TestResult
assertTCEq name tc expected = assertRightEq name (runTC tc) expected

||| Assert a TC computation fails
assertTCFails : String -> TC a -> TestResult
assertTCFails name tc = assertLeft name (runTC tc)

||| Parse command line arguments
parseArgs : List String -> Options
parseArgs args = MkOptions (elem "-v" args || elem "--verbose" args)

||| Print a single test result
printResult : Options -> TestResult -> IO ()
printResult opts res =
  if opts.verbose
    then putStrLn $ (if res.passed then "." else "X") ++ " " ++ res.name
    else putStr $ if res.passed then "." else "X"

||| Print failures if any
printFailures : List TestResult -> IO ()
printFailures [] = pure ()
printFailures fs = do
  putStrLn "\nFailures:"
  for_ fs (\res => putStrLn $ "  " ++ res.name ++ ": " ++ res.message)

||| Run tests and print results
runTests : Options -> List (String, List TestResult) -> IO ()
runTests opts groups =
  let allResults = concatMap snd groups in
  let numTotal = length allResults in
  let failures = filter (not . passed) allResults in
  let numFailed = length failures in
  do for_ allResults (printResult opts)
     if opts.verbose then pure () else putStrLn ""
     putStrLn $ "\n" ++ show (minus numTotal numFailed) ++ "/" ++ show numTotal ++ " tests passed"
     printFailures failures
     if numFailed > 0 then exitWith (ExitFailure 1) else pure ()

--------------------------------------------------------------------------------
-- Test: Lexer
--------------------------------------------------------------------------------

testLexer : List TestResult
testLexer =
  let input = "1 #NS 0 Nat\n2 #NS 0 zero\n"
  in case lexToTokens input of
       Left err => [MkTestResult "lexer: basic input" False $ "Lexer error: " ++ err]
       Right toks => [assert "lexer: produces tokens" (length toks > 0)]

--------------------------------------------------------------------------------
-- Test: Parser
--------------------------------------------------------------------------------

testParser : List TestResult
testParser =
  let input = "0.0.0\n1 #NS 0 Nat\n2 #NS 0 zero\n3 #NS 1 succ\n1 #US 0\n1 #ES 1\n2 #EC 1\n3 #EC 2\n"
  in case parseExport input of
       Left err => [MkTestResult "parser: basic input" False $ "Parse error: " ++ err]
       Right st =>
         [ assert "parser: parses names" (length (getNames st) > 0)
         , assert "parser: parses levels" (length (getLevels st) > 0)
         , assert "parser: parses exprs" (length (getExprs st) > 0)
         ]

--------------------------------------------------------------------------------
-- Test: Expression Construction
--------------------------------------------------------------------------------

testExpr : List TestResult
testExpr =
  let ty : ClosedExpr = Sort (Succ Zero)
      nat : ClosedExpr = Const (Str "Nat" Anonymous) []
      succName = Str "succ" (Str "Nat" Anonymous)
      zeroName = Str "zero" (Str "Nat" Anonymous)
      succZero : ClosedExpr = App (Const succName []) (Const zeroName [])
  in [ assert "expr: Sort 1 pretty prints" (ppClosedExpr ty == "Sort 1")
     , assert "expr: Nat pretty prints" (ppClosedExpr nat == "Nat")
     , assert "expr: App pretty prints" (length (ppClosedExpr succZero) > 0)
     ]

--------------------------------------------------------------------------------
-- Test: WHNF Reduction
--------------------------------------------------------------------------------

testWhnf : List TestResult
testWhnf =
  let env = emptyEnv
      sort1 : ClosedExpr = Sort (Succ Zero)
      nat : ClosedExpr = Const (Str "Nat" Anonymous) []
      zeroName = Str "zero" (Str "Nat" Anonymous)
      zero : ClosedExpr = Const zeroName []
      idBody : Expr 1 = BVar FZ
      idLam : ClosedExpr = Lam (Str "x" Anonymous) Default nat idBody
      app : ClosedExpr = App idLam zero
      letExpr : ClosedExpr = Let (Str "x" Anonymous) nat zero (BVar FZ)
  in [ assertTCEq "whnf: Sort is WHNF" (whnf env sort1) sort1
     , assertTCEq "whnf: beta reduction (λx.x) zero => zero" (whnf env app) zero
     , assertTCEq "whnf: let substitution" (whnf env letExpr) zero
     ]

--------------------------------------------------------------------------------
-- Test: Type Inference
--------------------------------------------------------------------------------

testInferType : List TestResult
testInferType =
  let env = emptyEnv
      sort0 : ClosedExpr = Sort Zero
      sort1 : ClosedExpr = Sort (Succ Zero)
      sort2 : ClosedExpr = Sort (Succ (Succ Zero))
      natLit : ClosedExpr = NatLit 42
      natConst : ClosedExpr = Const (Str "Nat" Anonymous) []
  in [ assertTCEq "infer: Sort 0 : Sort 1" (inferType env sort0) sort1
     , assertTCEq "infer: Sort 1 : Sort 2" (inferType env sort1) sort2
     , assertTCEq "infer: 42 : Nat" (inferType env natLit) natConst
     ]

--------------------------------------------------------------------------------
-- Test: Definitional Equality
--------------------------------------------------------------------------------

testIsDefEq : List TestResult
testIsDefEq =
  let natName = Str "Nat" Anonymous
      nat : ClosedExpr = Const natName []
      natDecl = AxiomDecl natName (Sort (Succ Zero)) []
      yName = Str "y" Anonymous
      y : ClosedExpr = Const yName []
      yDecl = AxiomDecl yName nat []
      env = addDecl yDecl (addDecl natDecl emptyEnv)
      sort1 : ClosedExpr = Sort (Succ Zero)
      sort1' : ClosedExpr = Sort (Succ Zero)
      sort0 : ClosedExpr = Sort Zero
      idBody : Expr 1 = BVar FZ
      idLam : ClosedExpr = Lam (Str "x" Anonymous) Default nat idBody
      appIdY : ClosedExpr = App idLam y
  in [ assertTCEq "defEq: Nat == Nat" (isDefEq env nat nat) True
     , assertTCEq "defEq: Sort 1 == Sort 1" (isDefEq env sort1 sort1') True
     , assertTCEq "defEq: Sort 0 != Sort 1" (isDefEq env sort0 sort1) False
     , assertTCEq "defEq: (λx.x) y == y" (isDefEq env appIdY y) True
     ]

--------------------------------------------------------------------------------
-- Test: Delta Reduction
--------------------------------------------------------------------------------

testDelta : List TestResult
testDelta =
  let natName = Str "Nat" Anonymous
      nat : ClosedExpr = Const natName []
      natDecl = AxiomDecl natName (Sort (Succ Zero)) []
      natInBody : Expr 1 = Const natName []
      zeroName = Str "zero" (Str "Nat" Anonymous)
      zero : ClosedExpr = Const zeroName []
      zeroDecl = AxiomDecl zeroName nat []
      idBody : Expr 1 = BVar FZ
      idLam : ClosedExpr = Lam (Str "x" Anonymous) Default nat idBody
      idType : ClosedExpr = Pi (Str "x" Anonymous) Default nat natInBody
      myIdName = Str "myId" Anonymous
      myIdDecl = DefDecl myIdName idType idLam Abbrev Safe []
      env = addDecl myIdDecl (addDecl zeroDecl (addDecl natDecl emptyEnv))
      myIdRef : ClosedExpr = Const myIdName []
      myIdZero : ClosedExpr = App myIdRef zero
      opaqueIdDecl = DefDecl (Str "opaqueId" Anonymous) idType idLam Opaq Safe []
      envWithOpaque = addDecl opaqueIdDecl env
      opaqueIdRef : ClosedExpr = Const (Str "opaqueId" Anonymous) []
  in [ assertTCEq "delta: myId unfolds to λx.x" (whnf env myIdRef) idLam
     , assertTCEq "delta: myId zero => zero" (whnf env myIdZero) zero
     , assertTCEq "delta: myId zero == zero" (isDefEq env myIdZero zero) True
     , assertTCEq "delta: opaque doesn't unfold" (whnf envWithOpaque opaqueIdRef) opaqueIdRef
     ]

--------------------------------------------------------------------------------
-- Test: Eta Expansion
--------------------------------------------------------------------------------

testEta : List TestResult
testEta =
  let natName = Str "Nat" Anonymous
      nat : ClosedExpr = Const natName []
      natDecl = AxiomDecl natName (Sort (Succ Zero)) []
      natInBody : Expr 1 = Const natName []
      idBody : Expr 1 = BVar FZ
      idLam : ClosedExpr = Lam (Str "x" Anonymous) Default nat idBody
      idType : ClosedExpr = Pi (Str "x" Anonymous) Default nat natInBody
      myIdName = Str "myId" Anonymous
      myIdDecl = DefDecl myIdName idType idLam Abbrev Safe []
      env = addDecl myIdDecl (addDecl natDecl emptyEnv)
      myIdRef : ClosedExpr = Const myIdName []
      etaExpanded : ClosedExpr = Lam (Str "x" Anonymous) Default nat (App (weaken1 myIdRef) (BVar FZ))
      fName = Str "f" Anonymous
      fDecl = AxiomDecl fName idType []
      envWithF = addDecl fDecl (addDecl natDecl emptyEnv)
      fRef : ClosedExpr = Const fName []
      fEtaExpanded : ClosedExpr = Lam (Str "x" Anonymous) Default nat (App (weaken1 fRef) (BVar FZ))
  in [ assertTCEq "eta: λx. myId x == myId" (isDefEq env etaExpanded myIdRef) True
     , assertTCEq "eta: myId == λx. myId x" (isDefEq env myIdRef etaExpanded) True
     , assertTCEq "eta: λx. f x == f (axiom)" (isDefEq envWithF fEtaExpanded fRef) True
     ]

--------------------------------------------------------------------------------
-- Test: Iota Reduction
--------------------------------------------------------------------------------

testIota : List TestResult
testIota =
  let natName = Str "Nat" Anonymous
      zeroName = Str "zero" (Str "Nat" Anonymous)
      succName = Str "succ" (Str "Nat" Anonymous)
      recName = Str "rec" (Str "Nat" Anonymous)
      natType : ClosedExpr = Sort (Succ Zero)
      natConst : ClosedExpr = Const natName []
      zeroType : ClosedExpr = natConst
      natInBody : Expr 1 = Const natName []
      succType : ClosedExpr = Pi (Str "n" Anonymous) Default natConst natInBody
      natIndInfo = MkInductiveInfo natName natType 0 0
                     [ MkConstructorInfo zeroName zeroType
                     , MkConstructorInfo succName succType ]
                     True False
      motiveTy : ClosedExpr = Pi (Str "_" Anonymous) Default natConst (Sort (Succ Zero))
      motive1 : Expr 1 = BVar FZ
      hzTy1 : Expr 1 = App motive1 (Const zeroName [])
      zeroRhs : ClosedExpr =
        Lam (Str "motive" Anonymous) Default motiveTy
          (Lam (Str "hz" Anonymous) Default hzTy1
            (Lam (Str "hs" Anonymous) Default (Sort Zero)
              (BVar (FS FZ))))
      zeroRule = MkRecursorRule zeroName 0 zeroRhs
      recType : ClosedExpr = Sort Zero
      natRecInfo = MkRecursorInfo recName recType 0 0 1 2 [zeroRule] False
      env0 = emptyEnv
      env1 = addDecl (IndDecl natIndInfo []) env0
      env2 = addDecl (CtorDecl zeroName zeroType natName 0 0 0 []) env1
      env3 = addDecl (CtorDecl succName succType natName 1 0 1 []) env2
      env4 = addDecl (RecDecl natRecInfo []) env3
      motive : ClosedExpr = Lam (Str "_" Anonymous) Default natConst (Sort (Succ Zero))
      hz : ClosedExpr = Sort Zero
      hs : ClosedExpr = Lam (Str "n" Anonymous) Default natConst
                          (Lam (Str "ih" Anonymous) Default (Sort (Succ Zero)) (BVar FZ))
      zero : ClosedExpr = Const zeroName []
      recApp = App (App (App (App (Const recName []) motive) hz) hs) zero
  in [ assertTCEq "iota: rec motive hz hs zero => hz" (whnf env4 recApp) hz
     ]

--------------------------------------------------------------------------------
-- Test: Open Term Type Inference
--------------------------------------------------------------------------------

testOpenInfer : List TestResult
testOpenInfer =
  let natName = Str "Nat" Anonymous
      nat : ClosedExpr = Const natName []
      natDecl = AxiomDecl natName (Sort (Succ Zero)) []
      env = addDecl natDecl emptyEnv
      ctx1 : LocalCtx 1 = extendCtx (Str "x" Anonymous) nat emptyCtx
      bvar0 : Expr 1 = BVar FZ
      idLam : ClosedExpr = Lam (Str "x" Anonymous) Default nat (BVar FZ)
      piTy : ClosedExpr = Pi (Str "x" Anonymous) Default nat (weaken1 nat)
      constLam : ClosedExpr = Lam (Str "x" Anonymous) Default nat
                                (Lam (Str "y" Anonymous) Default (weaken1 nat) (BVar (FS FZ)))
  in [ assertTCEq "openInfer: BVar in ctx has correct type" (inferTypeOpen env ctx1 bvar0) nat
     , assertTCEq "openInfer: λ(x:Nat).x : Nat -> Nat" (inferTypeOpen env emptyCtx idLam) piTy
     , assertTC "openInfer: Pi type has Sort type" (inferTypeOpen env emptyCtx piTy) (\ty => case ty of Sort _ => True; _ => False)
     , assertTC "openInfer: nested lambda infers" (inferTypeOpen env emptyCtx constLam) (const True)
     ]

--------------------------------------------------------------------------------
-- Test: Proof Irrelevance
--------------------------------------------------------------------------------

testProofIrrelevance : List TestResult
testProofIrrelevance =
  let prop : ClosedExpr = Sort Zero
      pName = Str "P" Anonymous
      p : ClosedExpr = Const pName []
      pDecl = AxiomDecl pName prop []
      p1Name = Str "p1" Anonymous
      p2Name = Str "p2" Anonymous
      p1 : ClosedExpr = Const p1Name []
      p2 : ClosedExpr = Const p2Name []
      p1Decl = AxiomDecl p1Name p []
      p2Decl = AxiomDecl p2Name p []
      env = addDecl p2Decl $ addDecl p1Decl $ addDecl pDecl emptyEnv
      natName = Str "Nat" Anonymous
      nat : ClosedExpr = Const natName []
      natDecl = AxiomDecl natName (Sort (Succ Zero)) []
      n1Name = Str "n1" Anonymous
      n2Name = Str "n2" Anonymous
      n1 : ClosedExpr = Const n1Name []
      n2 : ClosedExpr = Const n2Name []
      n1Decl = AxiomDecl n1Name nat []
      n2Decl = AxiomDecl n2Name nat []
      env2 = addDecl n2Decl $ addDecl n1Decl $ addDecl natDecl env
  in [ assertTCEq "proofIrr: p1 == p2 (both proofs of Prop)" (isDefEq env p1 p2) True
     , assertTCEq "proofIrr: isProp(p1)" (isProp env p1) True
     , assertTCEq "proofIrr: n1 != n2 (Type, not Prop)" (isDefEq env2 n1 n2) False
     , assertTCEq "proofIrr: isProp(n1) = False" (isProp env2 n1) False
     ]

--------------------------------------------------------------------------------
-- Test: Quotient Reduction
--------------------------------------------------------------------------------

testQuotient : List TestResult
testQuotient =
  let natName = Str "Nat" Anonymous
      nat : ClosedExpr = Const natName []
      natDecl = AxiomDecl natName (Sort (Succ Zero)) []
      rName = Str "r" Anonymous
      rType : ClosedExpr = Pi (Str "_" Anonymous) Default nat
                             (Pi (Str "_" Anonymous) Default (weaken1 nat) (Sort Zero))
      r : ClosedExpr = Const rName []
      rDecl = AxiomDecl rName rType []
      betaName = Str "β" Anonymous
      beta : ClosedExpr = Const betaName []
      betaDecl = AxiomDecl betaName (Sort (Succ Zero)) []
      fName = Str "f" Anonymous
      fType : ClosedExpr = Pi (Str "_" Anonymous) Default nat (weaken1 beta)
      f : ClosedExpr = Const fName []
      fDecl = AxiomDecl fName fType []
      hName = Str "h" Anonymous
      h : ClosedExpr = Const hName []
      hDecl = AxiomDecl hName (Sort Zero) []
      aName = Str "a" Anonymous
      a : ClosedExpr = Const aName []
      aDecl = AxiomDecl aName nat []
      env0 = enableQuot emptyEnv
      env = addDecl aDecl $ addDecl hDecl $ addDecl fDecl $
            addDecl betaDecl $ addDecl rDecl $ addDecl natDecl env0
      quotMk : ClosedExpr = mkApp (Const (Str "mk" (Str "Quot" Anonymous)) [Succ Zero]) [nat, r, a]
      quotLift : ClosedExpr = mkApp (Const (Str "lift" (Str "Quot" Anonymous)) [Succ Zero, Succ Zero])
                                    [nat, r, beta, f, h, quotMk]
      expected = App f a
      envNoQuot = addDecl aDecl $ addDecl hDecl $ addDecl fDecl $
                  addDecl betaDecl $ addDecl rDecl $ addDecl natDecl emptyEnv
      motiveType : ClosedExpr = Sort Zero
      indH : ClosedExpr = Const (Str "indH" Anonymous) []
      indHDecl = AxiomDecl (Str "indH" Anonymous) (Sort Zero) []
      envWithIndH = addDecl indHDecl env
      quotInd : ClosedExpr = mkApp (Const (Str "ind" (Str "Quot" Anonymous)) [Succ Zero])
                                   [nat, r, motiveType, indH, quotMk]
      expectedInd = App indH a
  in [ assertTCEq "quot: Quot.lift f h (Quot.mk r a) => f a" (whnf env quotLift) expected
     , assertTCEq "quot: without quotInit, no reduction" (whnf envNoQuot quotLift) quotLift
     , assertTCEq "quot: Quot.ind h (Quot.mk r a) => h a" (whnf envWithIndH quotInd) expectedInd
     ]

--------------------------------------------------------------------------------
-- Test: Declaration Validation
--------------------------------------------------------------------------------

testDeclValidation : List TestResult
testDeclValidation =
  let natName = Str "Nat" Anonymous
      nat : ClosedExpr = Const natName []
      natDecl = AxiomDecl natName (Sort (Succ Zero)) []
      prop : ClosedExpr = Sort Zero
      env1 = addDecl natDecl emptyEnv
      uName = Str "u" Anonymous
      env2 = addDecl natDecl emptyEnv
      tName = Str "T" Anonymous
      tType : ClosedExpr = Sort (Succ Zero)
      tValue : ClosedExpr = Sort Zero
      wrongName = Str "wrong" Anonymous
      wrongType : ClosedExpr = Sort (Succ (Succ Zero))
      wrongValue : ClosedExpr = Sort Zero
      pName = Str "P" Anonymous
      p : ClosedExpr = Const pName []
      pDecl = AxiomDecl pName prop []
      env3 = addDecl pDecl emptyEnv
      proofName = Str "proofAxiom" Anonymous
      proofDecl = AxiomDecl proofName p []
      env4 = addDecl proofDecl env3
      proofConst : ClosedExpr = Const proofName []
      thmName = Str "myThm" Anonymous
  in [ assertTC "declValid: valid axiom" (addAxiomChecked emptyEnv natName (Sort (Succ Zero)) []) (const True)
     , assertTCFails "declValid: duplicate decl fails" (addAxiomChecked env1 natName (Sort (Succ Zero)) [])
     , assertTCFails "declValid: duplicate univ params fails" (checkNoDuplicateUnivParams [uName, uName])
     , assertTC "declValid: valid definition" (addDefChecked env2 tName tType tValue Abbrev Safe []) (const True)
     , assertTCFails "declValid: wrong value type fails" (addDefChecked env2 wrongName wrongType wrongValue Abbrev Safe [])
     , assertTC "declValid: valid theorem" (addThmChecked env4 thmName p proofConst []) (const True)
     , assertTCFails "declValid: theorem with non-Prop fails" (addThmChecked env2 (Str "badThm" Anonymous) nat (Const (Str "zero" Anonymous) []) [])
     , assertTC "declValid: addDeclChecked works" (addDeclChecked emptyEnv (AxiomDecl (Str "X" Anonymous) (Sort (Succ Zero)) [])) (const True)
     ]

--------------------------------------------------------------------------------
-- Test: Real Export File (IO-based)
--------------------------------------------------------------------------------

testRealExport : IO (List TestResult)
testRealExport = do
  result <- readFile "data/simple.export"
  case result of
    Left _ => pure []  -- Skip if file not found
    Right content => do
      case parseExport content of
        Left err => pure [MkTestResult "realExport: parse" False $ "Parse error: " ++ err]
        Right st => pure
          [ assert "realExport: parses without error" True
          ]

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main : IO ()
main = do
  args <- getArgs
  let opts = parseArgs args

  -- Collect IO-based test results
  realExportResults <- testRealExport

  -- All test groups
  let groups =
        [ ("Lexer", testLexer)
        , ("Parser", testParser)
        , ("Expr", testExpr)
        , ("WHNF", testWhnf)
        , ("InferType", testInferType)
        , ("IsDefEq", testIsDefEq)
        , ("Delta", testDelta)
        , ("Eta", testEta)
        , ("Iota", testIota)
        , ("OpenInfer", testOpenInfer)
        , ("ProofIrrelevance", testProofIrrelevance)
        , ("Quotient", testQuotient)
        , ("DeclValidation", testDeclValidation)
        , ("RealExport", realExportResults)
        ]

  runTests opts groups
