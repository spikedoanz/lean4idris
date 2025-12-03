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

||| Test lexer on simple input
testLexer : IO ()
testLexer = do
  putStrLn "=== Testing Lexer ==="
  let input = "1 #NS 0 Nat\n2 #NS 0 zero\n"
  case lexToTokens input of
    Left err => putStrLn $ "Lexer error: " ++ err
    Right toks => do
      putStrLn $ "Tokens: " ++ show (length toks) ++ " tokens"
      for_ toks $ \tok => putStrLn $ "  " ++ show tok

||| Test parser on simple input
testParser : IO ()
testParser = do
  putStrLn "\n=== Testing Parser ==="
  -- Sample export with version, names, levels, and expressions
  let input = "0.0.0\n1 #NS 0 Nat\n2 #NS 0 zero\n3 #NS 1 succ\n1 #US 0\n1 #ES 1\n2 #EC 1\n3 #EC 2\n"
  case parseExport input of
    Left err => putStrLn $ "Parser error: " ++ err
    Right st => do
      putStrLn "Parsed successfully!"
      putStrLn "\nNames:"
      for_ (getNames st) $ \(idx, name) =>
        putStrLn $ "  " ++ show idx ++ " => " ++ show name
      putStrLn "\nLevels:"
      for_ (getLevels st) $ \(idx, lvl) =>
        putStrLn $ "  " ++ show idx ++ " => " ++ ppLevel lvl
      putStrLn "\nExpressions:"
      for_ (getExprs st) $ \(idx, expr) =>
        putStrLn $ "  " ++ show idx ++ " => " ++ ppClosedExpr expr

||| Test expression construction
testExpr : IO ()
testExpr = do
  putStrLn "\n=== Testing Expression Construction ==="
  -- Build: Sort 1 (Type 1)
  let ty : ClosedExpr = Sort (Succ Zero)
  putStrLn $ "Sort 1: " ++ ppClosedExpr ty

  -- Build: Const Nat []
  let nat : ClosedExpr = Const (Str "Nat" Anonymous) []
  putStrLn $ "Nat: " ++ ppClosedExpr nat

  -- Build: App (Const succ) (Const zero)
  let succName = Str "succ" (Str "Nat" Anonymous)
  let zeroName = Str "zero" (Str "Nat" Anonymous)
  let succZero : ClosedExpr = App (Const succName []) (Const zeroName [])
  putStrLn $ "Nat.succ Nat.zero: " ++ ppClosedExpr succZero

||| Test WHNF reduction (beta and let)
testWhnf : IO ()
testWhnf = do
  putStrLn "\n=== Testing WHNF ==="
  let env = emptyEnv

  -- Test 1: Sort is already in WHNF
  let sort1 : ClosedExpr = Sort (Succ Zero)
  putStrLn $ "Sort 1 reduces to: " ++ show (whnf env sort1)

  -- Test 2: Beta reduction - (λx:T. x) v → v
  -- Build: (\x : Nat. x) Nat.zero
  let nat : ClosedExpr = Const (Str "Nat" Anonymous) []
  let zeroName = Str "zero" (Str "Nat" Anonymous)
  let zero : ClosedExpr = Const zeroName []
  -- Identity lambda: λ(x : Nat). x
  -- Body is BVar FZ which refers to x (index 0)
  let idBody : Expr 1 = BVar FZ
  let idLam : ClosedExpr = Lam (Str "x" Anonymous) Default nat idBody
  let app : ClosedExpr = App idLam zero
  putStrLn $ "Before: " ++ ppClosedExpr app
  case whnf env app of
    Left err => putStrLn $ "Error: " ++ show err
    Right result => putStrLn $ "After:  " ++ ppClosedExpr result

  -- Test 3: Let substitution
  -- let x = zero in x → zero
  let letExpr : ClosedExpr = Let (Str "x" Anonymous) nat zero (BVar FZ)
  putStrLn $ "\nBefore: let x = zero in x"
  case whnf env letExpr of
    Left err => putStrLn $ "Error: " ++ show err
    Right result => putStrLn $ "After:  " ++ ppClosedExpr result

||| Test type inference
testInferType : IO ()
testInferType = do
  putStrLn "\n=== Testing Type Inference ==="
  let env = emptyEnv

  -- Test 1: Type of Sort 0 is Sort 1
  let sort0 : ClosedExpr = Sort Zero
  putStrLn $ "Type of Sort 0: " ++ show (inferType env sort0)

  -- Test 2: Type of Sort u is Sort (u+1)
  let sort1 : ClosedExpr = Sort (Succ Zero)
  putStrLn $ "Type of Sort 1: " ++ show (inferType env sort1)

  -- Test 3: Type of a nat literal is Nat
  let natLit : ClosedExpr = NatLit 42
  putStrLn $ "Type of 42: " ++ show (inferType env natLit)

||| Test definitional equality
testIsDefEq : IO ()
testIsDefEq = do
  putStrLn "\n=== Testing Definitional Equality ==="
  let env = emptyEnv

  -- Test 1: Syntactically equal expressions
  let nat : ClosedExpr = Const (Str "Nat" Anonymous) []
  putStrLn $ "Nat == Nat: " ++ show (isDefEq env nat nat)

  -- Test 2: Same Sort
  let sort1 : ClosedExpr = Sort (Succ Zero)
  let sort1' : ClosedExpr = Sort (Succ Zero)
  putStrLn $ "Sort 1 == Sort 1: " ++ show (isDefEq env sort1 sort1')

  -- Test 3: Different Sorts
  let sort0 : ClosedExpr = Sort Zero
  putStrLn $ "Sort 0 == Sort 1: " ++ show (isDefEq env sort0 sort1)

  -- Test 4: Beta-equivalent expressions
  -- (λx. x) y == y
  let y : ClosedExpr = Const (Str "y" Anonymous) []
  let idBody : Expr 1 = BVar FZ
  let idLam : ClosedExpr = Lam (Str "x" Anonymous) Default nat idBody
  let appIdY : ClosedExpr = App idLam y
  putStrLn $ "(λx. x) y == y: " ++ show (isDefEq env appIdY y)

||| Test delta reduction (constant unfolding)
testDelta : IO ()
testDelta = do
  putStrLn "\n=== Testing Delta Reduction ==="

  -- Create an environment with a definition:
  -- def myId : Nat -> Nat := λx. x
  let nat : ClosedExpr = Const (Str "Nat" Anonymous) []
  let natInBody : Expr 1 = Const (Str "Nat" Anonymous) []  -- Nat lifted to scope depth 1
  let idBody : Expr 1 = BVar FZ  -- λx. x (body returns the bound var)
  let idLam : ClosedExpr = Lam (Str "x" Anonymous) Default nat idBody
  let idType : ClosedExpr = Pi (Str "x" Anonymous) Default nat natInBody  -- Nat -> Nat

  let myIdName = Str "myId" Anonymous
  let myIdDecl = DefDecl myIdName idType idLam Abbrev Safe []

  let env = addDecl myIdDecl emptyEnv

  -- Test 1: myId should unfold to λx. x
  let myIdRef : ClosedExpr = Const myIdName []
  putStrLn $ "myId: " ++ ppClosedExpr myIdRef
  case whnf env myIdRef of
    Left err => putStrLn $ "Error: " ++ show err
    Right result => putStrLn $ "whnf(myId): " ++ ppClosedExpr result

  -- Test 2: myId zero should reduce to zero
  let zeroName = Str "zero" (Str "Nat" Anonymous)
  let zero : ClosedExpr = Const zeroName []
  let myIdZero : ClosedExpr = App myIdRef zero
  putStrLn $ "\nmyId zero: " ++ ppClosedExpr myIdZero
  case whnf env myIdZero of
    Left err => putStrLn $ "Error: " ++ show err
    Right result => putStrLn $ "whnf(myId zero): " ++ ppClosedExpr result

  -- Test 3: myId zero == zero via delta + beta
  putStrLn $ "\nmyId zero == zero: " ++ show (isDefEq env myIdZero zero)

  -- Test 4: Opaque definitions don't unfold
  let opaqueIdDecl = DefDecl (Str "opaqueId" Anonymous) idType idLam Opaq Safe []
  let envWithOpaque = addDecl opaqueIdDecl env
  let opaqueIdRef : ClosedExpr = Const (Str "opaqueId" Anonymous) []
  putStrLn $ "\nopaqueId (opaque): " ++ ppClosedExpr opaqueIdRef
  case whnf envWithOpaque opaqueIdRef of
    Left err => putStrLn $ "Error: " ++ show err
    Right result => putStrLn $ "whnf(opaqueId): " ++ ppClosedExpr result ++ " (unchanged)"

||| Test eta expansion
testEta : IO ()
testEta = do
  putStrLn "\n=== Testing Eta Expansion ==="

  -- We need an environment with myId defined so we can get its type
  let nat : ClosedExpr = Const (Str "Nat" Anonymous) []
  let natInBody : Expr 1 = Const (Str "Nat" Anonymous) []
  let idBody : Expr 1 = BVar FZ
  let idLam : ClosedExpr = Lam (Str "x" Anonymous) Default nat idBody
  let idType : ClosedExpr = Pi (Str "x" Anonymous) Default nat natInBody

  let myIdName = Str "myId" Anonymous
  let myIdDecl = DefDecl myIdName idType idLam Abbrev Safe []
  let env = addDecl myIdDecl emptyEnv

  -- Test 1: λx. myId x == myId  (eta equivalence)
  -- myId has type Nat -> Nat, and λx. myId x should be eta-equivalent to myId
  let myIdRef : ClosedExpr = Const myIdName []
  -- Build: λx. myId x
  let etaExpanded : ClosedExpr = Lam (Str "x" Anonymous) Default nat (App (weaken1 myIdRef) (BVar FZ))

  putStrLn $ "λx. myId x: " ++ ppClosedExpr etaExpanded
  putStrLn $ "myId:       " ++ ppClosedExpr myIdRef
  putStrLn $ "λx. myId x == myId: " ++ show (isDefEq env etaExpanded myIdRef)

  -- Test 2: The other direction should also work
  putStrLn $ "myId == λx. myId x: " ++ show (isDefEq env myIdRef etaExpanded)

  -- Test 3: λx. f x == f for an axiom f : Nat -> Nat
  let fName = Str "f" Anonymous
  let fDecl = AxiomDecl fName idType []  -- f : Nat -> Nat (axiom, no value)
  let envWithF = addDecl fDecl emptyEnv

  let fRef : ClosedExpr = Const fName []
  let fEtaExpanded : ClosedExpr = Lam (Str "x" Anonymous) Default nat (App (weaken1 fRef) (BVar FZ))

  putStrLn $ "\nλx. f x == f (axiom): " ++ show (isDefEq envWithF fEtaExpanded fRef)

||| Test iota reduction (recursor reduction)
testIota : IO ()
testIota = do
  putStrLn "\n=== Testing Iota Reduction ==="

  -- Set up a simple inductive type: Nat
  -- inductive Nat : Type where
  --   | zero : Nat
  --   | succ : Nat → Nat

  let natName = Str "Nat" Anonymous
  let zeroName = Str "zero" (Str "Nat" Anonymous)
  let succName = Str "succ" (Str "Nat" Anonymous)
  let recName = Str "rec" (Str "Nat" Anonymous)

  -- Nat : Type 0
  let natType : ClosedExpr = Sort (Succ Zero)
  let natConst : ClosedExpr = Const natName []

  -- zero : Nat
  let zeroType : ClosedExpr = natConst

  -- succ : Nat → Nat
  let natInBody : Expr 1 = Const natName []
  let succType : ClosedExpr = Pi (Str "n" Anonymous) Default natConst natInBody

  -- Create the inductive info
  let natIndInfo = MkInductiveInfo
        natName
        natType
        0  -- numParams
        0  -- numIndices
        [ MkConstructorInfo zeroName zeroType
        , MkConstructorInfo succName succType ]
        True   -- isRecursive
        False  -- isReflexive

  -- Recursor: Nat.rec
  -- Type: (motive : Nat → Sort u) → motive Nat.zero → ((n : Nat) → motive n → motive (Nat.succ n)) → (t : Nat) → motive t
  --
  -- Reduction rules:
  --   Nat.rec motive hz hs Nat.zero => hz
  --   Nat.rec motive hz hs (Nat.succ n) => hs n (Nat.rec motive hz hs n)
  --
  -- The rhs in each rule is already abstracted over params, motives, minors, and ctor fields

  -- For zero rule: no ctor fields, rhs should be λmotive.λhz.λhs. hz
  -- In de Bruijn: λ.λ.λ. BVar 1  (hz is at index 1)
  -- Actually, looking at lean4lean, the rhs is already abstracted but when applied,
  -- we apply: (params, motives, minors) then (ctor fields) then (remaining args)
  -- So rhs for zero: should evaluate to hz when given motive, hz, hs

  -- Build: λmotive.λhz.λhs. hz
  let zeroRhs : ClosedExpr =
        let motiveTy : ClosedExpr = Pi (Str "_" Anonymous) Default natConst (Sort (Succ Zero))
            motive1 : Expr 1 = BVar FZ
            hzTy1 : Expr 1 = App motive1 (Const zeroName [])
        in Lam (Str "motive" Anonymous) Default motiveTy
             (Lam (Str "hz" Anonymous) Default hzTy1
               (Lam (Str "hs" Anonymous) Default (Sort Zero)  -- placeholder type
                 (BVar (FS FZ))))  -- hz

  let zeroRule = MkRecursorRule zeroName 0 zeroRhs

  -- Recursor type (simplified for testing)
  let recType : ClosedExpr = Sort Zero  -- placeholder, not used in iota reduction

  let natRecInfo = MkRecursorInfo
        recName
        recType
        0  -- numParams
        0  -- numIndices
        1  -- numMotives
        2  -- numMinors (zero case and succ case)
        [zeroRule]
        False  -- isK

  -- Create environment with Nat, zero, succ, and rec
  let env0 = emptyEnv
  let env1 = addDecl (IndDecl natIndInfo []) env0
  let env2 = addDecl (CtorDecl zeroName zeroType natName 0 0 0 []) env1
  let env3 = addDecl (CtorDecl succName succType natName 1 0 1 []) env2
  let env4 = addDecl (RecDecl natRecInfo []) env3

  putStrLn $ "Environment set up with Nat, zero, succ, rec"

  -- Test: Nat.rec motive hz hs Nat.zero should reduce to hz
  -- Build: rec motive hz hs zero
  let motive : ClosedExpr = Lam (Str "_" Anonymous) Default natConst (Sort (Succ Zero))
  let hz : ClosedExpr = Sort Zero  -- our "zero result"
  let hs : ClosedExpr = Lam (Str "n" Anonymous) Default natConst
                          (Lam (Str "ih" Anonymous) Default (Sort (Succ Zero)) (BVar FZ))
  let zero : ClosedExpr = Const zeroName []

  let recApp = App (App (App (App (Const recName []) motive) hz) hs) zero

  putStrLn $ "Test 1: rec motive hz hs zero => hz"
  putStrLn $ "  before: " ++ ppClosedExpr recApp
  case whnf env4 recApp of
    Left err => putStrLn $ "  error: " ++ show err
    Right result => do
      putStrLn $ "  after:  " ++ ppClosedExpr result
      putStrLn $ "  correct: " ++ show (result == hz)

  -- Test 2: Add succ rule and test succ case
  -- For succ rule: ctor has 1 field (n : Nat), rhs should be λmotive.λhz.λhs.λn.λih. hs n ih
  -- where ih is the recursive call result
  -- But for simplicity, let's just test the structure is right by having hs return a known value

  -- Create succ rule: λmotive.λhz.λhs.λn. hs n (placeholder for ih)
  -- For testing, let's make rhs = λmotive.λhz.λhs.λn. Sort 1  (always returns Sort 1)
  let succRhs : ClosedExpr =
        let motiveTy : ClosedExpr = Pi (Str "_" Anonymous) Default natConst (Sort (Succ Zero))
            motive1 : Expr 1 = BVar FZ
            hzTy1 : Expr 1 = App motive1 (Const zeroName [])
        in Lam (Str "motive" Anonymous) Default motiveTy
             (Lam (Str "hz" Anonymous) Default hzTy1
               (Lam (Str "hs" Anonymous) Default (Sort Zero)
                 (Lam (Str "n" Anonymous) Default (weaken1 (weaken1 (weaken1 natConst)))
                   (Sort (Succ Zero)))))  -- always returns Sort 1

  let succRule = MkRecursorRule succName 1 succRhs  -- 1 field (n)

  let natRecInfoWithSucc = MkRecursorInfo
        recName
        recType
        0  -- numParams
        0  -- numIndices
        1  -- numMotives
        2  -- numMinors
        [zeroRule, succRule]
        False  -- isK

  let env5 = addDecl (RecDecl natRecInfoWithSucc []) env3  -- override recursor

  -- Build: rec motive hz hs (succ zero)
  let one : ClosedExpr = App (Const succName []) (Const zeroName [])
  let recAppSucc = App (App (App (App (Const recName []) motive) hz) hs) one

  putStrLn $ "\nTest 2: rec motive hz hs (succ zero) => Sort 1"
  putStrLn $ "  before: " ++ ppClosedExpr recAppSucc
  case whnf env5 recAppSucc of
    Left err => putStrLn $ "  error: " ++ show err
    Right result => do
      putStrLn $ "  after:  " ++ ppClosedExpr result
      putStrLn $ "  correct: " ++ show (result == Sort (Succ Zero))

main : IO ()
main = do
  putStrLn "Lean4Idris Test Suite"
  putStrLn "=====================\n"

  testLexer
  testParser
  testExpr
  testWhnf
  testInferType
  testIsDefEq
  testDelta
  testEta
  testIota

  putStrLn "\n\nAll tests completed!"
