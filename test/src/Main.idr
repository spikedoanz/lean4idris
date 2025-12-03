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

  putStrLn "\n\nAll tests completed!"
