module Main

import Lean4Idris
import Lean4Idris.Export.Token
import Lean4Idris.Export.Parser
import Lean4Idris.Export.Lexer
import Lean4Idris.Pretty

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

main : IO ()
main = do
  putStrLn "Lean4Idris Test Suite"
  putStrLn "=====================\n"

  testLexer
  testParser
  testExpr

  putStrLn "\n\nAll tests completed!"
