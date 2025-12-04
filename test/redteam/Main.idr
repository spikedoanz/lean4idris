module Main

import Lean4Idris
import Lean4Idris.Export.Token
import Lean4Idris.Export.Parser
import Lean4Idris.Export.Lexer
import Lean4Idris.Pretty
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import System.File
import System.Directory
import Data.List
import Data.String

||| Result of running a red team test
data TestResult
  = ParseError String          -- Failed to parse (might be expected)
  | TypeCheckError String      -- Type checking failed (might be expected)
  | Accepted                   -- Type checker accepted the declarations
  | Timeout                    -- Hit fuel limit or similar
  | Crash String               -- Unexpected crash/error

Show TestResult where
  show (ParseError e) = "PARSE_ERROR: " ++ e
  show (TypeCheckError e) = "TYPECHECK_ERROR: " ++ e
  show Accepted = "ACCEPTED"
  show Timeout = "TIMEOUT"
  show (Crash e) = "CRASH: " ++ e

||| Run a single export file through parser and type checker
runTest : String -> String -> IO TestResult
runTest name content = do
  case parseExport content of
    Left err => pure $ ParseError err
    Right st => do
      let decls = getDecls st
      checkDecls emptyEnv decls
  where
    checkDecls : TCEnv -> List Declaration -> IO TestResult
    checkDecls env [] = pure Accepted
    checkDecls env (d :: ds) = do
      case addDeclChecked env d of
        Left err => pure $ TypeCheckError (show err)
        Right env' => checkDecls env' ds

||| Information about expected test behavior
record TestSpec where
  constructor MkTestSpec
  filename : String
  description : String
  expectedBehavior : String  -- "reject", "accept", "crash", "timeout"

||| Soundness tests - these should all be REJECTED
soundnessTests : List TestSpec
soundnessTests =
  [ MkTestSpec "01-circular-ref.export"
      "Circular expression references (expr 2 refs 3, expr 3 refs 2)"
      "reject"
  , MkTestSpec "02-free-bvar.export"
      "Axiom type contains free bound variable (BVar 0 at depth 0)"
      "reject"
  , MkTestSpec "03-bad-projection.export"
      "Projection with out-of-bounds field index (999)"
      "reject"
  , MkTestSpec "04-forward-ref.export"
      "Expression references undefined index (99)"
      "reject"
  , MkTestSpec "05-self-ref-def.export"
      "Definition value references itself (loop : Type := loop)"
      "reject"
  , MkTestSpec "06-deep-nesting.export"
      "Deeply nested applications to test fuel exhaustion"
      "reject"
  , MkTestSpec "07-type-mismatch-def.export"
      "Definition with value type not matching declared type (bad : Bool := Nat)"
      "reject"
  , MkTestSpec "08-universe-escape.export"
      "Type 0 : Type 1, but def claims Type0 : Prop"
      "reject"
  , MkTestSpec "09-fake-prop-proof.export"
      "Circular proof: False : Prop, proof : False := proof"
      "reject"
  , MkTestSpec "10-lambda-wrong-body-type.export"
      "Lambda body type doesn't match Pi codomain"
      "reject"
  , MkTestSpec "11-bvar-escape-lambda.export"
      "Lambda identity function (valid: BVar 0 refers to lambda param)"
      "accept"
  , MkTestSpec "12-pi-universe-wrong.export"
      "Pi type where codomain universe is wrong"
      "reject"
  , MkTestSpec "13-app-no-arg-check.export"
      "Application where arg type doesn't match domain (f Bool instead of f Nat)"
      "reject"
  ]

||| Run a single test and report results
runSingleTest : String -> TestSpec -> IO (String, TestResult, Bool)
runSingleTest dir spec = do
  let path = dir ++ "/" ++ spec.filename
  result <- readFile path
  case result of
    Left err => pure (spec.filename, Crash ("File read error: " ++ show err), False)
    Right content => do
      testResult <- runTest spec.filename content
      let passed = case (spec.expectedBehavior, testResult) of
            ("reject", TypeCheckError _) => True
            ("reject", ParseError _) => True
            ("accept", Accepted) => True
            ("crash", Crash _) => True
            ("timeout", Timeout) => True
            _ => False
      pure (spec.filename, testResult, passed)

||| Main test runner
main : IO ()
main = do
  putStrLn "======================================"
  putStrLn "  lean4idris Red Team Test Suite"
  putStrLn "======================================"
  putStrLn ""

  -- Run soundness tests
  putStrLn "## Soundness Tests"
  putStrLn "These tests should all be REJECTED by the type checker."
  putStrLn "If any are ACCEPTED, that's a soundness bug!"
  putStrLn ""

  soundnessResults <- traverse (runSingleTest "test/redteam/soundness") soundnessTests

  for_ (zip soundnessTests soundnessResults) $ \(spec, (name, result, passed)) => do
    let status = if passed then "[PASS]" else "[FAIL - SOUNDNESS BUG!]"
    putStrLn $ status ++ " " ++ name
    putStrLn $ "  Description: " ++ spec.description
    putStrLn $ "  Expected: " ++ spec.expectedBehavior
    putStrLn $ "  Actual: " ++ show result
    putStrLn ""

  -- Summary
  let totalTests = length soundnessResults
  let passedTests = length (filter (\(_, _, p) => p) soundnessResults)
  let failedTests = totalTests `minus` passedTests

  putStrLn "======================================"
  putStrLn "  Summary"
  putStrLn "======================================"
  putStrLn $ "Total: " ++ show totalTests
  putStrLn $ "Passed: " ++ show passedTests
  putStrLn $ "Failed: " ++ show failedTests

  when (failedTests > 0) $ do
    putStrLn ""
    putStrLn "!! SOUNDNESS BUGS DETECTED !!"
    putStrLn "The type checker accepted terms that should be rejected."
