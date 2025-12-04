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
  -- Historical bugs from lean4lean / Lean kernel
  , MkTestSpec "14-let-type-dependency.export"
      "Let binding where body depends on let-bound var type (lean4#10475 style)"
      "reject"
  , MkTestSpec "15-let-nested-escape.export"
      "Nested let bindings with escaping variables"
      "reject"
  , MkTestSpec "16-nat-literal-no-nat.export"
      "Nat literal used when Nat type not defined (primitive check)"
      "reject"
  , MkTestSpec "17-string-literal-no-string.export"
      "String literal used when String type not defined (primitive check)"
      "reject"
  , MkTestSpec "18-wrong-level-count.export"
      "Constant applied with wrong number of universe levels"
      "reject"
  , MkTestSpec "19-level-param-mismatch.export"
      "Definition uses level param not in its declared params"
      "reject"
  , MkTestSpec "20-quot-mk-fake.export"
      "Fake Quot.mk application without proper quotient setup"
      "reject"
  , MkTestSpec "21-eq-fake-refl.export"
      "Fake Eq.refl claiming equality of distinct values"
      "reject"
  , MkTestSpec "22-imax-zero-exploit.export"
      "Exploit imax(u, 0) = 0 to collapse universes"
      "reject"
  , MkTestSpec "23-large-bvar-index.export"
      "Lambda with BVar index larger than scope (index 999 in depth 1)"
      "reject"
  , MkTestSpec "24-recursor-wrong-major.export"
      "Recursor applied to wrong type as major premise"
      "reject"
  , MkTestSpec "25-proof-irrel-non-prop.export"
      "Attempt proof irrelevance on non-Prop types"
      "reject"
  , MkTestSpec "26-let-value-type-mismatch.export"
      "Let binding value type doesn't match declared type (let x : Bool := Nat.zero)"
      "reject"
  -- Extended attack surface tests
  , MkTestSpec "29-app-defequal-not-structural.export"
      "Application where types are def-equal but not structurally equal after whnf"
      "accept"
  , MkTestSpec "30-whnf-deep-beta.export"
      "Deeply nested beta reductions (15 levels) to test fuel limits"
      "accept"
  -- Advanced inductive/recursor attacks (red team round 2)
  , MkTestSpec "31-negative-occurrence.export"
      "Negative occurrence in inductive (Bad -> False in Bad.mk) enables Curry's paradox"
      "reject"
  , MkTestSpec "32-rec-rule-wrong-rhs-type.export"
      "Recursor rule RHS swapped (true case returns false case)"
      "reject"
  , MkTestSpec "33-rec-rule-arbitrary-rhs.export"
      "Recursor rule RHS is arbitrary expr (Sort 0 instead of minor premise)"
      "reject"
  , MkTestSpec "34-rec-fewer-rules.export"
      "Recursor has fewer rules than constructors (1 rule for 2-ctor Bool)"
      "reject"
  , MkTestSpec "35-ctor-wrong-return-type.export"
      "Constructor type returns B but registered as A constructor"
      "reject"
  , MkTestSpec "36-ctor-wrong-field-count.export"
      "Constructor claims 5 fields but type has 1"
      "reject"
  , MkTestSpec "37-ctor-wrong-inductive-name.export"
      "Constructor registered for wrong inductive (Bool.true for Nat)"
      "reject"
  , MkTestSpec "38-cross-inductive-iota.export"
      "Two inductives with same constructor name, try cross-confusion"
      "reject"
  , MkTestSpec "39-recursor-wrong-inductive.export"
      "Recursor for Unit has rules for Bool constructors"
      "reject"
  , MkTestSpec "40-ctor-universe-mismatch.export"
      "Constructor uses universe param v when inductive uses u"
      "reject"
  -- Round 3: Recursor validation and advanced attacks
  , MkTestSpec "41-rec-rule-rhs-untyped.export"
      "Recursor rule RHS is Sort 1 (Type) instead of proper term"
      "reject"
  , MkTestSpec "42-rec-rule-wrong-numfields.export"
      "Recursor rule declares wrong numFields (5 for succ which has 1)"
      "reject"
  , MkTestSpec "43-rec-missing-rule.export"
      "Recursor for Bool has only 1 rule (missing false case)"
      "reject"
  , MkTestSpec "44-proof-irrel-asymmetric.export"
      "Proof irrelevance only checks t is Prop, not s"
      "reject"
  , MkTestSpec "45-imax-param-unsimplified.export"
      "IMax with Param may not simplify correctly"
      "reject"
  , MkTestSpec "46-level-param-cyclic.export"
      "Level parameter in own type (valid: T.{u} : Sort (Max 0 u))"
      "accept"
  , MkTestSpec "47-rec-wrong-param-counts.export"
      "Recursor with wrong numParams/numMotives/numMinors (99 each)"
      "reject"
  -- Round 4: DefEq, quotients, projections, theorems
  , MkTestSpec "48-placeholder-collision.export"
      "isDefEqBody uses _x placeholder that can collide with user constant"
      "reject"
  , MkTestSpec "49-proj-wrong-struct-name.export"
      "Projection claims Triple but projects from Pair (wrong struct name)"
      "reject"
  , MkTestSpec "50-quot-no-validation.export"
      "QuotDecl enables quotient without validating Quot axioms exist"
      "reject"
  , MkTestSpec "51-theorem-unfold.export"
      "Theorem proofs unfold unconditionally (should be opaque)"
      "reject"
  , MkTestSpec "52-large-elimination.export"
      "Prop recursor eliminating to Type (large elimination)"
      "reject"
  , MkTestSpec "53-k-axiom-ignored.export"
      "Eq recursor with isK=True but K-axiom not enforced"
      "reject"
  , MkTestSpec "54-placeholder-collision-real.export"
      "Lambda body uses _x constant, collides with isDefEqBody placeholder"
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
