module FuzzRunner

import Lean4Idris
import Lean4Idris.Export.Token
import Lean4Idris.Export.Parser
import Lean4Idris.Export.Lexer
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import System.File
import System.Directory
import Data.List
import Data.String

||| Result of running a fuzz test
data FuzzResult
  = ParseError String
  | TypeCheckError String
  | Accepted
  | Crash String

Show FuzzResult where
  show (ParseError _) = "PARSE_ERROR"
  show (TypeCheckError _) = "TYPECHECK_ERROR"
  show Accepted = "ACCEPTED"
  show (Crash e) = "CRASH: " ++ e

||| Run a single export file
runFuzz : String -> IO FuzzResult
runFuzz content = do
  case parseExport content of
    Left err => pure $ ParseError err
    Right st => do
      let decls = getDecls st
      checkDecls emptyEnv decls
  where
    checkDecls : TCEnv -> List Declaration -> IO FuzzResult
    checkDecls env [] = pure Accepted
    checkDecls env (d :: ds) =
      case addDeclChecked env d of
        Left err => pure $ TypeCheckError (show err)
        Right env' => checkDecls env' ds

||| Run all .export files in a directory
runFuzzDir : String -> IO ()
runFuzzDir dir = do
  Right entries <- listDir dir
    | Left err => putStrLn $ "Error listing directory: " ++ show err
  let exports = filter (\f => isSuffixOf ".export" f) entries
  results <- traverse (\f => runOne (dir ++ "/" ++ f)) exports
  let crashes = filter isCrash results
  putStrLn $ "Total: " ++ show (length results)
  putStrLn $ "Crashes: " ++ show (length crashes)
  when (not (null crashes)) $ do
    putStrLn "CRASH DETAILS:"
    traverse_ (\(f, r) => putStrLn $ "  " ++ f ++ ": " ++ show r) crashes
  where
    isCrash : (String, FuzzResult) -> Bool
    isCrash (_, Crash _) = True
    isCrash _ = False

    runOne : String -> IO (String, FuzzResult)
    runOne path = do
      Right content <- readFile path
        | Left err => pure (path, Crash ("read error: " ++ show err))
      result <- runFuzz content
      pure (path, result)

main : IO ()
main = do
  putStrLn "Running fuzz tests..."
  runFuzzDir "test/redteam/fuzz"
