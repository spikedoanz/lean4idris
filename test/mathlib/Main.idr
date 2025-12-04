module Main

import Lean4Idris
import Lean4Idris.Export.Token
import Lean4Idris.Export.Parser
import Lean4Idris.Export.Lexer
import Lean4Idris.Pretty
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import System.File
import System
import Data.List
import Data.String

||| Result of running a typecheck
data CheckResult
  = ParseError String          -- Failed to parse
  | TypeCheckError String      -- Type checking failed
  | Accepted                   -- Type checker accepted all declarations
  | Timeout                    -- Hit fuel limit
  | Crash String               -- Unexpected crash/error

Show CheckResult where
  show (ParseError e) = "PARSE_ERROR: " ++ e
  show (TypeCheckError e) = "TYPECHECK_ERROR: " ++ e
  show Accepted = "ACCEPTED"
  show Timeout = "TIMEOUT"
  show (Crash e) = "CRASH: " ++ e

||| Check all declarations in order
checkAllDecls : TCEnv -> List Declaration -> Either String ()
checkAllDecls env [] = Right ()
checkAllDecls env (d :: ds) =
  case addDeclChecked env d of
    Left err => Left (show err)
    Right env' => checkAllDecls env' ds

||| Run typechecker on an export file
runCheck : String -> String -> IO CheckResult
runCheck name content = do
  case parseExport content of
    Left err => pure $ ParseError err
    Right st => do
      let decls = getDecls st
      case checkAllDecls emptyEnv decls of
        Left err => pure $ TypeCheckError err
        Right () => pure Accepted

||| Get exit code for result
exitCode : CheckResult -> Int
exitCode Accepted = 0
exitCode _ = 1

||| Main entry point - accepts a file path argument
main : IO ()
main = do
  args <- getArgs
  case args of
    [_, path] => do
      result <- readFile path
      case result of
        Left err => do
          putStrLn $ "CRASH: Failed to read file: " ++ show err
          exitWith (ExitFailure 1)
        Right content => do
          let fileSize = length content
          putStrLn $ "File size: " ++ show fileSize ++ " bytes"

          -- Parse first to count declarations
          case parseExport content of
            Left err => do
              putStrLn $ show (ParseError err)
              exitWith (ExitFailure 1)
            Right st => do
              let decls = getDecls st
              putStrLn $ "Parsed " ++ show (length decls) ++ " declarations"
              putStrLn "Type checking..."

              checkResult <- runCheck path content
              putStrLn $ show checkResult

              exitWith (if exitCode checkResult == 0
                        then ExitSuccess
                        else ExitFailure 1)
    _ => do
      putStrLn "Usage: mathlib-check <export-file>"
      putStrLn ""
      putStrLn "Type-checks a Lean export file and reports the result."
      putStrLn ""
      putStrLn "Exit codes:"
      putStrLn "  0 - All declarations type-checked successfully"
      putStrLn "  1 - Parse error, type error, or other failure"
      exitWith (ExitFailure 2)
