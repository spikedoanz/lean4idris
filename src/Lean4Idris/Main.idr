||| CLI entry point for lean4idris type checker
module Lean4Idris.Main

import Lean4Idris
import Lean4Idris.Export.Parser
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import System.File
import System
import Data.List

||| Check all declarations in order
checkAllDecls : TCEnv -> List Declaration -> Either String ()
checkAllDecls env [] = Right ()
checkAllDecls env (d :: ds) =
  case addDeclChecked env d of
    Left err => Left (show err)
    Right env' => checkAllDecls env' ds

||| Main entry point
main : IO ()
main = do
  args <- getArgs
  let args' = drop 1 args
  case args' of
    (path :: _) => do
      result <- readFile path
      case result of
        Left err => do
          putStrLn $ "Error: Failed to read file: " ++ show err
          exitWith (ExitFailure 1)
        Right content => do
          case parseExport content of
            Left err => do
              putStrLn $ "Parse error: " ++ err
              exitWith (ExitFailure 1)
            Right st => do
              let decls = getDecls st
              putStrLn $ "Parsed " ++ show (length decls) ++ " declarations"
              case checkAllDecls emptyEnv decls of
                Left err => do
                  putStrLn $ "Type error: " ++ err
                  exitWith (ExitFailure 1)
                Right () => do
                  putStrLn "OK"
                  exitWith ExitSuccess
    _ => do
      putStrLn "lean4idris - Type checker for Lean 4 export files"
      putStrLn ""
      putStrLn "Usage: lean4idris <export-file>"
      putStrLn ""
      putStrLn "Exit codes:"
      putStrLn "  0 - All declarations type-checked successfully"
      putStrLn "  1 - Parse error or type error"
      exitWith (ExitFailure 2)
