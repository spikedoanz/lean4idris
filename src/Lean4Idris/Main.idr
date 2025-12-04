||| CLI entry point for lean4idris type checker
module Lean4Idris.Main

import Lean4Idris
import Lean4Idris.Export.Parser
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import System.File
import System
import Data.List
import System.FFI

||| Check all declarations in order, with verbose output
checkAllDeclsVerbose : TCEnv -> List Declaration -> List String -> Either (String, List String) ()
checkAllDeclsVerbose env [] _ = Right ()
checkAllDeclsVerbose env (d :: ds) checked =
  let name = show (declName d)
  in case addDeclChecked env d of
    Left err => Left (show err ++ " (in " ++ name ++ ")", reverse (name :: checked))
    Right env' => checkAllDeclsVerbose env' ds (name :: checked)

||| Check all declarations in order
checkAllDecls : TCEnv -> List Declaration -> Either String ()
checkAllDecls env [] = Right ()
checkAllDecls env (d :: ds) =
  case addDeclChecked env d of
    Left err => Left (show err)
    Right env' => checkAllDecls env' ds

%foreign "C:fflush,libc"
prim__fflush : AnyPtr -> PrimIO Int

flushStdout : IO ()
flushStdout = do
  _ <- primIO $ prim__fflush prim__getNullAnyPtr
  pure ()

||| Check all declarations in IO (with progress output)
checkAllDeclsIO : TCEnv -> List Declaration -> IO (Either String TCEnv)
checkAllDeclsIO env [] = pure (Right env)
checkAllDeclsIO env (d :: ds) = do
  let name = show (declName d)
  putStr $ "Checking: " ++ name ++ "... "
  flushStdout
  case addDeclChecked env d of
    Left err => do
      putStrLn "FAIL"
      pure (Left (show err ++ " (in " ++ name ++ ")"))
    Right env' => do
      putStrLn "ok"
      checkAllDeclsIO env' ds

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
              putStr "Getting declarations... "
              flushStdout
              let decls = getDecls st
              putStrLn $ show (length decls) ++ " found"
              result <- checkAllDeclsIO emptyEnv decls
              case result of
                Left err => do
                  putStrLn $ "Type error: " ++ err
                  exitWith (ExitFailure 1)
                Right _ => do
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
