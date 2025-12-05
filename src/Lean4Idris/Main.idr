||| CLI entry point for lean4idris type checker
module Lean4Idris.Main

import Lean4Idris
import Lean4Idris.Export.Parser
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import System.File
import System
import Data.List
import Data.Maybe
import Data.String
import System.FFI

||| Check all declarations in order, with verbose output
checkAllDeclsVerbose : Nat -> TCEnv -> List Declaration -> List String -> Either (String, List String) ()
checkAllDeclsVerbose fuel env [] _ = Right ()
checkAllDeclsVerbose fuel env (d :: ds) checked =
  let name = show (declName d)
  in case runTCWithFuel fuel (addDeclChecked env d) of
    Left err => Left (show err ++ " (in " ++ name ++ ")", reverse (name :: checked))
    Right env' => checkAllDeclsVerbose fuel env' ds (name :: checked)

||| Check all declarations in order
checkAllDecls : Nat -> TCEnv -> List Declaration -> Either String ()
checkAllDecls fuel env [] = Right ()
checkAllDecls fuel env (d :: ds) =
  case runTCWithFuel fuel (addDeclChecked env d) of
    Left err => Left (show err)
    Right env' => checkAllDecls fuel env' ds

%foreign "C:fflush,libc"
prim__fflush : AnyPtr -> PrimIO Int

flushStdout : IO ()
flushStdout = do
  _ <- primIO $ prim__fflush prim__getNullAnyPtr
  pure ()

||| Check all declarations in IO (with progress output)
||| If continueOnError is True, continues checking after failures and reports summary
checkAllDeclsIO : (fuel : Nat) -> (continueOnError : Bool) -> (verbose : Bool) -> TCEnv -> List Declaration -> (passed : Nat) -> (failed : Nat) -> (timedOut : Nat) -> (errors : List String) -> IO (Either String TCEnv)
checkAllDeclsIO _ _ verbose env [] passed failed timedOut errors =
  let totalDecls : Nat = passed + failed + timedOut
      pct : Double = if totalDecls == 0 then 100.0
                       else (cast passed / cast totalDecls) * 100.0
      -- Round to 1 decimal place
      pctRounded : Double = (fromInteger $ cast {to=Integer} (pct * 10.0)) / 10.0
  in do
      when verbose $ do
        putStrLn ""
        putStrLn "=== Errors encountered ==="
        traverse_ putStrLn (reverse errors)
      putStrLn ""
      -- Parsable format: TOTAL n OK n FAIL n TIMEOUT n OK% pct
      putStrLn $ "TOTAL " ++ show totalDecls ++ " OK " ++ show passed ++ " FAIL " ++ show failed ++ " TIMEOUT " ++ show timedOut ++ " OK% " ++ show pctRounded
      if failed > 0 || timedOut > 0
        then pure (Left $ show (failed + timedOut) ++ " declarations failed")
        else pure (Right env)
checkAllDeclsIO fuel cont verbose env (d :: ds) passed failed timedOut errors = do
  let name = show (declName d)
  putStr $ "Checking: " ++ name ++ "... "
  flushStdout
  case runTCWithFuel fuel (addDeclChecked env d) of
    Left FuelExhausted => do
      putStrLn "TIMEOUT"
      let errMsg = "fuel exhausted (in " ++ name ++ ")"
      if cont
        then checkAllDeclsIO fuel cont verbose env ds passed failed (S timedOut) (errMsg :: errors)
        else pure (Left errMsg)
    Left err => do
      putStrLn "FAIL"
      let errMsg = show err ++ " (in " ++ name ++ ")"
      if cont
        then checkAllDeclsIO fuel cont verbose env ds passed (S failed) timedOut (errMsg :: errors)
        else pure (Left errMsg)
    Right env' => do
      putStrLn "ok"
      checkAllDeclsIO fuel cont verbose env' ds (S passed) failed timedOut errors

||| CLI options
record Options where
  constructor MkOptions
  eager : Bool  -- Stop on first error (default: continue)
  verbose : Bool
  fuel : Maybe Nat
  files : List String

defaultOptions : Options
defaultOptions = MkOptions False False Nothing []

||| Parse command line arguments
parseArgs : List String -> Options
parseArgs [] = defaultOptions
parseArgs ("--eager" :: rest) = { eager := True } (parseArgs rest)
parseArgs ("-e" :: rest) = { eager := True } (parseArgs rest)
parseArgs ("--fuel" :: n :: rest) = { fuel := parsePositive n } (parseArgs rest)
parseArgs ("-f" :: n :: rest) = { fuel := parsePositive n } (parseArgs rest)
parseArgs ("--verbose" :: rest) = { verbose := True } (parseArgs rest)
parseArgs ("-v" :: rest) = { verbose := True } (parseArgs rest)
parseArgs (arg :: rest) = { files $= (arg ::) } (parseArgs rest)

||| Main entry point
main : IO ()
main = do
  args <- getArgs
  let args' = drop 1 args
  let opts = parseArgs args'
  let fuel = fromMaybe defaultFuel opts.fuel
  case opts.files of
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
              when opts.eager $ putStrLn "(eager mode: stopping on first error)"
              when (isJust opts.fuel) $ putStrLn $ "(fuel: " ++ show fuel ++ ")"
              let continueOnError = not opts.eager
              result <- checkAllDeclsIO fuel continueOnError opts.verbose emptyEnv decls 0 0 0 []
              case result of
                Left err => do
                  when opts.verbose $ putStrLn $ "Type error: " ++ err
                  unless opts.verbose $ putStrLn "Type error (use -v to see details)"
                  exitWith (ExitFailure 1)
                Right _ => do
                  putStrLn "OK"
                  exitWith ExitSuccess
    _ => do
      putStrLn "lean4idris - Type checker for Lean 4 export files"
      putStrLn ""
      putStrLn "Usage: lean4idris [OPTIONS] <export-file>"
      putStrLn ""
      putStrLn "Options:"
      putStrLn "  -e, --eager          Stop on first error (default: continue all)"
      putStrLn "  -f, --fuel <amount>  Set fuel limit per declaration (default: 100000)"
      putStrLn "  -v, --verbose        Print full error details"
      putStrLn ""
      putStrLn "Exit codes:"
      putStrLn "  0 - All declarations type-checked successfully"
      putStrLn "  1 - Parse error or type error"
      exitWith (ExitFailure 2)
