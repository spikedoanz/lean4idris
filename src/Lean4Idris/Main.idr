||| CLI entry point for lean4idris type checker
module Lean4Idris.Main

import Lean4Idris
import Lean4Idris.Export.Parser
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import Lean4Idris.Cache
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

||| Check all declarations in IO (with progress output and caching)
||| If continueOnError is True, continues checking after failures and reports summary
covering
checkAllDeclsIO : (fuel : Nat) -> (continueOnError : Bool) -> (verbose : Bool) -> TCEnv -> List Declaration -> CacheState -> (passed : Nat) -> (failed : Nat) -> (timedOut : Nat) -> (cached : Nat) -> (errors : List String) -> IO (Either String TCEnv, CacheState)
checkAllDeclsIO _ _ verbose env [] cache passed failed timedOut cached errors =
  let totalDecls : Nat = passed + failed + timedOut + cached
      pct : Double = if totalDecls == 0 then 100.0
                       else (cast (passed + cached) / cast totalDecls) * 100.0
      -- Round to 1 decimal place
      pctRounded : Double = (fromInteger $ cast {to=Integer} (pct * 10.0)) / 10.0
  in do
      when verbose $ do
        putStrLn ""
        putStrLn "=== Errors encountered ==="
        traverse_ putStrLn (reverse errors)
      putStrLn ""
      -- Parsable format: TOTAL n OK n FAIL n TIMEOUT n CACHED n OK% pct
      putStrLn $ "TOTAL " ++ show totalDecls ++ " OK " ++ show passed ++ " FAIL " ++ show failed ++ " TIMEOUT " ++ show timedOut ++ " CACHED " ++ show cached ++ " OK% " ++ show pctRounded
      if failed > 0 || timedOut > 0
        then pure (Left $ show (failed + timedOut) ++ " declarations failed", cache)
        else pure (Right env, cache)
checkAllDeclsIO fuel cont verbose env (d :: ds) cache passed failed timedOut cached errors = do
  let name = maybe "<anonymous>" show (declName d)
  -- Check if declaration is cached
  if isCached name cache
    then do
      putStr $ "Checking: " ++ name ++ "... "
      flushStdout
      putStrLn "[cached] ok"
      -- Add declaration to env without type checking
      let env' = addDecl d env
      checkAllDeclsIO fuel cont verbose env' ds cache passed failed timedOut (S cached) errors
    else do
      putStr $ "Checking: " ++ name ++ "... "
      flushStdout
      case runTCWithFuel fuel (addDeclChecked env d) of
        Left FuelExhausted => do
          putStrLn "TIMEOUT"
          let errMsg = "fuel exhausted (in " ++ name ++ ")"
          if cont
            then checkAllDeclsIO fuel cont verbose env ds cache passed failed (S timedOut) cached (errMsg :: errors)
            else pure (Left errMsg, cache)
        Left err => do
          putStrLn "FAIL"
          let errMsg = show err ++ " (in " ++ name ++ ")"
          if cont
            then checkAllDeclsIO fuel cont verbose env ds cache passed (S failed) timedOut cached (errMsg :: errors)
            else pure (Left errMsg, cache)
        Right env' => do
          putStrLn "ok"
          -- Add to cache on success
          let cache' = addPassed name cache
          checkAllDeclsIO fuel cont verbose env' ds cache' (S passed) failed timedOut cached errors

||| CLI options
record Options where
  constructor MkOptions
  eager : Bool  -- Stop on first error (default: continue)
  verbose : Bool
  noCache : Bool  -- Disable caching
  fuel : Maybe Nat
  files : List String

defaultOptions : Options
defaultOptions = MkOptions False False False Nothing []

||| Parse command line arguments
parseArgs : List String -> Options
parseArgs [] = defaultOptions
parseArgs ("--eager" :: rest) = { eager := True } (parseArgs rest)
parseArgs ("-e" :: rest) = { eager := True } (parseArgs rest)
parseArgs ("--fuel" :: n :: rest) = { fuel := parsePositive n } (parseArgs rest)
parseArgs ("-f" :: n :: rest) = { fuel := parsePositive n } (parseArgs rest)
parseArgs ("--verbose" :: rest) = { verbose := True } (parseArgs rest)
parseArgs ("-v" :: rest) = { verbose := True } (parseArgs rest)
parseArgs ("--no-cache" :: rest) = { noCache := True } (parseArgs rest)
parseArgs (arg :: rest) = { files $= (arg ::) } (parseArgs rest)

||| Main entry point
covering
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
          -- Compute export file hash for caching
          let exportHash = simpleHash content
          -- Load cache if caching is enabled
          cache <- if opts.noCache
                     then pure (initCache exportHash)
                     else do
                       maybeCache <- loadCache path exportHash
                       case maybeCache of
                         Just c => do
                           putStrLn $ "Cache loaded: " ++ show (cacheSize c) ++ " declarations"
                           pure c
                         Nothing => do
                           putStrLn "No cache found or hash mismatch, starting fresh"
                           pure (initCache exportHash)
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
              when opts.noCache $ putStrLn "(caching disabled)"
              let continueOnError = not opts.eager
              (result, finalCache) <- checkAllDeclsIO fuel continueOnError opts.verbose emptyEnv decls cache 0 0 0 0 []
              -- Save cache unless disabled
              unless opts.noCache $ do
                saveCache path finalCache
                putStrLn $ "Cache saved: " ++ show (cacheSize finalCache) ++ " declarations"
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
      putStrLn "  --no-cache           Disable caching"
      putStrLn ""
      putStrLn "Exit codes:"
      putStrLn "  0 - All declarations type-checked successfully"
      putStrLn "  1 - Parse error or type error"
      exitWith (ExitFailure 2)
