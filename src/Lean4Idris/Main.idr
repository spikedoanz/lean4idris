||| CLI entry point for lean4idris type checker
module Lean4Idris.Main

import Lean4Idris
import Lean4Idris.Export.Parser
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import Lean4Idris.Cache
import System.File
import System
import System.Clock
import Data.List
import Data.Maybe
import Data.String
import Data.Bits
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

||| Simple FNV-1a hash for cache versioning
fnvHash : String -> Bits64
fnvHash s = foldl (\h, c => (h `xor` cast (ord c)) * 0x100000001b3) 0xcbf29ce484222325 (unpack s)

||| Compute version string from the binary
||| We hash the actual .so binary to detect changes
covering
computeVersion : IO String
computeVersion = do
  args <- getArgs
  case args of
    (binPath :: _) => do
      -- The wrapper script is at /path/to/bin/lean4idris
      -- The actual binary is at /path/to/bin/lean4idris_app/lean4idris.so
      -- But when run via chez, arg0 might be the .so directly
      let soPath = if isSuffixOf ".so" binPath
                     then binPath
                     else binPath ++ "_app/lean4idris.so"
      result <- readFile soPath
      case result of
        Right content => pure $ "lean4idris-" ++ show (fnvHash content)
        Left _ => pure "lean4idris-unknown"
    _ => pure "lean4idris-unknown"

||| Per-declaration stats for profiling
record DeclStats where
  constructor MkDeclStats
  name : String
  fuelUsed : Nat
  timeNs : Integer  -- nanoseconds
  status : String   -- "ok", "fail", "timeout", "cached"

||| Format stats as TSV line
formatStats : DeclStats -> String
formatStats s = s.name ++ "\t" ++ show s.fuelUsed ++ "\t" ++ show s.timeNs ++ "\t" ++ s.status

||| Get elapsed time in nanoseconds between two monotonic clocks
elapsedNs : Clock Monotonic -> Clock Monotonic -> Integer
elapsedNs start end = toNano end - toNano start
  where
    toNano : Clock Monotonic -> Integer
    toNano (MkClock s ns) = s * 1000000000 + ns

||| Check all declarations in IO (with progress output and caching)
||| If continueOnError is True, continues checking after failures and reports summary
covering
checkAllDeclsIO : (fuel : Nat) -> (continueOnError : Bool) -> (verbose : Bool) -> (profile : Bool) -> TCEnv -> List Declaration -> CacheState -> (passed : Nat) -> (failed : Nat) -> (timedOut : Nat) -> (cached : Nat) -> (errors : List String) -> (stats : List DeclStats) -> IO (Either String TCEnv, CacheState, List DeclStats)
checkAllDeclsIO _ _ verbose profile env [] cache passed failed timedOut cached errors stats =
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
      -- Output profiling stats if enabled
      when profile $ do
        putStrLn ""
        putStrLn "=== Profiling Stats (name\\tfuel_used\\ttime_ns\\tstatus) ==="
        traverse_ (putStrLn . formatStats) (reverse stats)
      putStrLn ""
      -- Parsable format: TOTAL n OK n FAIL n TIMEOUT n CACHED n OK% pct
      putStrLn $ "TOTAL " ++ show totalDecls ++ " OK " ++ show passed ++ " FAIL " ++ show failed ++ " TIMEOUT " ++ show timedOut ++ " CACHED " ++ show cached ++ " OK% " ++ show pctRounded
      if failed > 0 || timedOut > 0
        then pure (Left $ show (failed + timedOut) ++ " declarations failed", cache, reverse stats)
        else pure (Right env, cache, reverse stats)
checkAllDeclsIO fuel cont verbose profile env (d :: ds) cache passed failed timedOut cached errors stats = do
  let maybeName = declName d
  let name = maybe "<anonymous>" show maybeName
  -- Check if declaration is cached (skip anonymous declarations)
  if isJust maybeName && isCached name cache
    then do
      putStr $ "Checking: " ++ name ++ "... "
      flushStdout
      putStrLn "[cached] ok"
      -- Add declaration to env without type checking
      let env' = addDecl d env
      let stat = MkDeclStats name 0 0 "cached"
      checkAllDeclsIO fuel cont verbose profile env' ds cache passed failed timedOut (S cached) errors (stat :: stats)
    else do
      putStr $ "Checking: " ++ name ++ "... "
      flushStdout
      -- Time the type checking
      startTime <- clockTime Monotonic
      let result = runTCFuel fuel (addDeclChecked env d)
      endTime <- clockTime Monotonic
      let elapsed = elapsedNs startTime endTime
      case result of
        Left FuelExhausted => do
          putStrLn "TIMEOUT"
          let errMsg = "fuel exhausted (in " ++ name ++ ")"
          let stat = MkDeclStats name fuel elapsed "timeout"
          if cont
            then checkAllDeclsIO fuel cont verbose profile env ds cache passed failed (S timedOut) cached (errMsg :: errors) (stat :: stats)
            else pure (Left errMsg, cache, reverse (stat :: stats))
        Left err => do
          putStrLn "FAIL"
          let errMsg = show err ++ " (in " ++ name ++ ")"
          when verbose $ putStrLn $ "  Error: " ++ errMsg
          let stat = MkDeclStats name 0 elapsed "fail"  -- Can't know fuel used on error
          if cont
            then checkAllDeclsIO fuel cont verbose profile env ds cache passed (S failed) timedOut cached (errMsg :: errors) (stat :: stats)
            else pure (Left errMsg, cache, reverse (stat :: stats))
        Right (remainingFuel, env') => do
          putStrLn "ok"
          -- Add to cache on success (skip anonymous declarations)
          let cache' = if isJust maybeName then addPassed name cache else cache
          let fuelUsed = fuel `minus` remainingFuel
          let stat = MkDeclStats name fuelUsed elapsed "ok"
          checkAllDeclsIO fuel cont verbose profile env' ds cache' (S passed) failed timedOut cached errors (stat :: stats)

||| CLI options
record Options where
  constructor MkOptions
  eager : Bool  -- Stop on first error (default: continue)
  verbose : Bool
  noCache : Bool  -- Disable caching
  profile : Bool  -- Output per-declaration profiling stats
  fuel : Maybe Nat
  files : List String

defaultOptions : Options
defaultOptions = MkOptions False False False False Nothing []

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
parseArgs ("--profile" :: rest) = { profile := True } (parseArgs rest)
parseArgs ("-p" :: rest) = { profile := True } (parseArgs rest)
parseArgs (arg :: rest) = { files $= (arg ::) } (parseArgs rest)

||| Main entry point
covering
main : IO ()
main = do
  args <- getArgs
  let args' = drop 1 args
  let opts = parseArgs args'
  let fuel = fromMaybe defaultFuel opts.fuel
  -- Compute version hash from binary
  tcVersion <- computeVersion
  case opts.files of
    (path :: _) => do
      result <- readFile path
      case result of
        Left err => do
          putStrLn $ "Error: Failed to read file: " ++ show err
          exitWith (ExitFailure 1)
        Right content => do
          -- Load global cache if caching is enabled
          cache <- if opts.noCache
                     then pure (initCache tcVersion)
                     else do
                       maybeCache <- loadCache tcVersion
                       case maybeCache of
                         Just c => do
                           putStrLn $ "Global cache loaded: " ++ show (cacheSize c) ++ " declarations (version: " ++ tcVersion ++ ")"
                           pure c
                         Nothing => do
                           putStrLn $ "No cache found or version mismatch, starting fresh (version: " ++ tcVersion ++ ")"
                           pure (initCache tcVersion)
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
              when opts.profile $ putStrLn "(profiling enabled)"
              let continueOnError = not opts.eager
              (result, finalCache, _) <- checkAllDeclsIO fuel continueOnError opts.verbose opts.profile emptyEnv decls cache 0 0 0 0 [] []
              -- Save cache unless disabled
              unless opts.noCache $ do
                saveCache finalCache
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
      putStrLn "  -p, --profile        Output per-declaration fuel and timing stats"
      putStrLn ""
      putStrLn "Exit codes:"
      putStrLn "  0 - All declarations type-checked successfully"
      putStrLn "  1 - Parse error or type error"
      exitWith (ExitFailure 2)
