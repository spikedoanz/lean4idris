module Bench

import Lean4Idris
import Lean4Idris.Export.Parser
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import System.File
import System.Clock
import Data.List
import System

||| Benchmark a single export file
benchmarkExport : String -> IO ()
benchmarkExport path = do
  putStrLn $ "Checking: " ++ path

  -- Read file
  Right content <- readFile path
    | Left err => putStrLn $ "ERROR: Failed to read: " ++ show err

  -- Parse
  start <- clockTime Monotonic
  case parseExport content of
    Left err => putStrLn $ "PARSE_ERROR: " ++ err
    Right st => do
      parseEnd <- clockTime Monotonic

      let decls = getDecls st
      putStrLn $ "Parsed " ++ show (length decls) ++ " declarations"

      -- Type check
      checkStart <- clockTime Monotonic
      result <- checkDecls emptyEnv decls
      checkEnd <- clockTime Monotonic

      let parseTime = timeDiffNanos parseEnd start
      let checkTime = timeDiffNanos checkEnd checkStart
      let totalTime = timeDiffNanos checkEnd start

      case result of
        Left err => do
          putStrLn $ "TYPECHECK_ERROR: " ++ err
          putStrLn $ "Time: " ++ show (totalTime `div` 1000000) ++ "ms"
        Right _ => do
          putStrLn "OK"
          putStrLn $ "Parse time: " ++ show (parseTime `div` 1000000) ++ "ms"
          putStrLn $ "Check time: " ++ show (checkTime `div` 1000000) ++ "ms"
          putStrLn $ "Total time: " ++ show (totalTime `div` 1000000) ++ "ms"
  where
    timeDiffNanos : Clock Monotonic -> Clock Monotonic -> Integer
    timeDiffNanos end start =
      let endNanos = seconds end * 1000000000 + nanoseconds end
          startNanos = seconds start * 1000000000 + nanoseconds start
      in endNanos - startNanos

    checkDecls : TCEnv -> List Declaration -> IO (Either String TCEnv)
    checkDecls env [] = pure (Right env)
    checkDecls env (d :: ds) =
      case addDeclChecked env d of
        Left err => pure (Left (show err))
        Right env' => checkDecls env' ds

main : IO ()
main = do
  args <- getArgs
  case args of
    [_, path] => benchmarkExport path
    _ => putStrLn "Usage: lean4idris-bench <export-file>"
