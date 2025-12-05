||| Simple CLI for reduction visualization
|||
||| Usage: lean4idris-vis <export-file> <decl-name> [--json|--html|--text]
module Lean4Idris.VisMain

import Lean4Idris
import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.TypeChecker
import Lean4Idris.Trace
import Lean4Idris.TracingWhnf
import Lean4Idris.Pretty
import Lean4Idris.Export.Parser
import System
import System.File
import Data.String
import Data.List
import Data.List1

||| Parse a dotted name like "Nat.add" into a Name
||| Names are structured with innermost first: "Nat.add" becomes Str "add" (Str "Nat" Anonymous)
parseDottedName : String -> Name
parseDottedName s =
  let parts = forget (split (== '.') s)
  in foldl (\acc, seg => Str seg acc) Anonymous parts

||| Find a declaration by name
findDecl : Name -> List Declaration -> Maybe Declaration
findDecl _ [] = Nothing
findDecl target (d :: ds) =
  case declName d of
    Just n => if n == target then Just d else findDecl target ds
    Nothing => findDecl target ds

||| Get an expression to reduce from a declaration
getDeclExpr : Declaration -> Maybe ClosedExpr
getDeclExpr (DefDecl _ _ val _ _ _) = Just val
getDeclExpr (ThmDecl _ _ val _) = Just val
getDeclExpr (OpaqueDecl _ _ val _) = Just val
getDeclExpr _ = Nothing

||| Format output based on mode
data OutputMode = JSON | HTML | Text

parseOutputMode : List String -> OutputMode
parseOutputMode args =
  if elem "--json" args then JSON
  else if elem "--html" args then HTML
  else Text

||| Main entry point
main : IO ()
main = do
  args <- getArgs
  case args of
    [_, file, name] => runVis file name Text
    [_, file, name, mode] => runVis file name (parseOutputMode [mode])
    _ => do
      putStrLn "Usage: lean4idris-vis <export-file> <decl-name> [--json|--html|--text]"
      putStrLn ""
      putStrLn "Examples:"
      putStrLn "  lean4idris-vis test.export Nat.add"
      putStrLn "  lean4idris-vis test.export Nat.add --html > trace.html"
      putStrLn "  lean4idris-vis test.export Nat.add --json"
  where
    runVis : String -> String -> OutputMode -> IO ()
    runVis file name mode = do
      Right content <- readFile file
        | Left err => putStrLn $ "Error reading file: " ++ show err
      case parseExport content of
        Left err => putStrLn $ "Parse error: " ++ err
        Right st => do
          let decls = getDecls st
          let env = foldl (\e, d => addDecl d e) emptyEnv decls
          let targetName = parseDottedName name
          case findDecl targetName decls of
            Nothing => putStrLn $ "Declaration not found: " ++ name
            Just decl => do
              putStrLn $ "Found declaration: " ++ show (declName decl)
              case getDeclExpr decl of
                Nothing => putStrLn "Declaration has no value to reduce"
                Just expr => do
                  putStrLn $ "Expression: " ++ show expr
                  putStrLn ""
                  case whnfTraced env expr of
                    Left err => putStrLn $ "Error during reduction: " ++ show err
                    Right (result, trace) => do
                      putStrLn $ "Result: " ++ show result
                      putStrLn ""
                      putStrLn "=== Reduction Trace ==="
                      case mode of
                        Text => putStrLn (ppTrace trace)
                        JSON => putStrLn (traceToJSON trace)
                        HTML => putStrLn (traceToHTML trace)
