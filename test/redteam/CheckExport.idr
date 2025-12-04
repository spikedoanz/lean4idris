module CheckExport

import Lean4Idris
import Lean4Idris.Export.Parser
import Lean4Idris.TypeChecker
import Lean4Idris.Decl
import System.File
import Data.List
import Data.String

||| Get name of declaration as string
getDeclNameStr : Declaration -> String
getDeclNameStr d = maybe "Quot" show (declName d)

||| Load all declarations without type checking
loadAllDecls : TCEnv -> List Declaration -> TCEnv
loadAllDecls tcenv [] = tcenv
loadAllDecls tcenv (d :: ds) = loadAllDecls (addDecl d tcenv) ds

||| Get all but last element and last element
splitLast : List a -> Maybe (List a, a)
splitLast [] = Nothing
splitLast [x] = Just ([], x)
splitLast (x :: xs) = map (\(rest, lst) => (x :: rest, lst)) (splitLast xs)

||| Check only the final declaration after loading all dependencies
checkFinalDecl : TCEnv -> List Declaration -> Either String String
checkFinalDecl tcenv decls =
  case splitLast decls of
    Nothing => Left "No declarations to check"
    Just (deps, lastDecl) =>
      let env = loadAllDecls tcenv deps
          name = getDeclNameStr lastDecl
      in case addDeclChecked env lastDecl of
           Right _ => Right $ "Successfully type-checked: " ++ name
           Left err => Left $ name ++ ": " ++ show err

||| Check an export file - only checks the final theorem
export
checkExportFile : String -> IO (Either String String)
checkExportFile path = do
  putStrLn $ "Reading: " ++ path
  Right content <- readFile path
    | Left err => pure $ Left $ "Failed to read file: " ++ show err

  putStrLn $ "File size: " ++ show (length content) ++ " bytes"

  case parseExport content of
    Left err => pure $ Left $ "Parse error: " ++ err
    Right st => do
      let decls = getDecls st
      putStrLn $ "Parsed " ++ show (length decls) ++ " declarations"
      putStrLn "Loading dependencies..."
      pure $ checkFinalDecl emptyEnv decls

||| Main entry point
main : IO ()
main = do
  putStrLn "======================================"
  putStrLn "  lean4idris Export File Checker"
  putStrLn "======================================"
  putStrLn ""

  putStrLn "## Checking Nat.gcd_self"
  result1 <- checkExportFile "lean4export/examples/Nat.gcd_self.export"
  case result1 of
    Left err => putStrLn $ "FAILED: " ++ err
    Right msg => putStrLn msg

  putStrLn ""
  putStrLn "## Checking CategoryTheory.yonedaLemma"
  result2 <- checkExportFile "lean4export/examples/CategoryTheory.yonedaLemma.export"
  case result2 of
    Left err => putStrLn $ "FAILED: " ++ err
    Right msg => putStrLn msg

  putStrLn ""
  putStrLn "Done!"
