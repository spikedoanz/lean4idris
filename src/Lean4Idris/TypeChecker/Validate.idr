module Lean4Idris.TypeChecker.Validate

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Subst
import Lean4Idris.Pretty
import Lean4Idris.TypeChecker.Monad
import Lean4Idris.TypeChecker.Reduction
import Lean4Idris.TypeChecker.Infer
import Lean4Idris.TypeChecker.DefEq
import Data.List
import System.File
import Debug.Trace

%default total

debugFile : File
debugFile = unsafePerformIO $ do
  Right f <- openFile "/tmp/typecheck_debug.txt" Append
    | Left _ => pure stdin
  pure f

debugPrint : String -> a -> a
debugPrint msg x = unsafePerformIO $ do
  Right () <- fPutStrLn debugFile (msg ++ "\n")
    | Left _ => pure x
  fflush debugFile
  pure x

------------------------------------------------------------------------
-- Name/Param Validation
------------------------------------------------------------------------

export
checkNameNotDeclared : TCEnv -> Name -> TC ()
checkNameNotDeclared env name = case lookupDecl name env of
  Just _ => throw (OtherError $ "already declared: " ++ show name)
  Nothing => pure ()

export
checkNoDuplicateUnivParams : List Name -> TC ()
checkNoDuplicateUnivParams [] = pure ()
checkNoDuplicateUnivParams (p :: ps) =
  if elem p ps
    then throw (OtherError $ "duplicate universe parameter: " ++ show p)
    else checkNoDuplicateUnivParams ps

export covering
checkIsType : TCEnv -> ClosedExpr -> TC Level
checkIsType env e = do
  ty <- inferType env e
  ensureSort env ty

------------------------------------------------------------------------
-- Positivity Check
------------------------------------------------------------------------

checkNegativeOccurrence : Name -> {n : Nat} -> Expr n -> Bool
checkNegativeOccurrence indName = go 0
  where
    go : {m : Nat} -> Nat -> Expr m -> Bool
    go _ (BVar _) = False
    go _ (Sort _) = False
    go _ (NatLit _) = False
    go _ (StringLit _) = False
    go depth (Const n _) = depth >= 2 && n == indName
    go depth (App f x) = go depth f || go depth x
    go depth (Lam _ _ ty body) = go depth ty || go depth body
    go depth (Pi _ _ dom cod) = go (S depth) dom || go 0 cod
    go depth (Let _ ty val body) = go depth ty || go depth val || go depth body
    go depth (Proj _ _ e) = go depth e

checkStrictlyPositive : Name -> ClosedExpr -> Bool
checkStrictlyPositive indName ty = not (checkNegativeOccurrence indName ty)

checkPositivity : Name -> List ConstructorInfo -> TC ()
checkPositivity indName [] = pure ()
checkPositivity indName (ctor :: ctors) =
  if checkStrictlyPositive indName ctor.type
    then checkPositivity indName ctors
    else throw (NegativeOccurrence indName ctor.name)

------------------------------------------------------------------------
-- Constructor Validation
------------------------------------------------------------------------

getReturnTypeHead : Expr n -> Maybe (Name, List Level)
getReturnTypeHead (Pi _ _ _ cod) = getReturnTypeHead cod
getReturnTypeHead (App f _) = getReturnTypeHead f
getReturnTypeHead (Const n ls) = Just (n, ls)
getReturnTypeHead _ = Nothing

countPiBinders : Expr n -> Nat
countPiBinders (Pi _ _ _ cod) = S (countPiBinders cod)
countPiBinders _ = 0

checkCtorReturnType : Name -> Name -> ClosedExpr -> TC ()
checkCtorReturnType ctorName indName ctorTy = case getReturnTypeHead ctorTy of
  Just (returnName, _) =>
    if returnName == indName then pure () else throw (CtorWrongInductive ctorName indName returnName)
  Nothing => throw (CtorWrongReturnType ctorName indName ctorTy)

checkCtorFieldCount : Name -> Nat -> Nat -> ClosedExpr -> TC ()
checkCtorFieldCount ctorName numParams declaredFields ctorTy =
  let totalBinders = countPiBinders ctorTy
      actualFields = if totalBinders >= numParams then totalBinders `minus` numParams else 0
  in if declaredFields == actualFields then pure ()
     else throw (CtorWrongFieldCount ctorName declaredFields actualFields)

checkCtorUniverseParams : Name -> List Name -> List Name -> TC ()
checkCtorUniverseParams ctorName indParams ctorParams =
  if indParams == ctorParams then pure ()
  else throw (CtorUniverseMismatch ctorName indParams ctorParams)

getInductiveLevelParams : TCEnv -> Name -> Maybe (List Name)
getInductiveLevelParams env name = case lookupDecl name env of
  Just (IndDecl _ params) => Just params
  _ => Nothing

------------------------------------------------------------------------
-- Axiom/Def/Thm Validation
------------------------------------------------------------------------

export covering
checkAxiomDecl : TCEnv -> Name -> ClosedExpr -> List Name -> TC ()
checkAxiomDecl env name ty levelParams = do
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env ty
  pure ()

export covering
checkDefDecl : TCEnv -> Name -> ClosedExpr -> ClosedExpr -> List Name -> TC ()
checkDefDecl env name ty value levelParams = do
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env ty
  (env', valueTy) <- inferTypeE env value
  eq <- isDefEq env' valueTy ty
  if eq
    then pure ()
    else throw (OtherError $ "definition type mismatch for " ++ show name
               ++ "\n  inferred: " ++ show valueTy
               ++ "\n  declared: " ++ show ty)

export covering
checkThmDecl : TCEnv -> Name -> ClosedExpr -> ClosedExpr -> List Name -> TC ()
checkThmDecl env name ty value levelParams = do
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  tyLevel <- checkIsType env ty
  if simplify tyLevel /= Zero
    then throw (OtherError $ "theorem type must be a Prop: " ++ show name)
    else do
      (env', valueTy) <- inferTypeE env value
      eq <- isDefEq env' valueTy ty
      if eq
        then pure ()
        else throw (OtherError $ "theorem proof type mismatch for " ++ show name
                   ++ "\n  inferred: " ++ show valueTy
                   ++ "\n  declared: " ++ show ty)

------------------------------------------------------------------------
-- Add Validated Declarations
------------------------------------------------------------------------

export covering
addAxiomChecked : TCEnv -> Name -> ClosedExpr -> List Name -> TC TCEnv
addAxiomChecked env name ty levelParams = do
  checkAxiomDecl env name ty levelParams
  pure (addDecl (AxiomDecl name ty levelParams) env)

export covering
addDefChecked : TCEnv -> Name -> ClosedExpr -> ClosedExpr ->
                ReducibilityHint -> Safety -> List Name -> TC TCEnv
addDefChecked env name ty value hint safety levelParams = do
  checkDefDecl env name ty value levelParams
  pure (addDecl (DefDecl name ty value hint safety levelParams) env)

export covering
addThmChecked : TCEnv -> Name -> ClosedExpr -> ClosedExpr -> List Name -> TC TCEnv
addThmChecked env name ty value levelParams = do
  checkThmDecl env name ty value levelParams
  pure (addDecl (ThmDecl name ty value levelParams) env)

export covering
addDeclChecked : TCEnv -> Declaration -> TC TCEnv
addDeclChecked env (AxiomDecl name ty levelParams) =
  addAxiomChecked env name ty levelParams
addDeclChecked env (DefDecl name ty value hint safety levelParams) =
  addDefChecked env name ty value hint safety levelParams
addDeclChecked env (ThmDecl name ty value levelParams) =
  addThmChecked env name ty value levelParams
addDeclChecked env (OpaqueDecl name ty value levelParams) = do
  checkDefDecl env name ty value levelParams
  pure (addDecl (OpaqueDecl name ty value levelParams) env)
addDeclChecked env QuotDecl = pure (enableQuot env)
addDeclChecked env decl@(IndDecl info levelParams) = do
  checkNameNotDeclared env info.name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env info.type
  pure (addDecl decl env)
addDeclChecked env decl@(CtorDecl name ty indName ctorIdx numParams numFields levelParams) = do
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env ty
  case getInductiveLevelParams env indName of
    Nothing => throw (CtorInductiveNotFound name indName)
    Just indLevelParams => do
      if checkStrictlyPositive indName ty
        then pure ()
        else throw (NegativeOccurrence indName name)
      checkCtorReturnType name indName ty
      checkCtorFieldCount name numParams numFields ty
      checkCtorUniverseParams name indLevelParams levelParams
      pure (addDecl decl env)
addDeclChecked env decl@(RecDecl info levelParams) = do
  checkNameNotDeclared env info.name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env info.type
  pure (addDecl decl env)
