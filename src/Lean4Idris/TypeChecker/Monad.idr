module Lean4Idris.TypeChecker.Monad

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Pretty
import Data.SortedMap
import Data.Fin
import Data.Vect

%default total

------------------------------------------------------------------------
-- Environment
------------------------------------------------------------------------

public export
record TCEnv where
  constructor MkTCEnv
  decls : SortedMap Name Declaration
  quotInit : Bool
  nextLocalId : Nat  -- Counter for generating unique Local IDs
  localTypes : SortedMap Nat ClosedExpr  -- Types of Local variables by ID

public export
emptyEnv : TCEnv
emptyEnv = MkTCEnv empty False 0 empty

public export
addLocalType : Nat -> ClosedExpr -> TCEnv -> TCEnv
addLocalType id ty env = { localTypes $= insert id ty } env

public export
lookupLocalType : Nat -> TCEnv -> Maybe ClosedExpr
lookupLocalType id env = lookup id env.localTypes

public export
enableQuot : TCEnv -> TCEnv
enableQuot env = { quotInit := True } env

public export
addDecl : Declaration -> TCEnv -> TCEnv
addDecl d env = case declName d of
  Just n  => { decls $= insert n d } env
  Nothing => env

public export
lookupDecl : Name -> TCEnv -> Maybe Declaration
lookupDecl n env = lookup n env.decls

------------------------------------------------------------------------
-- Local Context
------------------------------------------------------------------------

public export
record LocalEntry where
  constructor MkLocalEntry
  name : Name
  type : ClosedExpr
  value : Maybe ClosedExpr
  placeholder : Maybe ClosedExpr

public export
LocalCtx : Nat -> Type
LocalCtx n = Vect n LocalEntry

public export
emptyCtx : LocalCtx 0
emptyCtx = []

public export
extendCtx : Name -> ClosedExpr -> LocalCtx n -> LocalCtx (S n)
extendCtx name ty ctx = MkLocalEntry name ty Nothing Nothing :: ctx

public export
extendCtxLet : Name -> ClosedExpr -> ClosedExpr -> LocalCtx n -> LocalCtx (S n)
extendCtxLet name ty val ctx = MkLocalEntry name ty (Just val) Nothing :: ctx

public export
lookupCtx : Fin n -> LocalCtx n -> LocalEntry
lookupCtx FZ (entry :: _) = entry
lookupCtx (FS k) (_ :: ctx) = lookupCtx k ctx

------------------------------------------------------------------------
-- Errors
------------------------------------------------------------------------

public export
data TCError : Type where
  TypeExpected : ClosedExpr -> TCError
  FunctionExpected : ClosedExpr -> TCError
  AppTypeMismatch : (expected : ClosedExpr) -> (actual : ClosedExpr) -> TCError
  LetTypeMismatch : (expected : ClosedExpr) -> (actual : ClosedExpr) -> TCError
  UnknownConst : Name -> TCError
  WrongNumLevels : (expected : Nat) -> (actual : Nat) -> Name -> TCError
  NegativeOccurrence : (indName : Name) -> (ctorName : Name) -> TCError
  CtorWrongReturnType : (ctorName : Name) -> (expected : Name) -> (actual : ClosedExpr) -> TCError
  CtorWrongFieldCount : (ctorName : Name) -> (declared : Nat) -> (actual : Nat) -> TCError
  CtorWrongInductive : (ctorName : Name) -> (declared : Name) -> (actual : Name) -> TCError
  CtorUniverseMismatch : (ctorName : Name) -> (indParams : List Name) -> (ctorParams : List Name) -> TCError
  CtorInductiveNotFound : (ctorName : Name) -> (indName : Name) -> TCError
  CyclicLevelParam : Name -> TCError
  FuelExhausted : TCError
  OtherError : String -> TCError

export
showExprHead : ClosedExpr -> String
showExprHead (Sort _) = "Sort"
showExprHead (Const n _) = "Const " ++ show n
showExprHead (App f _) = "App (" ++ showExprHead f ++ " ...)"
showExprHead (Lam _ _ _ _) = "Lam"
showExprHead (Pi _ _ _ _) = "Pi"
showExprHead (Let _ _ _ _) = "Let"
showExprHead (BVar i) = "BVar " ++ show (finToNat i)
showExprHead (Local id _) = "Local " ++ show id
showExprHead (Proj sn _ _) = "Proj " ++ show sn
showExprHead (NatLit n) = "NatLit " ++ show n
showExprHead (StringLit _) = "StringLit"

export
covering
Show TCError where
  show (TypeExpected e) = "type expected: " ++ showExprHead e
  show (FunctionExpected e) = "function expected: " ++ showExprHead e
  show (AppTypeMismatch dom argTy) = "application type mismatch: expected " ++ showExprHead dom ++ ", got " ++ showExprHead argTy
  show (LetTypeMismatch expected actual) = "let type mismatch: expected " ++ showExprHead expected ++ ", got " ++ showExprHead actual
  show (UnknownConst n) = "unknown constant: " ++ show n
  show (WrongNumLevels exp act n) = "wrong number of universe levels for " ++ show n ++ ": expected " ++ show exp ++ ", got " ++ show act
  show (NegativeOccurrence ind ctor) = "negative occurrence of " ++ show ind ++ " in constructor " ++ show ctor
  show (CtorWrongReturnType ctor expected _) = "constructor " ++ show ctor ++ " must return " ++ show expected
  show (CtorWrongFieldCount ctor decl actual) = "constructor " ++ show ctor ++ " declares " ++ show decl ++ " fields but type has " ++ show actual
  show (CtorWrongInductive ctor decl actual) = "constructor " ++ show ctor ++ " registered for " ++ show decl ++ " but returns " ++ show actual
  show (CtorUniverseMismatch ctor indPs ctorPs) = "constructor " ++ show ctor ++ " universe params don't match inductive"
  show (CtorInductiveNotFound ctor ind) = "inductive " ++ show ind ++ " not found for constructor " ++ show ctor
  show (CyclicLevelParam n) = "cyclic universe level parameter: " ++ show n
  show FuelExhausted = "fuel exhausted"
  show (OtherError s) = s

------------------------------------------------------------------------
-- TC Monad
------------------------------------------------------------------------

public export
defaultFuel : Nat
defaultFuel = 100000

public export
data TC : Type -> Type where
  MkTC : (Nat -> Either TCError (Nat, a)) -> TC a

export
runTCFuel : Nat -> TC a -> Either TCError (Nat, a)
runTCFuel fuel (MkTC f) = f fuel

export
runTC : TC a -> Either TCError a
runTC tc = map snd (runTCFuel defaultFuel tc)

export
runTCWithFuel : Nat -> TC a -> Either TCError a
runTCWithFuel fuel tc = map snd (runTCFuel fuel tc)

export
liftEither : Either TCError a -> TC a
liftEither (Left err) = MkTC (\_ => Left err)
liftEither (Right x) = MkTC (\fuel => Right (fuel, x))

export
Functor TC where
  map f (MkTC tc) = MkTC (\fuel => case tc fuel of
    Left err => Left err
    Right (fuel', x) => Right (fuel', f x))

export
Applicative TC where
  pure x = MkTC (\fuel => Right (fuel, x))
  (MkTC tf) <*> (MkTC tx) = MkTC (\fuel => case tf fuel of
    Left err => Left err
    Right (fuel', f) => case tx fuel' of
      Left err => Left err
      Right (fuel'', x) => Right (fuel'', f x))

export
Monad TC where
  (MkTC tx) >>= f = MkTC (\fuel => case tx fuel of
    Left err => Left err
    Right (fuel', x) => runTCFuel fuel' (f x))

export
useFuel : TC ()
useFuel = MkTC (\fuel => case fuel of
  0 => Left FuelExhausted
  S k => Right (k, ()))

export
throw : TCError -> TC a
throw err = MkTC (\_ => Left err)

export
tcRight : a -> TC a
tcRight = pure

export
tcLeft : TCError -> TC a
tcLeft = throw
