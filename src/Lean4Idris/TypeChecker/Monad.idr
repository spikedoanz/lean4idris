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
-- Type Checker Cache (for memoization)
------------------------------------------------------------------------

||| Cache for memoizing expensive operations during type checking.
||| Following lean4lean's approach:
||| - whnfCache: memoizes whnf results
||| - inferCache: memoizes inferType results
public export
record TCCache where
  constructor MkTCCache
  whnfCache : SortedMap ClosedExpr ClosedExpr
  inferCache : SortedMap ClosedExpr ClosedExpr

public export
emptyCache : TCCache
emptyCache = MkTCCache empty empty

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
showExprHead (Sort l) = "Sort " ++ show l
showExprHead (Const n _) = "Const " ++ show n
showExprHead (App f _) = "App (" ++ showExprHead f ++ " ...)"
showExprHead (Lam _ _ _ _) = "Lam"
showExprHead (Pi _ _ dom _) = "Pi (" ++ showExprHead dom ++ " -> ...)"
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

||| TC monad state: (fuel, cache)
public export
TCState : Type
TCState = (Nat, TCCache)

public export
defaultFuel : Nat
defaultFuel = 100000

public export
data TC : Type -> Type where
  MkTC : (TCState -> Either TCError (TCState, a)) -> TC a

export
runTCState : TCState -> TC a -> Either TCError (TCState, a)
runTCState st (MkTC f) = f st

export
runTCFuel : Nat -> TC a -> Either TCError (Nat, a)
runTCFuel fuel tc = case runTCState (fuel, emptyCache) tc of
  Left err => Left err
  Right ((fuel', _), a) => Right (fuel', a)

export
runTC : TC a -> Either TCError a
runTC tc = map snd (runTCFuel defaultFuel tc)

export
runTCWithFuel : Nat -> TC a -> Either TCError a
runTCWithFuel fuel tc = map snd (runTCFuel fuel tc)

export
liftEither : Either TCError a -> TC a
liftEither (Left err) = MkTC (\_ => Left err)
liftEither (Right x) = MkTC (\st => Right (st, x))

export
Functor TC where
  map f (MkTC tc) = MkTC (\st => case tc st of
    Left err => Left err
    Right (st', x) => Right (st', f x))

export
Applicative TC where
  pure x = MkTC (\st => Right (st, x))
  (MkTC tf) <*> (MkTC tx) = MkTC (\st => case tf st of
    Left err => Left err
    Right (st', f) => case tx st' of
      Left err => Left err
      Right (st'', x) => Right (st'', f x))

export
Monad TC where
  (MkTC tx) >>= f = MkTC (\st => case tx st of
    Left err => Left err
    Right (st', x) => runTCState st' (f x))

export
useFuel : TC ()
useFuel = MkTC (\(fuel, cache) => case fuel of
  0 => Left FuelExhausted
  S k => Right ((k, cache), ()))

------------------------------------------------------------------------
-- Cache Operations
------------------------------------------------------------------------

||| Look up a cached whnf result
export
lookupWhnfCache : ClosedExpr -> TC (Maybe ClosedExpr)
lookupWhnfCache e = MkTC (\(fuel, cache) =>
  Right ((fuel, cache), lookup e cache.whnfCache))

||| Insert a whnf result into the cache
export
insertWhnfCache : ClosedExpr -> ClosedExpr -> TC ()
insertWhnfCache e result = MkTC (\(fuel, cache) =>
  Right ((fuel, { whnfCache $= insert e result } cache), ()))

||| Look up a cached inferType result
export
lookupInferCache : ClosedExpr -> TC (Maybe ClosedExpr)
lookupInferCache e = MkTC (\(fuel, cache) =>
  Right ((fuel, cache), lookup e cache.inferCache))

||| Insert an inferType result into the cache
export
insertInferCache : ClosedExpr -> ClosedExpr -> TC ()
insertInferCache e result = MkTC (\(fuel, cache) =>
  Right ((fuel, { inferCache $= insert e result } cache), ()))

export
throw : TCError -> TC a
throw err = MkTC (\_ => Left err)

export
tcRight : a -> TC a
tcRight = pure

export
tcLeft : TCError -> TC a
tcLeft = throw
