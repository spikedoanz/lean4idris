||| Declarations for Lean 4
|||
||| Declarations are top-level definitions in Lean: axioms, definitions,
||| theorems, inductive types, etc.
module Lean4Idris.Decl

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr

%default total

||| Reduction hint for definitions
public export
data ReducibilityHint : Type where
  ||| Abbreviation: always unfold
  Abbrev : ReducibilityHint
  ||| Opaque: never unfold
  Opaq : ReducibilityHint
  ||| Regular: unfold based on heuristics
  Regular : Nat -> ReducibilityHint

export
Eq ReducibilityHint where
  Abbrev == Abbrev = True
  Opaq == Opaq = True
  (Regular n1) == (Regular n2) = n1 == n2
  _ == _ = False

export
Show ReducibilityHint where
  show Abbrev = "abbrev"
  show Opaq = "opaque"
  show (Regular n) = "regular(" ++ show n ++ ")"

||| Safety level for definitions
public export
data Safety : Type where
  Safe : Safety
  Unsafe : Safety
  Partial : Safety

export
Eq Safety where
  Safe == Safe = True
  Unsafe == Unsafe = True
  Partial == Partial = True
  _ == _ = False

export
Show Safety where
  show Safe = "safe"
  show Unsafe = "unsafe"
  show Partial = "partial"

||| Constructor info for inductive types
public export
record ConstructorInfo where
  constructor MkConstructorInfo
  name : Name
  type : ClosedExpr

export
Show ConstructorInfo where
  show ci = show ci.name ++ " : <type>"

||| Recursor rule for inductive types
public export
record RecursorRule where
  constructor MkRecursorRule
  ctorName : Name
  numFields : Nat
  rhs : ClosedExpr

||| Recursor info
public export
record RecursorInfo where
  constructor MkRecursorInfo
  name : Name
  type : ClosedExpr
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List RecursorRule
  isK : Bool

||| Inductive type info
public export
record InductiveInfo where
  constructor MkInductiveInfo
  name : Name
  type : ClosedExpr
  numParams : Nat
  numIndices : Nat
  constructors : List ConstructorInfo
  isRecursive : Bool
  isReflexive : Bool

export
Show InductiveInfo where
  show ii = "inductive " ++ show ii.name ++
            " (params=" ++ show ii.numParams ++
            ", indices=" ++ show ii.numIndices ++ ")"

||| A declaration in the environment
public export
data Declaration : Type where
  ||| Axiom: a postulated constant
  AxiomDecl : (name : Name) -> (type : ClosedExpr) -> (levelParams : List Name) -> Declaration
  ||| Definition: a defined constant
  DefDecl : (name : Name) -> (type : ClosedExpr) -> (value : ClosedExpr) ->
            (hint : ReducibilityHint) -> (safety : Safety) ->
            (levelParams : List Name) -> Declaration
  ||| Theorem: like definition but proof-irrelevant
  ThmDecl : (name : Name) -> (type : ClosedExpr) -> (value : ClosedExpr) ->
            (levelParams : List Name) -> Declaration
  ||| Opaque: definition that cannot be unfolded
  OpaqueDecl : (name : Name) -> (type : ClosedExpr) -> (value : ClosedExpr) ->
               (levelParams : List Name) -> Declaration
  ||| Quotient type primitives
  QuotDecl : Declaration
  ||| Inductive type
  IndDecl : InductiveInfo -> (levelParams : List Name) -> Declaration
  ||| Constructor
  CtorDecl : (name : Name) -> (type : ClosedExpr) -> (inductiveName : Name) ->
             (ctorIdx : Nat) -> (numParams : Nat) -> (numFields : Nat) ->
             (levelParams : List Name) -> Declaration
  ||| Recursor
  RecDecl : RecursorInfo -> (levelParams : List Name) -> Declaration

||| Get the name of a declaration
public export
declName : Declaration -> Maybe Name
declName (AxiomDecl n _ _) = Just n
declName (DefDecl n _ _ _ _ _) = Just n
declName (ThmDecl n _ _ _) = Just n
declName (OpaqueDecl n _ _ _) = Just n
declName QuotDecl = Nothing
declName (IndDecl info _) = Just info.name
declName (CtorDecl n _ _ _ _ _ _) = Just n
declName (RecDecl info _) = Just info.name

||| Get the type of a declaration
public export
declType : Declaration -> Maybe ClosedExpr
declType (AxiomDecl _ t _) = Just t
declType (DefDecl _ t _ _ _ _) = Just t
declType (ThmDecl _ t _ _) = Just t
declType (OpaqueDecl _ t _ _) = Just t
declType QuotDecl = Nothing
declType (IndDecl info _) = Just info.type
declType (CtorDecl _ t _ _ _ _ _) = Just t
declType (RecDecl info _) = Just info.type

||| Get level parameters of a declaration
public export
declLevelParams : Declaration -> List Name
declLevelParams (AxiomDecl _ _ ps) = ps
declLevelParams (DefDecl _ _ _ _ _ ps) = ps
declLevelParams (ThmDecl _ _ _ ps) = ps
declLevelParams (OpaqueDecl _ _ _ ps) = ps
declLevelParams QuotDecl = []
declLevelParams (IndDecl _ ps) = ps
declLevelParams (CtorDecl _ _ _ _ _ _ ps) = ps
declLevelParams (RecDecl _ ps) = ps

export
Show Declaration where
  show (AxiomDecl n _ _) = "axiom " ++ show n
  show (DefDecl n _ _ hint safety _) = show safety ++ " def " ++ show n ++ " [" ++ show hint ++ "]"
  show (ThmDecl n _ _ _) = "theorem " ++ show n
  show (OpaqueDecl n _ _ _) = "opaque " ++ show n
  show QuotDecl = "quot"
  show (IndDecl info _) = show info
  show (CtorDecl n _ ind _ _ _ _) = "constructor " ++ show n ++ " of " ++ show ind
  show (RecDecl info _) = "recursor " ++ show info.name

||| Make a declaration opaque (non-unfoldable)
||| Used when a declaration times out or fails type checking - we still add it
||| to the environment for type lookups but prevent unfolding its value
public export
makeDeclOpaque : Declaration -> Declaration
makeDeclOpaque (DefDecl n ty val _ safety ps) = DefDecl n ty val Opaq safety ps
makeDeclOpaque (ThmDecl n ty val ps) = OpaqueDecl n ty val ps
makeDeclOpaque d = d  -- Other declarations don't have values to unfold
