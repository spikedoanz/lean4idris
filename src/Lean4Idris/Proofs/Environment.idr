||| Global Environment for the Proof Layer
|||
||| This module defines the global environment that stores:
||| - Axioms (types without definitions)
||| - Definitions (types with values)
||| - Inductive types (with constructors)
||| - Recursors (eliminators for inductive types)
|||
||| The environment is needed to type-check global constant references
||| and to implement delta/iota reduction.
module Lean4Idris.Proofs.Environment

import Data.Fin
import Lean4Idris.Proofs.Name
import Lean4Idris.Proofs.Syntax

%default total

------------------------------------------------------------------------
-- Universe Level Instantiation
------------------------------------------------------------------------

||| Instantiate universe level parameters in an expression.
||| This replaces level variables with concrete levels.
|||
||| For simplicity, we don't have level variables in our syntax,
||| so this is the identity function. A full implementation would
||| track level parameters and substitute them.
public export
instantiateLevels : Expr n -> List Level -> Expr n
instantiateLevels e [] = e
instantiateLevels e _ = e  -- No level polymorphism in our simplified model

------------------------------------------------------------------------
-- Constructor Information
------------------------------------------------------------------------

||| Information about a constructor of an inductive type.
public export
record CtorInfo where
  constructor MkCtorInfo
  ||| Name of this constructor
  ctorName : Name
  ||| Type of the constructor (closed, no free variables)
  ctorType : Expr 0
  ||| Name of the inductive type this constructor belongs to
  inductiveName : Name
  ||| Number of parameters (shared with the inductive type)
  numParams : Nat
  ||| Number of fields (arguments after parameters)
  numFields : Nat

------------------------------------------------------------------------
-- Inductive Type Information
------------------------------------------------------------------------

||| Information about an inductive type.
public export
record IndInfo where
  constructor MkIndInfo
  ||| Name of this inductive type
  indName : Name
  ||| Type of the inductive (e.g., Type -> Type for List)
  indType : Expr 0
  ||| Number of parameters
  numParams : Nat
  ||| Number of indices
  numIndices : Nat
  ||| Constructor information
  constructors : List CtorInfo

------------------------------------------------------------------------
-- Recursor Information
------------------------------------------------------------------------

||| A computation rule for a recursor.
||| Specifies how the recursor computes on a particular constructor.
public export
record RecRule where
  constructor MkRecRule
  ||| Name of the constructor this rule handles
  ctorName : Name
  ||| Number of fields for this constructor
  numFields : Nat
  ||| Right-hand side of the computation rule (closed)
  rhs : Expr 0

||| Information about a recursor (eliminator).
public export
record RecInfo where
  constructor MkRecInfo
  ||| Name of this recursor
  recName : Name
  ||| Type of the recursor
  recType : Expr 0
  ||| Name of the inductive type being eliminated
  inductiveName : Name
  ||| Number of parameters
  numParams : Nat
  ||| Number of indices
  numIndices : Nat
  ||| Number of motives (usually 1)
  numMotives : Nat
  ||| Number of minor premises (one per constructor)
  numMinors : Nat
  ||| Computation rules (one per constructor)
  rules : List RecRule

------------------------------------------------------------------------
-- Environment Entries
------------------------------------------------------------------------

||| An entry in the global environment.
public export
data EnvEntry : Type where
  ||| An axiom: just a type, no definition
  AxiomEntry : (type : Expr 0) -> EnvEntry

  ||| A definition: type and value
  DefEntry : (type : Expr 0) -> (value : Expr 0) -> EnvEntry

  ||| An opaque constant: type only, value hidden
  ||| (used for constants that shouldn't unfold)
  OpaqueEntry : (type : Expr 0) -> EnvEntry

  ||| An inductive type
  IndEntry : IndInfo -> EnvEntry

  ||| A constructor of an inductive type
  CtorEntry : CtorInfo -> EnvEntry

  ||| A recursor for an inductive type
  RecEntry : RecInfo -> EnvEntry

------------------------------------------------------------------------
-- Global Environment
------------------------------------------------------------------------

||| The global environment maps names to entries.
|||
||| We use a function representation for simplicity.
||| A real implementation would use a more efficient data structure.
public export
record Env where
  constructor MkEnv
  entries : Name -> Maybe EnvEntry

||| Empty environment
public export
emptyEnv : Env
emptyEnv = MkEnv (const Nothing)

||| Look up an entry by name
public export
lookupEnv : Name -> Env -> Maybe EnvEntry
lookupEnv n env = env.entries n

||| Extend the environment with a new entry
public export
extendEnv : Name -> EnvEntry -> Env -> Env
extendEnv n e env = MkEnv $ \m =>
  if m == n then Just e else env.entries m

||| Check if a name is defined in the environment
public export
isDefined : Name -> Env -> Bool
isDefined n env = case env.entries n of
  Just _ => True
  Nothing => False

------------------------------------------------------------------------
-- Environment Lookups
------------------------------------------------------------------------

||| Get the type of a constant (if it exists)
public export
getConstType : Name -> Env -> Maybe (Expr 0)
getConstType n env = case lookupEnv n env of
  Just (AxiomEntry ty) => Just ty
  Just (DefEntry ty _) => Just ty
  Just (OpaqueEntry ty) => Just ty
  Just (IndEntry info) => Just info.indType
  Just (CtorEntry info) => Just info.ctorType
  Just (RecEntry info) => Just info.recType
  Nothing => Nothing

||| Get the value of a definition (if it's a definition, not an axiom)
public export
getDefValue : Name -> Env -> Maybe (Expr 0)
getDefValue n env = case lookupEnv n env of
  Just (DefEntry _ val) => Just val
  _ => Nothing

||| Get inductive info (if it's an inductive type)
public export
getIndInfo : Name -> Env -> Maybe IndInfo
getIndInfo n env = case lookupEnv n env of
  Just (IndEntry info) => Just info
  _ => Nothing

||| Get constructor info (if it's a constructor)
public export
getCtorInfo : Name -> Env -> Maybe CtorInfo
getCtorInfo n env = case lookupEnv n env of
  Just (CtorEntry info) => Just info
  _ => Nothing

||| Get recursor info (if it's a recursor)
public export
getRecInfo : Name -> Env -> Maybe RecInfo
getRecInfo n env = case lookupEnv n env of
  Just (RecEntry info) => Just info
  _ => Nothing

------------------------------------------------------------------------
-- Well-Formed Environment (Predicate)
------------------------------------------------------------------------

||| A well-formed environment has all types well-typed.
|||
||| This predicate ensures that:
||| - All axiom types are well-formed
||| - All definition types are well-formed and values have those types
||| - All inductive types satisfy the positivity condition
||| - All constructors have valid types
||| - All recursors have valid types and computation rules
|||
||| For now, we define this as a simple predicate.
||| The full definition would require HasType with environment parameter.
public export
0 WfEnv : Env -> Type
WfEnv env = Unit  -- Placeholder: full definition requires mutual recursion with HasType

------------------------------------------------------------------------
-- Example: Boolean Type
------------------------------------------------------------------------

||| Example: The Bool inductive type
public export
boolIndInfo : IndInfo
boolIndInfo = MkIndInfo
  { indName = "Bool"
  , indType = Sort LZero  -- Bool : Type 0
  , numParams = 0
  , numIndices = 0
  , constructors = [ MkCtorInfo "Bool.true" (Const "Bool" []) "Bool" 0 0
                   , MkCtorInfo "Bool.false" (Const "Bool" []) "Bool" 0 0
                   ]
  }

||| Example environment with Bool
public export
boolEnv : Env
boolEnv =
  let env1 = extendEnv "Bool" (IndEntry boolIndInfo) emptyEnv
      env2 = extendEnv "Bool.true" (CtorEntry (MkCtorInfo "Bool.true" (Const "Bool" []) "Bool" 0 0)) env1
      env3 = extendEnv "Bool.false" (CtorEntry (MkCtorInfo "Bool.false" (Const "Bool" []) "Bool" 0 0)) env2
  in env3
