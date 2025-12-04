# Full Environment Proofs Plan

## Goal

Extend the proof layer to support:
- Global constants (definitions, axioms)
- Inductive types (with constructors)
- Projections (structure field access)
- Recursors (inductive eliminators)

This enables proving subject reduction for the full Lean 4 kernel, not just the pure lambda calculus fragment.

## Architecture

### Current State (Proofs/)

```
Syntax.idr          -- Expr with Var, Sort, Pi, Lam, App, Let
Substitution.idr    -- Renaming and substitution
Typing.idr          -- HasType judgment, Ctx
Reduction.idr       -- Step, Steps, WHNF
DefEq.idr           -- Definitional equality
Weakening.idr       -- Renaming preserves typing
SubstitutionLemma.idr -- Substitution preserves typing
CtxConversion.idr   -- Context equivalence
SubjectReduction.idr -- Type preservation theorem
```

### Target State

```
Syntax.idr          -- + Const, Proj (maybe Rec)
Name.idr            -- Simple name type for constants
Level.idr           -- Universe levels (already have)
Environment.idr     -- NEW: Global environment, declarations
Substitution.idr    -- + cases for Const, Proj
Typing.idr          -- + TConst, TProj, env parameter
Reduction.idr       -- + SDelta, SProj, SIota
DefEq.idr           -- + cases for new constructs
Weakening.idr       -- + cases for new constructs
SubstitutionLemma.idr -- + cases for new constructs
SubjectReduction.idr  -- + cases for new reduction rules
```

## Phase 1: Core Infrastructure

### 1.1 Names (Proofs/Name.idr)

Simple string-based names for now:

```idris
public export
Name : Type
Name = String
```

### 1.2 Extended Syntax (Proofs/Syntax.idr)

Add:

```idris
data Expr : Nat -> Type where
  -- existing...
  Var : Fin n -> Expr n
  Sort : Level -> Expr n
  Pi : Expr n -> Expr (S n) -> Expr n
  Lam : Expr n -> Expr (S n) -> Expr n
  App : Expr n -> Expr n -> Expr n
  Let : Expr n -> Expr n -> Expr (S n) -> Expr n

  -- NEW
  ||| Global constant reference
  Const : Name -> List Level -> Expr n

  ||| Projection from a structure
  ||| Proj structName fieldIdx struct
  Proj : Name -> Nat -> Expr n -> Expr n
```

Note: `Const` takes level arguments for universe polymorphism.

### 1.3 Environment (Proofs/Environment.idr)

```idris
||| Constructor info
public export
record CtorInfo where
  constructor MkCtorInfo
  name : Name
  type : Expr 0           -- Closed type
  inductiveName : Name
  numParams : Nat
  numFields : Nat

||| Inductive type info
public export
record IndInfo where
  constructor MkIndInfo
  name : Name
  type : Expr 0           -- e.g., Type -> Type
  numParams : Nat
  numIndices : Nat
  constructors : List CtorInfo

||| Recursor rule
public export
record RecRule where
  constructor MkRecRule
  ctorName : Name
  numFields : Nat
  rhs : Expr 0

||| Recursor info
public export
record RecInfo where
  constructor MkRecInfo
  name : Name
  type : Expr 0
  inductiveName : Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List RecRule

||| Environment entry
public export
data EnvEntry : Type where
  ||| Axiom: just a type
  AxiomEntry : (type : Expr 0) -> EnvEntry
  ||| Definition: type and value
  DefEntry : (type : Expr 0) -> (value : Expr 0) -> EnvEntry
  ||| Inductive type
  IndEntry : IndInfo -> EnvEntry
  ||| Constructor
  CtorEntry : CtorInfo -> EnvEntry
  ||| Recursor
  RecEntry : RecInfo -> EnvEntry

||| Global environment
public export
record Env where
  constructor MkEnv
  entries : Name -> Maybe EnvEntry

||| Empty environment
public export
emptyEnv : Env
emptyEnv = MkEnv (const Nothing)

||| Extend environment
public export
extendEnv : Name -> EnvEntry -> Env -> Env
extendEnv n e env = MkEnv $ \m =>
  if m == n then Just e else env.entries m
```

## Phase 2: Typing Rules

### 2.1 Typing with Environment

Change `HasType` to take environment:

```idris
||| Typing judgment: Σ; Γ ⊢ e : T
||| where Σ is the global environment
public export
data HasType : Env -> Ctx n -> Expr n -> Expr n -> Type where
  -- All existing rules gain env parameter

  ||| Constant typing
  ||| Look up type in environment, instantiate level params
  TConst : {env : Env} -> {ctx : Ctx n}
        -> (name : Name) -> (levels : List Level)
        -> env.entries name = Just (AxiomEntry ty)  -- or DefEntry
        -> HasType env ctx (Const name levels) (instantiateLevels ty levels)

  ||| Projection typing
  ||| Proj structName idx struct : fieldType
  ||| where struct : structType and fieldType is the idx-th field
  TProj : {env : Env} -> {ctx : Ctx n}
       -> HasType env ctx struct structTy
       -> -- ... lookup struct info, compute field type
       -> HasType env ctx (Proj structName idx struct) fieldTy
```

### 2.2 Well-Formed Environment

We need a predicate that the environment is well-formed:

```idris
||| All types in environment are well-typed
public export
data WfEnv : Env -> Type where
  WfEmpty : WfEnv emptyEnv
  WfExtend : WfEnv env
          -> HasType env Empty ty (Sort l)  -- type is well-typed
          -> WfEnv (extendEnv n (AxiomEntry ty) env)
  -- ... cases for Def, Ind, Ctor, Rec
```

## Phase 3: Reduction Rules

### 3.1 Delta Reduction (unfold definitions)

```idris
||| Delta: unfold a defined constant
||| Const name levels → instantiateLevels value levels
||| when env has DefEntry for name
SDelta : {env : Env}
      -> env.entries name = Just (DefEntry ty value)
      -> Step env (Const name levels) (instantiateLevels value levels)
```

### 3.2 Projection Reduction

```idris
||| Proj reduction: Proj structName idx (Ctor args) → args[numParams + idx]
SProj : {env : Env}
     -> -- struct reduces to constructor application
     -> Step env (Proj structName idx struct) (nthArg (numParams + idx) struct)
```

### 3.3 Iota Reduction (recursor computation)

```idris
||| Iota: reduce recursor on constructor
||| rec params motives minors (Ctor args) indices → rule.rhs applied appropriately
SIota : {env : Env}
     -> -- complex: need to find matching rule, apply to fields + recursive calls
     -> Step env (App ... rec ... (Ctor args) ...) result
```

## Phase 4: Subject Reduction Extension

New cases needed:

1. **TConst + SDelta**: When constant unfolds, type preserved by definition
2. **TProj + SProj**: When projection computes, type is the field type
3. **TApp + SIota**: When recursor computes, type follows from recursor typing

## Complexity Estimate

| Component | New Code | Existing Changes |
|-----------|----------|------------------|
| Name.idr | ~10 lines | - |
| Syntax.idr | ~20 lines | - |
| Environment.idr | ~150 lines | - |
| Substitution.idr | ~50 lines | +Const, Proj cases |
| Typing.idr | ~100 lines | +env param everywhere |
| Reduction.idr | ~150 lines | +SDelta, SProj, SIota |
| DefEq.idr | ~50 lines | +new cases |
| Weakening.idr | ~30 lines | +new cases |
| SubstitutionLemma.idr | ~50 lines | +new cases |
| SubjectReduction.idr | ~100 lines | +new cases |
| **Total** | **~700 lines new** | **~200 lines modified** |

## Open Questions

1. **Level polymorphism**: How to handle level parameters in proofs?
   - Option A: Monomorphize (no level params in proofs)
   - Option B: Add level context alongside type context

2. **Recursor complexity**: Full iota reduction is complex
   - Option A: Start without recursors, add later
   - Option B: Include from start but hole out complex cases

3. **Mutual inductives**: Support single inductives first, mutual later?

4. **Proof irrelevance**: How to handle Prop and proof irrelevance?

## Recommended Order

1. Add `Const` and `Proj` to Syntax
2. Create Environment.idr with basic entries (Axiom, Def)
3. Add env parameter to all typing rules
4. Add `TConst` and `SDelta`
5. Get basic subject reduction working with delta
6. Add `IndEntry`, `CtorEntry` to environment
7. Add `TProj` and `SProj`
8. Get projection subject reduction working
9. Add `RecEntry` and `SIota` (complex)
10. Complete recursor subject reduction
