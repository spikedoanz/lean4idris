# Proofs Migration Guide

This document outlines the gaps between the formal proofs in `src/Lean4Idris/Proofs/` and the actual type checker implementation, along with a migration plan to bring them back into alignment.

## Current Status

The proofs were originally written for a simplified type theory and have diverged from the implementation. They still compile (with `believe_me` holes), but no longer accurately describe the system being implemented.

## Gap Analysis

### 1. Expression Syntax (`Proofs/Syntax.idr` vs `Expr.idr`)

| Feature | Proofs | Implementation | Migration Difficulty |
|---------|--------|----------------|---------------------|
| Bound variables | `Var : Fin n` | `BVar : Fin n` | Trivial rename |
| Local variables | **Missing** | `Local : Nat -> Name -> Expr n` | Medium |
| Binder info | Not tracked | `BinderInfo` in Lam/Pi | Medium |
| Binder names | Not tracked | Names in Lam/Pi/Let | Easy (ignorable) |
| Nat literals | **Missing** | `NatLit : Nat -> Expr n` | Easy |
| String literals | **Missing** | `StringLit : String -> Expr n` | Easy |

**Migration Plan:**

```idris
-- Phase 1: Add missing constructors to Proofs/Syntax.idr
data Expr : Nat -> Type where
  Var : Fin n -> Expr n                    -- Keep (rename to BVar optional)
  Local : Nat -> Expr n                    -- ADD: for runtime type checking
  Sort : Level -> Expr n
  Pi : (dom : Expr n) -> (cod : Expr (S n)) -> Expr n
  Lam : (ty : Expr n) -> (body : Expr (S n)) -> Expr n
  App : Expr n -> Expr n -> Expr n
  Let : (ty : Expr n) -> (val : Expr n) -> (body : Expr (S n)) -> Expr n
  Const : Name -> List Level -> Expr n
  Proj : Name -> Nat -> Expr n -> Expr n
  NatLit : Nat -> Expr n                   -- ADD: for native evaluation
  StringLit : String -> Expr n             -- ADD: for native evaluation
```

**Notes:**
- `Local` is used during type checking to represent variables introduced by binders with unique IDs (instead of de Bruijn). The proofs can treat `Local` as a neutral form that blocks reduction.
- `BinderInfo` can be ignored in proofs (it's metadata for implicit argument synthesis).
- Binder names are purely for pretty-printing; proofs can ignore them.

---

### 2. Universe Levels (`Proofs/Syntax.idr` vs `Level.idr`)

| Feature | Proofs | Implementation | Migration Difficulty |
|---------|--------|----------------|---------------------|
| Zero | `LZero` | `Zero` | Trivial rename |
| Successor | `LSucc` | `Succ` | Trivial rename |
| Maximum | `lmax` (function) | `Max` (constructor) | Easy |
| IMax | **Missing** | `IMax : Level -> Level -> Level` | Hard |
| Parameters | **Missing** | `Param : Name -> Level` | Hard |

**Migration Plan:**

```idris
-- Phase 2: Extend Level in Proofs/Syntax.idr
data Level : Type where
  LZero : Level
  LSucc : Level -> Level
  LMax  : Level -> Level -> Level          -- CHANGE: from function to constructor
  LIMax : Level -> Level -> Level          -- ADD: impredicative max
  LParam : Name -> Level                   -- ADD: universe polymorphism
```

**Key semantics to prove:**
- `IMax l1 l2 = 0` when `l2 = 0`
- `IMax l1 l2 = Max l1 l2` when `l2 > 0`
- This makes `Prop` (universe 0) impredicative: `(P : Prop) -> Prop : Prop`

**New lemmas needed:**
- `imaxZeroRight : IMax l Zero = Zero`
- `imaxSuccRight : IMax l1 (Succ l2) = Max l1 (Succ l2)`
- Level substitution for `Param`

---

### 3. Reduction (`Proofs/Reduction.idr` vs `TypeChecker/Reduction.idr`)

| Feature | Proofs | Implementation | Migration Difficulty |
|---------|--------|----------------|---------------------|
| Beta | `SBeta` | `whnfStepCore` | Already aligned |
| Zeta | `SZeta` | `whnfStepCore` | Already aligned |
| Delta | `SDelta` (separate) | `unfoldHead` | Easy to unify |
| Iota | **Missing** | `tryIotaReduction` | Hard |
| Projection | **Missing** | `tryProjReduction` | Medium |
| Quotient | **Missing** | `tryQuotReduction` | Hard |
| Native eval | **Missing** | `tryNativeEval` (20+ ops) | Out of scope |

**Migration Plan:**

#### Phase 3a: Unify Delta Reduction

The proofs already have `DeltaStep` as a separate relation. This is good - keep it separate for opacity control.

```idris
-- Already exists, just verify alignment:
data DeltaStep : Env -> Expr n -> Expr n -> Type where
  SDelta : (name : Name) -> (levels : List Level)
        -> (def : Expr 0)
        -> getDefValue name env = Just def
        -> DeltaStep env (Const name levels) (instantiateLevels def levels)
```

#### Phase 3b: Add Iota Reduction

Iota reduction eliminates recursors when the major premise is a constructor.

```idris
-- New: Iota reduction for inductive elimination
data IotaStep : Env -> Expr n -> Expr n -> Type where
  ||| rec.{ls} params motives minors indices (ctor.{ls'} params' fields) rest
  ||| -->
  ||| (minor_for_ctor params motives minors) fields rest
  SIota : (recName : Name)
       -> (ctorName : Name)
       -> (rule : RecursorRule)
       -> findRecRule recName ctorName env = Just rule
       -> IotaStep env
            (mkApp (Const recName levels) (params ++ motives ++ minors ++ indices ++ [ctorApp] ++ rest))
            (mkApp (instantiateLevels rule.rhs levels) (params ++ motives ++ minors ++ fields ++ rest))
```

**Key lemmas needed:**
- Iota preserves typing (subject reduction for iota)
- Iota commutes with substitution

#### Phase 3c: Add Projection Reduction

```idris
-- New: Projection reduction for structures
data ProjStep : Env -> Expr n -> Expr n -> Type where
  ||| Proj structName idx (ctor params fields) --> fields[idx]
  SProj : (structName : Name) -> (idx : Nat) -> (ctorName : Name)
       -> (fields : Vect numFields (Expr n))
       -> isStructCtor ctorName structName env = True
       -> ProjStep env (Proj structName idx (mkApp (Const ctorName ls) (params ++ toList fields)))
                       (index idx fields)
```

#### Phase 3d: Add Quotient Reduction

```idris
-- New: Quotient reduction
data QuotStep : Expr n -> Expr n -> Type where
  ||| Quot.lift f h (Quot.mk a) --> f a
  SQuotLift : QuotStep (App (App (App (App (App (App (Const quotLiftName ls) alpha) r) beta) f) h)
                            (App (App (App (Const quotMkName ls') alpha') r') a))
                       (App f a)

  ||| Quot.ind h (Quot.mk a) --> h a
  SQuotInd : QuotStep (App (App (App (App (App (Const quotIndName ls) alpha) r) beta) h)
                           (App (App (App (Const quotMkName ls') alpha') r') a))
                      (App h a)
```

#### Phase 3e: Native Evaluation (Out of Scope)

Native evaluation (`Nat.add`, `Nat.ble`, etc.) is implementation-specific optimization. The proofs should **not** include these - they're computationally equivalent to the definitional unfolding, just faster.

**Recommendation:** Document that native evaluation is sound because it produces the same results as full delta+iota reduction.

---

### 4. Typing (`Proofs/Typing.idr` vs `TypeChecker/Infer.idr`)

| Feature | Proofs | Implementation | Migration Difficulty |
|---------|--------|----------------|---------------------|
| Variables | `TVar` | `inferType BVar` | Aligned |
| Sort | `TSort` | `inferType Sort` | Aligned |
| Pi | `TPi` | `inferType Pi` | Aligned |
| Lambda | `TLam` | `inferType Lam` | Aligned |
| Application | `TApp` | `inferType App` | Aligned |
| Let | `TLet` | `inferType Let` | Aligned |
| Conversion | `TConv` | implicit in `checkType` | Aligned |
| Constants | `TConst` | `inferType Const` | Aligned |
| **Local** | **Missing** | `inferType Local` | Medium |
| **Projection** | **Missing** | `inferType Proj` | Medium |
| **NatLit** | **Missing** | `inferType NatLit` | Easy |
| **StringLit** | **Missing** | `inferType StringLit` | Easy |

**Migration Plan:**

```idris
-- Phase 4: Add missing typing rules

||| Local variable typing (lookup in runtime context)
TLocal : (id : Nat) -> (ty : Expr n)
      -> lookupLocal id env = Just ty
      -> HasType env ctx (Local id) ty

||| Projection typing
TProj : (structName : Name) -> (idx : Nat) -> (struct : Expr n)
     -> (structTy : Expr n) -> (fieldTy : Expr n)
     -> HasType env ctx struct structTy
     -> getFieldType structName idx structTy env = Just fieldTy
     -> HasType env ctx (Proj structName idx struct) fieldTy

||| Natural number literal typing
TNatLit : (n : Nat) -> HasType env ctx (NatLit n) (Const natName [])

||| String literal typing
TStringLit : (s : String) -> HasType env ctx (StringLit s) (Const stringName [])
```

---

### 5. Definitional Equality (`Proofs/DefEq.idr` vs `TypeChecker/DefEq.idr`)

| Feature | Proofs | Implementation | Migration Difficulty |
|---------|--------|----------------|---------------------|
| Reflexivity | `DERefl` | implicit | Aligned |
| Symmetry | `DESym` | implicit | Aligned |
| Transitivity | `DETrans` | via WHNF | Aligned |
| Beta/Zeta | `DEStep` | via `whnf` | Aligned |
| Congruence | `DEPi`, `DELam`, etc. | structural comparison | Aligned |
| **Proof irrelevance** | **Missing** | `tryProofIrrelevance` | Medium |
| **Level equality** | Basic | Complex normalization | Medium |

**Migration Plan:**

```idris
-- Phase 5: Add proof irrelevance

||| Proof irrelevance: all proofs of Prop are equal
DEProofIrrel : HasType env ctx e1 ty
            -> HasType env ctx e2 ty
            -> HasType env ctx ty (Sort LZero)  -- ty : Prop
            -> DefEq e1 e2
```

**Level equality** requires proving that the level simplification algorithm is sound:
- `simplify l1 = simplify l2 -> l1 ≡ l2` (under all parameter assignments)

---

### 6. Substitution (`Proofs/Substitution.idr` vs `Subst.idr`)

The proofs have a more general substitution framework than the implementation needs:

| Feature | Proofs | Implementation | Notes |
|---------|--------|----------------|-------|
| General substitution | `Sub n m`, `subst` | Not present | Proofs are more general |
| Renaming | `Ren n m`, `rename` | Not present | Proofs are more general |
| Single-var subst | `singleSub`, `subst0` | `subst0`, `instantiate1` | Aligned |
| Weakening | `weaken`, `weakenN` | `weaken`, `weaken1` | Aligned |

**No migration needed** - the proofs are already more general. The implementation's specialized approach is an optimization.

---

## Migration Phases

### Phase 1: Syntax Alignment (Easy)
- [ ] Add `Local`, `NatLit`, `StringLit` to `Proofs/Syntax.idr`
- [ ] Update all pattern matches in Proofs modules
- [ ] Add trivial reduction/typing rules for new constructors

### Phase 2: Level System (Hard)
- [ ] Add `LMax`, `LIMax`, `LParam` constructors
- [ ] Prove IMax semantics
- [ ] Add level substitution lemmas
- [ ] Update typing rules to use new level constructors

### Phase 3: Reduction Extensions (Hard)
- [ ] Formalize iota reduction with `IotaStep`
- [ ] Formalize projection reduction with `ProjStep`
- [ ] Formalize quotient reduction with `QuotStep`
- [ ] Prove subject reduction extends to new rules
- [ ] Prove confluence extends to new rules

### Phase 4: Typing Extensions (Medium)
- [ ] Add `TLocal`, `TProj`, `TNatLit`, `TStringLit` rules
- [ ] Update `typeOfType` lemma for new rules
- [ ] Verify subject reduction still holds

### Phase 5: DefEq Extensions (Medium)
- [ ] Add proof irrelevance rule
- [ ] Prove level simplification soundness
- [ ] Update all DefEq lemmas

### Phase 6: Fill Proof Holes (Hard)
- [ ] Replace `believe_me` in `typeOfType` with actual proofs
- [ ] Complete `diamond` property proof
- [ ] Complete WHNF lemmas

---

## Files to Modify

| File | Changes | Priority |
|------|---------|----------|
| `Proofs/Syntax.idr` | Add constructors, update Level | High |
| `Proofs/Substitution.idr` | Handle new constructors | High |
| `Proofs/Reduction.idr` | Add Iota/Proj/Quot steps | High |
| `Proofs/Typing.idr` | Add new typing rules | Medium |
| `Proofs/DefEq.idr` | Add proof irrelevance | Medium |
| `Proofs/Environment.idr` | Add recursor/struct info | Medium |
| `Proofs/SubjectReduction.idr` | Extend to new rules | Low (depends on above) |
| `Proofs/Weakening.idr` | Handle new constructors | Medium |
| `Proofs/SubstitutionLemma.idr` | Handle new constructors | Medium |
| `Proofs/CtxConversion.idr` | Minor updates | Low |

---

## What to Keep vs. Remove

### Keep (valuable metatheory)
- `Proofs/Substitution.idr` - General substitution framework
- `Proofs/Reduction.idr` - Core beta/zeta reduction proofs
- `Proofs/DefEq.idr` - Definitional equality as equivalence
- `Proofs/Typing.idr` - Core typing rules (with extensions)
- `Proofs/SubjectReduction.idr` - Main theorem (once updated)
- `Proofs/Weakening.idr` - Weakening lemmas

### Consider Simplifying
- `Proofs/CtxConversion.idr` - May not be needed if we don't track WfCtx
- `Proofs/SubstitutionLemma.idr` - Complex, many `believe_me` holes

### Out of Scope
- Native evaluation proofs (trust implementation matches spec)
- Full level simplification correctness (complex, low value)

---

## Success Criteria

The migration is complete when:

1. All `believe_me` calls in core lemmas are replaced with actual proofs
2. Subject reduction theorem covers beta, zeta, delta, iota, projection, quotient
3. Proofs compile without holes (except clearly documented assumptions)
4. A mapping document shows correspondence between proof rules and implementation functions
