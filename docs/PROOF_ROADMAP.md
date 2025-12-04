# Proof Roadmap: From Substitution to Type Checker Consistency

This document sketches the complete proof of consistency for a Lean-like type checker,
from our current position to the final result.

## Current Status (What We Have)

### Completed Proofs (Zero Holes)
1. **Syntax.idr** - Intrinsically-scoped expressions with de Bruijn indices
2. **Substitution.idr** - Full substitution infrastructure:
   - Renaming and substitution operations
   - Extensionality lemmas
   - Composition lemmas (renameComp, substSubst)
   - Key interaction: `weakenSubst`, `substSubst0`
3. **Typing.idr** - Typing judgment with explicit universe levels
4. **Weakening.idr** - Weakening lemma: `Γ ⊢ e : T → Γ,x:A ⊢ weaken(e) : weaken(T)`
5. **SubstitutionLemma.idr** - Substitution lemma:
   - `Γ,x:A ⊢ e : T` and `Γ ⊢ s : A` implies `Γ ⊢ e[x:=s] : T[x:=s]`

### Partially Complete
6. **Reduction.idr** - β/ζ reduction with congruence rules (10 holes)
7. **SubjectReduction.idr** - Type preservation (6 holes)
8. **DefEq.idr** - Definitional equality (NEW, ~15 holes)

---

## The Full Proof Stack

### Layer 1: Core Metatheory (Current Focus)

```
┌─────────────────────────────────────────────────────────────────────┐
│                     CORE METATHEORY                                 │
├─────────────────────────────────────────────────────────────────────┤
│  Syntax           Substitution        Typing                        │
│     ↓                  ↓                 ↓                          │
│  Weakening ───────────────────────> Weakening Lemma                 │
│     ↓                  ↓                 ↓                          │
│  Reduction ───────────────────────> Substitution Lemma              │
│     ↓                                    ↓                          │
│  DefEq ──────────────────────────> Subject Reduction                │
└─────────────────────────────────────────────────────────────────────┘
```

**What remains for Layer 1:**

1. **DefEq completeness**:
   - `defEqWeaken` - weakening preserves DefEq
   - `defEqSubst` - substitution preserves DefEq
   - `stepWeaken` - weakening preserves reduction steps

2. **Subject Reduction cases**:
   - `SAppR`: needs `DefEq (subst0 cod arg) (subst0 cod arg')` when `arg → arg'`
   - `SLamTy`: needs context conversion
   - `SPiDom`: needs context conversion
   - `SLetTy`, `SLetVal`: similar

3. **Context Conversion**:
   - If `Γ ≡ Γ'` (pointwise DefEq) and `Γ ⊢ e : T`, then `Γ' ⊢ e : T'` with `T ≡ T'`

### Layer 2: Type Uniqueness and Inversion

```
┌─────────────────────────────────────────────────────────────────────┐
│                   TYPE UNIQUENESS                                   │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Inversion Lemmas:                                                  │
│    app_inv:  Γ ⊢ f x : T  →  ∃A B. Γ ⊢ f : Π(A,B) ∧ Γ ⊢ x : A     │
│    lam_inv:  Γ ⊢ λx.e : T →  ∃A B. T ≡ Π(A,B) ∧ Γ,x:A ⊢ e : B     │
│    pi_inv:   Γ ⊢ Π(A,B) : T → ∃l₁ l₂. Γ ⊢ A : Sort l₁ ∧ ...      │
│                                                                     │
│  Type Uniqueness:                                                   │
│    If Γ ⊢ e : A and Γ ⊢ e : B, then A ≡ B                         │
│                                                                     │
│  Type Synthesis (Bidirectional):                                    │
│    Given Γ and e, compute T such that Γ ⊢ e : T                    │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

**Key lemmas needed:**

- Inversion is straightforward pattern matching on typing derivations
- Type uniqueness follows by induction, using inversion + DefEq
- These enable algorithmic type checking

### Layer 3: Decidable Type Checking

```
┌─────────────────────────────────────────────────────────────────────┐
│                DECIDABLE TYPE CHECKING                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  WHNF (Weak Head Normal Form):                                      │
│    whnf : Expr → Expr                                               │
│    whnf_reduces : e →* whnf(e)                                      │
│    whnf_normalizing : whnf(e) is in WHNF                           │
│                                                                     │
│  DefEq Decision:                                                    │
│    isDefEq : Expr → Expr → Bool                                    │
│    isDefEq_sound : isDefEq(e₁,e₂) = true → e₁ ≡ e₂                │
│    isDefEq_complete : e₁ ≡ e₂ → isDefEq(e₁,e₂) = true             │
│                                                                     │
│  Type Checking Decision:                                            │
│    check : Ctx → Expr → Expr → Bool                                │
│    infer : Ctx → Expr → Maybe Expr                                 │
│    check_sound : check(Γ,e,T) = true → Γ ⊢ e : T                   │
│    check_complete : Γ ⊢ e : T → check(Γ,e,T) = true               │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

**Key challenges:**

- Termination of whnf (needs well-founded recursion or fuel)
- Strong normalization is undecidable for full dependent types
- Lean uses structural recursion + reducibility hints
- lean4lean uses `Option` monad with explicit fuel

### Layer 4: Environment and Declarations

```
┌─────────────────────────────────────────────────────────────────────┐
│              ENVIRONMENT AND DECLARATIONS                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Declarations:                                                      │
│    Axiom : Name → Type → Decl                                      │
│    Def   : Name → Type → Value → Decl                              │
│    Ind   : Name → IndInfo → Decl  (inductive types)                │
│                                                                     │
│  Environment:                                                       │
│    Env = List Decl                                                  │
│    EnvWf : Env → Type (all declarations well-typed)                │
│                                                                     │
│  Monotonicity:                                                      │
│    If EnvWf(E) and E ⊢ e : T and E ⊆ E',                          │
│    then E' ⊢ e : T                                                 │
│                                                                     │
│  δ-reduction (definition unfolding):                               │
│    If Def(n,T,v) ∈ E, then n → v                                   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### Layer 5: Inductive Types and Recursors

```
┌─────────────────────────────────────────────────────────────────────┐
│               INDUCTIVE TYPES                                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Inductive Type Formation:                                          │
│    IndParams, IndSort, Constructors                                 │
│    Strict positivity checking                                       │
│                                                                     │
│  Recursor:                                                          │
│    rec : (C : I → Sort) → (cases) → (i : I) → C i                  │
│                                                                     │
│  ι-reduction (recursor computation):                               │
│    rec C cases (ctor args) → case(args, rec C cases)               │
│                                                                     │
│  Large Elimination:                                                 │
│    Inductive in Prop can eliminate to Prop only                    │
│    (proof irrelevance)                                              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

**This is where Lean differs from simpler type theories:**
- Mutual inductives
- Nested inductives
- Indices vs parameters
- Universe constraints

### Layer 6: Consistency

```
┌─────────────────────────────────────────────────────────────────────┐
│                    CONSISTENCY                                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Logical Consistency (Weak):                                        │
│    ∄ proof : ⊢ False                                               │
│    (No closed term of type Empty/False in empty env)               │
│                                                                     │
│  Strong Normalization (for a fragment):                             │
│    All well-typed terms reduce to normal form                       │
│    (Not true for full Lean with axioms)                            │
│                                                                     │
│  Canonicity:                                                        │
│    Every closed term of type Nat reduces to a numeral               │
│    (Broken by axioms like funext, propext, choice)                 │
│                                                                     │
│  Relative Consistency:                                              │
│    If ZFC is consistent, then Lean's type theory is consistent     │
│    (Via set-theoretic model)                                        │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## lean4lean's Approach

lean4lean proves type checker correctness differently:

```
┌─────────────────────────────────────────────────────────────────────┐
│              lean4lean VERIFICATION                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  1. Define "ideal" type checker (TypeChecker.Expr)                 │
│     - Specification of what the type checker SHOULD compute        │
│                                                                     │
│  2. Define actual type checker (TypeChecker.Inner)                 │
│     - Executable implementation with caching, fuel, etc.           │
│                                                                     │
│  3. Prove refinement (Verify/*.lean)                               │
│     - TrExpr : relates actual expressions to ideal                 │
│     - RecM.WF : monadic well-formedness predicates                 │
│     - Every operation preserves the refinement                     │
│                                                                     │
│  4. Key theorems:                                                   │
│     - whnf'.WF : WHNF computation is correct                       │
│     - isDefEq.WF : DefEq check is sound and complete              │
│     - check.WF : Type checking is sound                            │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Proof Dependency Graph

```
                    Syntax
                      │
              ┌───────┴───────┐
              ↓               ↓
        Substitution       Typing
              │               │
     ┌────────┼────────┐      │
     ↓        ↓        ↓      ↓
 Renaming  SubstId  SubstComp │
     │        │        │      │
     └────────┴────────┴──────┘
                      │
         ┌────────────┼────────────┐
         ↓            ↓            ↓
    Weakening    SubstLemma    Reduction
         │            │            │
         └────────────┴────────────┘
                      │
              ┌───────┴───────┐
              ↓               ↓
           DefEq      SubjectReduction
              │               │
              └───────┬───────┘
                      ↓
              ┌───────┴───────┐
              ↓               ↓
         Inversion     TypeUniqueness
              │               │
              └───────┬───────┘
                      ↓
              ┌───────┴───────┐
              ↓               ↓
           WHNF          DefEqDecide
              │               │
              └───────┬───────┘
                      ↓
              TypeCheckerSoundness
                      │
                      ↓
                Environment
                      │
         ┌────────────┼────────────┐
         ↓            ↓            ↓
     Inductives   Recursors   Monotonicity
         │            │            │
         └────────────┴────────────┘
                      ↓
              ι-ReductionSound
                      │
                      ↓
              TypeCheckerComplete
                      │
                      ↓
                 Consistency
```

---

## Estimated Effort

| Layer | LOC | Holes | Difficulty | Status |
|-------|-----|-------|------------|--------|
| 1. Core Metatheory | ~1500 | ~30 | Medium | 80% |
| 2. Type Uniqueness | ~500 | ~10 | Medium | 0% |
| 3. Decidable TC | ~1000 | ~50 | Hard | 0% |
| 4. Environment | ~800 | ~30 | Medium | 0% |
| 5. Inductives | ~2000 | ~100 | Very Hard | 0% |
| 6. Consistency | ~300 | ~5 | Medium* | 0% |

*Consistency proof is "easy" once everything else is done - it's a consequence.

---

## Next Steps (Immediate)

1. **Complete DefEq.idr** - Fill holes for weakening/substitution preservation
2. **Complete SubjectReduction.idr** - Use DefEq for conversion cases
3. **Add Inversion.idr** - Pattern matching on typing derivations
4. **Add TypeUniqueness.idr** - Key lemma for bidirectional typing

After that:
- WHNF with fuel-based termination
- Decidable DefEq
- Decidable type checking
- Environment monotonicity

---

## References

1. **lean4lean** - https://github.com/digama0/lean4lean
   - Lean 4 type checker verified in Lean 4
   - ~15k LOC of proofs

2. **Coq in Coq** - Barras's thesis
   - Similar approach for Coq's kernel

3. **PLFA** - Programming Language Foundations in Agda
   - Accessible introduction to mechanized metatheory

4. **Intrinsically-Typed Interpreters** - Various papers
   - Our approach with intrinsic de Bruijn scoping
