# The Nat.le.below.casesOn Placeholder Scope Issue

**Status**: Known limitation, not yet resolved
**Impact**: Blocks type checking at declaration 195+ in Init.Prelude.export and Init.Core.export
**Date documented**: 2024-12-04

---

## Summary

The type checker fails on `Nat.le.below.casesOn` with an "application type mismatch" error. The root cause is a **placeholder scope leakage problem** where placeholder types created during one comparison context contain references to placeholders from a different context, causing type confusion.

---

## The Error

```
Checking: Just Nat.le.below.casesOn... FAIL
Type error: application type mismatch:
  expected: ((a._@._internal._hyg.0 : Nat) -> ((t : (Nat.le n.15._isDefEqBody a._@._internal._hyg.0)) -> Sort 0))
  got:      ((a._@._internal._hyg.0 : Nat) -> ((t : (Nat.le n.15._isDefEqBody a._@._internal._hyg.0)) -> ((t : (Nat.le.below n.15._isDefEqBody motive.16._isDefEqBody a._@._internal._hyg.0 t)) -> Sort 0)))
```

Key observation: The **inferred type has an extra Pi binder** compared to the expected type.

---

## Technical Background

### Placeholder Naming Conventions

The type checker uses placeholder constants to handle open terms (terms with free variables). There are two kinds:

1. **Inference placeholders**: Created during type inference when closing open terms
   - Format: `Str "_local" (Num counter binderName)`
   - Example: `α.0._local`, `motive.5._local`

2. **Comparison placeholders**: Created during definitional equality checking (`isDefEq`)
   - Format: `Str "_isDefEqBody" (Str counter binderName)`
   - Example: `n.15._isDefEqBody`, `motive.16._isDefEqBody`

### How Placeholder Comparison Works

When comparing two Pi types `(x : A) → B` and `(x : A') → B'`:
1. Check `A =?= A'` (domains equal)
2. Create a fresh comparison placeholder `x.N._isDefEqBody`
3. Substitute the placeholder into both bodies
4. Check `B[x := placeholder] =?= B'[x := placeholder]`

The placeholder is registered in `env.placeholders` with its type, so subsequent type inference can find its type.

### The Problem: Placeholder Type Leakage

When a placeholder is created, its type is stored. But that type might itself **contain other placeholders** from enclosing scopes. Consider this scenario:

```
Comparing motive types where motive's type references itself:
  motive : (a : Nat) → (t : Nat.le n a) → (t : Nat.le.below n motive a t) → Sort 0
                                                        ^^^^^ self-reference!
```

When we create `motive.16._isDefEqBody` as a comparison placeholder, its registered type contains `motive` (the binder name). But there might be a *different* placeholder `motive.5._isDefEqBody` from an outer scope, and the type ends up mixing them.

---

## Nat.le.below.casesOn Structure

`Nat.le.below.casesOn` is an auxiliary eliminator for the `Nat.le.below` type, which is used internally by Lean for well-founded recursion on `Nat.le` proofs.

### Type Signature (simplified)

```lean
Nat.le.below.casesOn :
  {n : Nat} →
  {motive : (a : Nat) → (t : Nat.le n a) → (t : Nat.le.below n motive a t) → Sort u} →
  ... constructors ...
```

The critical part is that `motive`'s type **references motive itself**:
```
motive : (a : Nat) → (t : Nat.le n a) → (t : Nat.le.below n motive a t) → Sort u
                                                        ^^^^^
```

This self-referential structure is the trigger for the bug.

### Why Self-Reference Causes Problems

1. When checking `Nat.le.below.casesOn`, we need to verify the motive type
2. During comparison, we create placeholder `motive.N._isDefEqBody`
3. We look up the placeholder's type from `env.placeholders`
4. That type contains another `motive` reference (could be from a different context)
5. The types mix up different placeholder scopes, causing the "extra Pi binder" error

---

## Code Locations

### Key Functions

- **`closeWithPlaceholders`** (line ~1022): Converts open terms to closed terms by replacing bound variables with placeholder constants

- **`isDefEqBodyWithNameAndType`** (line ~1976): The core function that creates comparison placeholders and compares Pi bodies

- **`addPlaceholder`** (line ~75): Registers a placeholder with its type in the environment

- **`lookupPlaceholder`** (line ~83): Looks up a placeholder's type

- **`areEquivalentPlaceholders`** (line ~2093): Checks if two placeholder names refer to the same binder (handles aliasing)

### Placeholder State in TCEnv

```idris
record TCEnv where
  constructor MkTCEnv
  decls : SortedMap Name Declaration
  quotInit : Bool
  placeholders : SortedMap Name ClosedExpr    -- Placeholder types
  binderAliases : SortedMap Name Name         -- Binder → comparison placeholder mapping
  nextPlaceholder : Nat                        -- Counter for unique names
```

---

## Debugging Output (Historical)

During investigation, debug output showed:

```
lookupPlaceholder motive.17._isDefEqBody = Just ((a._@._internal._hyg.0 : Nat) ->
  ((t : (Nat.le n.15._isDefEqBody a._@._internal._hyg.0)) ->
    ((t : (Nat.le.below n.15._isDefEqBody motive.16._isDefEqBody a._@._internal._hyg.0 t)) ->
      Sort 0)))
```

Key observations:
1. `motive.17._isDefEqBody` has type containing `motive.16._isDefEqBody`
2. This means when we look up `motive.17`, we get a type mentioning `motive.16`
3. These are supposed to be the "same" motive from different comparison contexts
4. But the placeholder replacement mechanism doesn't handle this cross-context reference

---

## Why Other Declarations Pass

Most declarations don't have this issue because:
1. Their motive types don't reference themselves
2. Placeholder scopes don't cross-contaminate
3. The comparison placeholders all resolve to the same canonical form

`Nat.le.below.casesOn` (and similar `*.below.casesOn` declarations) are special because:
1. They use auxiliary `below` types for well-founded recursion
2. The motive's type explicitly mentions the motive
3. This creates nested placeholder contexts that interact incorrectly

---

## Potential Solutions

### Option 1: Normalize Placeholder Types

When storing a placeholder's type, first normalize it to replace any existing comparison placeholders with fresh inference placeholders tied to the binder name only (not counter).

**Pros**: Conceptually clean
**Cons**: Complex to implement correctly, might have other side effects

### Option 2: Unification-Based Approach

Instead of tracking exact placeholder types, use a unification-based approach where placeholders are treated as metavariables that get unified during comparison.

**Pros**: More robust, closer to how real proof assistants work
**Cons**: Major architectural change, need constraint solving

### Option 3: Skip Self-Referential Motive Validation

Special-case the validation to skip checking motive types that reference themselves, trusting that Lean's kernel already validated them.

**Pros**: Simple workaround
**Cons**: Reduces type checking coverage, not a real fix

### Option 4: Placeholder Canonicalization

Track a canonical form for each binder name across all contexts. When comparing placeholders, map them to canonical names first.

**Pros**: Directly addresses the aliasing issue
**Cons**: Need to thread canonical mappings through all comparison paths

---

## Related Work

### lean4lean

The reference Lean 4 in Lean 4 implementation (`lean4lean`) likely handles this through its environment design. It would be worth studying how it manages placeholder types during definitional equality checking.

### Lean 4 Kernel

The actual Lean 4 kernel in C++ handles this through its metacontext and metavariable system. Our implementation simplified this by using placeholder constants instead of true metavariables.

---

## Test Case Location

The failing test is in:
- `test/exports/tier1-core/Init.Prelude.export` (declaration 195+)
- `test/exports/tier1-core/Init.Core.export` (declaration 193+)

Both fail at `Nat.le.below.casesOn` with the same error pattern.

---

## Impact Assessment

**Current state**:
- 194 declarations pass in Init.Prelude before hitting this
- 193 declarations pass in Init.Core before hitting this
- All 67 red team soundness tests pass
- This is a **completeness** issue, not a **soundness** issue

The type checker correctly rejects invalid proofs. It just can't verify this particular (valid) declaration due to the placeholder scope limitation.

---

## Appendix: Nat.le.below Type Structure

For reference, here's what `Nat.le.below` looks like conceptually:

```lean
-- Nat.le.below is an auxiliary type for well-founded recursion on Nat.le
-- It captures "all the data below" a given Nat.le proof

inductive Nat.le.below (n : Nat) (motive : (a : Nat) → Nat.le n a → Sort u)
    : (a : Nat) → Nat.le n a → Sort (max 1 u) where
  | refl : Nat.le.below n motive n Nat.le.refl
  | step : {a : Nat} → (h : Nat.le n a) →
           motive a h →
           Nat.le.below n motive a h →
           Nat.le.below n motive (a + 1) (Nat.le.step h)
```

The key is that `motive` appears both as:
1. A parameter to `Nat.le.below`
2. Inside the type of `motive` itself (through `Nat.le.below n motive a t`)

This circularity is what triggers the placeholder scope issue.
