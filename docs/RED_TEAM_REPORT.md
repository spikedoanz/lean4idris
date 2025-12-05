# lean4idris Red Team Security Report

**Date:** 2024-12-04
**Tester:** Claude (Opus 4.5)
**Total Tests:** 68
**Passed:** 60
**Failed (Potential Bugs):** 8

## Executive Summary

Red team testing of the lean4idris type checker revealed **8 potential issues**, categorized as:
- **3 True Soundness Bugs** - Type checker accepts invalid terms
- **4 Test Expectation Issues** - Tests may have incorrect expectations or be edge cases
- **1 Missing Feature** - Valid input rejected due to incomplete implementation

## Critical Findings

### 1. Deep Application Nesting Accepted (Test 06)

**Severity:** MEDIUM
**File:** `06-deep-nesting.export`
**Status:** Type checker ACCEPTED when it should REJECT

**Description:**
Deep self-application `((((Sort 0) (Sort 0)) (Sort 0)) ...)` is accepted as an axiom type.
The expression applies `Sort 0` to itself repeatedly, which should be a type error
since `Sort 0` (Prop) is not a function.

**Root Cause:**
The type inference for deeply nested applications may be failing silently or
the `ensurePi` function is trusting placeholder types too liberally.

**Impact:**
Could allow accepting ill-typed terms through deeply nested applications.

**Recommendation:**
Review `inferTypeE` for App case and ensure `ensurePi` fails properly when
type inference produces non-Pi types.

---

### 2. Recursor Wrong Major Premise Accepted (Test 24)

**Severity:** MEDIUM
**File:** `24-recursor-wrong-major.export`
**Status:** Type checker ACCEPTED when it should REJECT

**Description:**
A recursor application `Nat.rec Bool` is accepted where `Bool` is used as the
major premise instead of a `Nat` value.

**Root Cause:**
The recursor application is not validating that the major premise has the correct
inductive type. The type checker seems to only check function application types
without verifying the recursor-specific constraints.

**Impact:**
Could allow using recursors with wrong major premises, potentially leading to
unsound reduction.

**Recommendation:**
Add special validation for recursor applications checking the major premise type
matches the recursor's inductive type.

---

### 3. Recursor Rule Arbitrary RHS Accepted (Test 33)

**Severity:** HIGH
**File:** `33-rec-rule-arbitrary-rhs.export`
**Status:** Type checker ACCEPTED when it should REJECT

**Description:**
A recursor rule with `Sort 0` (Prop) as the RHS is accepted, when it should
require the RHS to have the proper type based on the motive application.

**Root Cause:**
`addDeclChecked` for `RecDecl` only validates the recursor type itself but
does not type-check each recursor rule's RHS against the expected type
(motive applied to the constructor).

**Impact:**
**CRITICAL** - This allows defining recursors with arbitrary computation rules,
potentially breaking subject reduction and type safety.

**Recommendation:**
Add validation in `addDeclChecked` for `RecDecl` that:
1. For each rule, compute expected type from motive + constructor
2. Type check rule.rhs and verify it matches expected type

---

### 4. Recursor Rule RHS Untyped Accepted (Test 41)

**Severity:** HIGH
**File:** `41-rec-rule-rhs-untyped.export`
**Status:** Type checker ACCEPTED when it should REJECT

**Description:**
Similar to test 33 - recursor rule with `Sort 1` as RHS is accepted.

**Root Cause:**
Same as test 33 - recursor rules are not validated.

**Impact:**
Same as test 33 - unsound computation rules.

**Recommendation:**
Same as test 33.

---

### 5. IMax with Param Simplification Issue (Test 45)

**Severity:** LOW
**File:** `45-imax-param-unsimplified.export`
**Status:** Type checker ACCEPTED when it should REJECT

**Description:**
Definition with type `Sort (imax 0 u)` is accepted when the value has type
`T.{u}` (which is `Sort (imax 0 u)` after instantiation).

**Analysis:**
This may actually be **correct behavior**. The test defines:
- `T.{u} : Sort (imax 0 u)`
- `bad.{u} : Sort (imax 0 u) := T.{u}`

If `T.{u}` has type `Sort (imax 0 u)` then `bad` declaring type `Sort (imax 0 u)`
with value `T.{u}` should type-check since `typeof(T.{u}) = Sort (imax 0 u)`.

**Recommendation:**
Review test expectation - this may be correct acceptance.

---

### 6. Placeholder Name Collision (Test 57)

**Severity:** MEDIUM
**File:** `57-placeholder-name-collision.export`
**Status:** Type checker ACCEPTED when it should REJECT

**Description:**
User creates a constant named `_local.0._local` which could collide with
internal placeholder names used by `closeWithPlaceholders`.

**Root Cause:**
The placeholder naming scheme `_local.N.name` can theoretically collide with
user-defined constants. The test creates a constant that mimics this pattern.

**Impact:**
Could cause confusion in definitional equality checks or type inference
when user constants match placeholder patterns.

**Recommendation:**
Use a more unique prefix for placeholders that's less likely to collide,
such as `__lean4idris_internal_placeholder_` or similar.

---

### 7. Subst0Single Depth Exploit (Test 63)

**Severity:** LOW
**File:** `63-subst0single-depth-exploit.export`
**Status:** Type checker ACCEPTED when it should REJECT

**Description:**
Nested lambda/pi with de Bruijn indices at multiple depths is accepted.

**Analysis:**
This test defines:
- `bad : (x : Nat) -> (y : Nat) -> Nat`
- Value: `λx.λy. BVar 1` (referring to outer x)

This is actually **valid** - in a well-scoped context, `BVar 1` under two
lambdas refers to `x` which has type `Nat`, matching the declared return type.

**Recommendation:**
Review test expectation - this appears to be correct acceptance.

---

### 8. W-Type Recursive Argument (Test 70)

**Severity:** LOW - False Positive
**File:** `70-recursive-inductive-arg.export`
**Status:** Type checker REJECTED when it should ACCEPT

**Description:**
W-type (well-founded tree) definition with recursive occurrence in function
codomain is rejected.

**Root Cause:**
The export file may be malformed, or the type checker doesn't properly
handle complex recursive inductive types during parsing.

**Impact:**
Prevents accepting valid W-type definitions.

**Recommendation:**
Review W-type encoding and ensure parser handles complex inductive families.

---

## Summary of True Soundness Bugs

| Test | Description | Severity | Status |
|------|-------------|----------|--------|
| 33 | Recursor rule arbitrary RHS | HIGH | Needs Fix |
| 41 | Recursor rule untyped RHS | HIGH | Needs Fix |
| 06 | Deep application nesting | MEDIUM | Needs Investigation |
| 24 | Recursor wrong major premise | MEDIUM | Needs Investigation |
| 57 | Placeholder name collision | MEDIUM | Needs Fix |

## Recommended Fixes (Priority Order)

### Priority 1: Recursor Rule Validation
```idris
addDeclChecked env decl@(RecDecl info levelParams) = do
  checkNameNotDeclared env info.name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env info.type
  -- ADD: Validate each recursor rule
  validateRecursorRules env info
  Right (addDecl decl env)

validateRecursorRules : TCEnv -> RecursorInfo -> TC ()
validateRecursorRules env info = do
  for_ info.rules $ \rule => do
    -- Compute expected type from motive + constructor args
    expectedTy <- computeRuleExpectedType env info rule
    -- Type check RHS
    actualTy <- inferType env rule.rhs
    -- Compare
    eq <- isDefEq env expectedTy actualTy
    unless eq $ Left (OtherError "recursor rule type mismatch")
```

### Priority 2: Placeholder Prefix
Change `_local` to a more unique prefix in `placeholderName`:
```idris
placeholderName : Name -> Nat -> Name
placeholderName n counter = Str "__lean4idris_ph__" (Num counter n)
```

### Priority 3: Recursor Application Validation
In type inference for recursor applications, add check that major premise
has the correct inductive type.

## Tests to Update

Tests 45, 63 appear to have incorrect expectations - review and update:
- Test 45: May be correct acceptance
- Test 63: Appears to be correct acceptance

Test 70 needs the export file fixed for proper W-type encoding.

## Conclusion

The lean4idris type checker has robust handling for many attack vectors but
has **critical gaps in recursor rule validation**. The recursor rules are
added to the environment without checking that their RHS terms have the
correct types. This could allow defining unsound computation rules that
violate type preservation.

Immediate action should focus on adding recursor rule type validation
before this implementation is used in any security-sensitive context.
