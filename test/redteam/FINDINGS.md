# Red Team Findings: lean4idris Type Checker

## Executive Summary

Red team testing of the lean4idris type checker identified **2 soundness bugs** which have been **FIXED**. All 13 security tests now pass.

## Fixed Soundness Bugs

### Bug #1: Lambda Body Type Not Validated (FIXED)

**Severity**: CRITICAL
**Location**: `src/Lean4Idris/TypeChecker.idr`
**Status**: ✅ FIXED

#### Description

The `inferType` function for lambda expressions did not verify that the body has the correct type. It blindly returned `Pi ty body` regardless of whether `body` actually had a type compatible with the expected codomain.

#### Root Cause (before fix)

```idris
inferType env (Lam name bi ty body) = do
  _ <- inferType env ty >>= ensureSort env
  Right (Pi name bi ty body)  -- NOT FULLY CORRECT - doesn't check body type!
```

#### Fix Applied

Lambda expressions now delegate to `inferTypeOpen` which properly handles local contexts and validates the body type:

```idris
inferType env (Lam name bi ty body) =
  inferTypeOpen env emptyCtx (Lam name bi ty body)
```

The `inferTypeOpen` function extends the local context with the lambda parameter and infers the body type in that extended context.

---

### Bug #2: Application Argument Type Not Checked (FIXED)

**Severity**: CRITICAL
**Location**: `src/Lean4Idris/TypeChecker.idr`
**Status**: ✅ FIXED

#### Description

The `inferType` function for applications did not verify that the argument type matches the function's domain type.

#### Fix Applied

```idris
inferType env (App f arg) = do
  fTy <- inferType env f
  (_, _, dom, cod) <- ensurePi env fTy
  -- Verify argument type matches domain
  argTy <- inferType env arg
  argTy' <- whnf env argTy
  dom' <- whnf env dom
  if argTy' == dom'
    then Right (subst0 cod arg)
    else Left (AppTypeMismatch dom argTy)
```

---

## Other Observations

### Parser Robustness

The parser correctly rejects several attack vectors:

| Attack | Result | Notes |
|--------|--------|-------|
| Circular references | REJECT | "Invalid expr index: 3" |
| Free bound variables | REJECT | "Expression 1 invalid at depth 0" |
| Forward references | REJECT | "Invalid expr index: 99" |
| Universe level gaps | REJECT | "Invalid level index: 1" |

### Type Checker Robustness

The type checker correctly rejects:

| Attack | Result | Notes |
|--------|--------|-------|
| Type mismatch in def | REJECT | "definition type mismatch" |
| Self-referential def | REJECT | "unknown constant: loop" |
| Deep nesting | REJECT | "function expected" |
| Wrong Pi codomain universe | REJECT | "definition type mismatch" |
| Wrong application arg type | REJECT | "application type mismatch" |
| Lambda body type mismatch | REJECT | "definition type mismatch" |

### Incomplete but Safe

| Feature | Status | Notes |
|---------|--------|-------|
| Projections | Error | "projection not yet supported" |
| Unknown constants | Error | Correctly detected |

### Corrected Test Cases

Test #11 (`bvar-escape-lambda.export`) was originally expected to be rejected, but analysis shows it defines a valid identity function `λ(x : Nat). x` where `BVar 0` correctly refers to the lambda parameter. The test expectation was updated to "accept".

---

## Test Summary

| Total Tests | Passed | Failed |
|-------------|--------|--------|
| 13 | 13 | 0 |

All soundness tests now pass.

---

## Files

- Test cases: `test/redteam/soundness/*.export`
- Test runner: `test/redteam/Main.idr`
- Build: `cd test/redteam && pack build redteam.ipkg`
- Run: `cd <project_root> && ./test/redteam/build/exec/lean4idris-redteam`
