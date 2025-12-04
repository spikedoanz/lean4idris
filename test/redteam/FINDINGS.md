# Red Team Findings: lean4idris Type Checker

## Executive Summary

Red team testing of the lean4idris type checker identified **3 soundness bugs**, all of which have been **FIXED**:
1. Lambda body type not validated
2. Application argument type not checked
3. Let binding value type not checked

Total test cases: 26
Passing: 26
Failing: 0

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

### Bug #3: Let Binding Value Type Not Checked (FIXED)

**Severity**: CRITICAL
**Location**: `src/Lean4Idris/TypeChecker.idr`
**Status**: ✅ FIXED

#### Description

The `inferTypeOpen` function for `Let` expressions did not verify that the value expression has the declared type. It blindly extended the context with the let binding without checking type compatibility.

#### Fix Applied

```idris
inferTypeOpen env ctx (Let name tyExpr valExpr body) = do
  tyTy <- inferTypeOpen env ctx tyExpr
  _ <- ensureSort env tyTy
  let tyClosed = closeWithPlaceholders ctx tyExpr
  let valClosed = closeWithPlaceholders ctx valExpr
  -- Check value has the declared type
  valTy <- inferTypeOpen env ctx valExpr
  tyClosed' <- whnf env tyClosed
  valTy' <- whnf env valTy
  if tyClosed' == valTy'
    then do
      let ctx' = extendCtxLet name tyClosed valClosed ctx
      inferTypeOpen env ctx' body
    else Left (LetTypeMismatch tyClosed valTy)
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

**Test #11** (`bvar-escape-lambda.export`) was originally expected to be rejected, but analysis shows it defines a valid identity function `λ(x : Nat). x` where `BVar 0` correctly refers to the lambda parameter. The test expectation was updated to "accept".

**Tests #14 and #26** (`14-let-type-dependency.export` and `26-let-value-type-mismatch.export`) had incorrect export file definitions that did not actually test the let binding type mismatch bug. The original files used expression indices that resulted in valid type assignments:
- Original test 14 defined `let x : Prop := True in x` where `True : Prop` - this is valid
- Original test 26 defined `let x : Nat := zero in x` where `zero : Nat` - this is also valid

Both test files were corrected to actually test `let x : Bool := zero in x` where `zero : Nat`. This creates a genuine type mismatch (Bool vs Nat) that the type checker must reject. The fix involved changing the type expression index in the `#EZ` command from referring to `Nat` (expr 2) to `Bool` (expr 3).

---

## Historical Bugs Tested

The expanded test suite includes tests based on known Lean kernel bugs:

| Bug | Test | Status |
|-----|------|--------|
| lean4#10475 (inferLet) | 14, 26 | **REPRODUCED** - Let binding type not checked |
| lean4#10511 (Substring) | N/A | Not applicable to type checker |
| looseBVarRange overflow | 23 | Parser catches large BVar indices |
| Primitive validation | 16, 17, 20, 21 | Handled via unknown constant errors |
| Level param handling | 18, 19 | Correctly validated |
| imax(u,0) exploit | 22 | Correctly rejected |
| Proof irrelevance abuse | 25 | Correctly rejected |

---

## Test Summary

| Total Tests | Passed | Failed |
|-------------|--------|--------|
| 26 | 26 | 0 |

All soundness bugs have been fixed.

Sources:
- [lean4#10475](https://github.com/leanprover/lean4/issues/10475) - inferLet bug
- [lean4#10511](https://github.com/leanprover/lean4/issues/10511) - Substring reflexivity
- [Lean4Lean paper](https://arxiv.org/abs/2403.14064) - looseBVarRange bug

---

## Files

- Test cases: `test/redteam/soundness/*.export`
- Test runner: `test/redteam/Main.idr`
- Build: `cd test/redteam && pack build redteam.ipkg`
- Run: `cd <project_root> && ./test/redteam/build/exec/lean4idris-redteam`
