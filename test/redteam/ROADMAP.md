# Red Team Roadmap: Untested Attack Surface

This document catalogs areas of the lean4idris type checker that haven't been fully tested, organized by feature area. Use this as a guide when new features are implemented.

## Priority Legend
- 🔴 **CRITICAL** - Potential soundness bug
- 🟠 **HIGH** - Likely exploitable
- 🟡 **MEDIUM** - Edge case, may cause issues
- 🟢 **LOW** - Unlikely to be exploitable

---

## 1. Environment Management (TCEnv)

**Files:** `TypeChecker.idr:27-54`

| Area | Risk | Status | Notes |
|------|------|--------|-------|
| `enableQuot` idempotency | 🟠 | Untested | What if called twice? |
| Declaration ordering | 🟡 | Untested | SortedMap insertion order effects |
| Empty environment operations | 🟡 | Untested | Lookups on fresh `emptyEnv` |
| `quotInit` state persistence | 🟠 | Untested | State across multiple operations |

**Test ideas:**
```
55-quot-enable-twice.export     # Call #QUOT twice
56-decl-ordering.export         # Add declarations in unusual order
```

---

## 2. Local Context (LocalCtx)

**Files:** `TypeChecker.idr:59-98, 538-700`

| Area | Risk | Status | Notes |
|------|------|--------|-------|
| `closeWithPlaceholders` collision | 🔴 | Partial | Uses `_local<name>`, can collide with user constants |
| `extendCtxLet` with circular values | 🟠 | Untested | `let x := f x in ...` |
| Context depth mismatches | 🟠 | Untested | Wrong depth passed to expression |
| Deep nesting fuel | 🟡 | Untested | >1000 nested binders |

**Test ideas:**
```
57-placeholder-local-collision.export  # User defines _local_x constant
58-let-self-reference.export           # let x := x in body
59-context-depth-mismatch.export       # Wrong scope depth
```

---

## 3. Iota Reduction (Recursor Application)

**Files:** `TypeChecker.idr:259-350`

| Area | Risk | Status | Notes |
|------|------|--------|-------|
| `getMajorIdx` with all zeros | 🟡 | Untested | numParams=numMotives=numMinors=0 |
| Constructor field extraction bounds | 🟠 | Partial | majorArgs shorter than expected |
| Rule matching failure | 🟡 | Untested | Constructor doesn't match any rule |
| `iterWhnfStep` fuel (100) | 🟡 | Untested | Expressions needing >100 steps |
| Nested/sparse applications | 🟡 | Untested | Complex arg patterns |

**Test ideas:**
```
60-rec-all-zero-params.export    # All counts are zero
61-iota-short-args.export        # Fewer args than expected
62-iota-no-matching-rule.export  # Constructor without rule
```

---

## 4. Projection Reduction

**Files:** `TypeChecker.idr:351-370, 697-700`

| Area | Risk | Status | Notes |
|------|------|--------|-------|
| **Projection typing** | 🔴 | UNIMPLEMENTED | Returns error, fails safe |
| Unknown struct name | 🟡 | Untested | Struct not in environment |
| Non-constructor after reduction | 🟠 | Untested | Projection target doesn't reduce |
| Struct name vs actual type | 🟠 | Partial | Test 49 covers partially |

**Test ideas:**
```
63-proj-unknown-struct.export     # Proj "NonExistent" 0 term
64-proj-non-constructor.export    # Proj on term that doesn't reduce
```

**Note:** Projection typing is unimplemented. When implemented, needs full test coverage.

---

## 5. Quotient Reduction

**Files:** `TypeChecker.idr:371-426`

| Area | Risk | Status | Notes |
|------|------|--------|-------|
| Use without `enableQuot` | 🟠 | Untested | Quot.lift before #QUOT |
| Quot.mk wrong arity | 🟡 | Untested | 2 or 4 args instead of 3 |
| fOrH not a function | 🟡 | Untested | Quot.lift with non-function |
| Remaining args edge cases | 🟡 | Untested | mkPos is last arg |

**Test ideas:**
```
65-quot-before-enable.export     # Use Quot.lift before #QUOT
66-quot-mk-wrong-arity.export    # Quot.mk with 2 args
67-quot-lift-non-function.export # Quot.lift with bad f
```

---

## 6. Definitional Equality (isDefEq)

**Files:** `TypeChecker.idr:708-905`

| Area | Risk | Status | Notes |
|------|------|--------|-------|
| **Proof irrelevance asymmetry** | 🔴 | Partial | Only checks `isProp(t)`, not `isProp(s)` - Test 44 |
| **`isDefEqBody` placeholder** | 🔴 | Partial | Uses `_x`, can collide - Tests 48, 54 |
| Eta expansion on partial apply | 🟡 | Untested | `s` not a function type |
| Eta infinite loop | 🟡 | Untested | Mutual eta expansion |
| Let comparison without reduction | 🟡 | Untested | Let in whnf form |

**Test ideas:**
```
68-proof-irrel-reverse.export    # Check s isProp, not just t
69-eta-partial-apply.export      # Eta on non-function
70-eta-mutual-loop.export        # Cyclic eta expansion
```

---

## 7. Type Inference (inferTypeOpen)

**Files:** `TypeChecker.idr:617-705`

| Area | Risk | Status | Notes |
|------|------|--------|-------|
| Pi domain universe (IMax) | 🟡 | Partial | Pathological IMax cases |
| Let type-value defeq | 🟡 | Untested | Types defeq but whnf differs |
| **Projection typing** | 🔴 | UNIMPLEMENTED | Returns error |

**Test ideas:**
```
71-pi-imax-pathological.export   # Complex IMax universe
72-let-defeq-whnf-diff.export    # Types defeq, whnf different
```

---

## 8. Declaration Validation (addDeclChecked)

**Files:** `TypeChecker.idr:928-1208`

| Area | Risk | Status | Notes |
|------|------|--------|-------|
| Inductive with no constructors | 🟡 | Untested | Empty inductive |
| Recursor without rules | 🟡 | Partial | Test 43 catches via parser |
| numMinors vs rules.length | 🟡 | Untested | Count mismatch |
| Safety field ignored | 🟢 | Known | Parsed but not enforced |

**Test ideas:**
```
73-inductive-no-ctors.export     # Inductive with zero constructors
74-rec-numminors-mismatch.export # numMinors != len(rules)
```

---

## 9. Substitution & Level Parameters

**Files:** `Subst.idr`, `Level.idr:120-173`

| Area | Risk | Status | Notes |
|------|------|--------|-------|
| Cyclic param detection gaps | 🟠 | Partial | Is occur check applied everywhere? |
| Level list length mismatch | 🟡 | Untested | len(names) != len(levels) |
| IMax simplification edge cases | 🟡 | Partial | Test 22 covers some |
| Simplify ordering | 🟡 | Untested | Order of operations |

**Test ideas:**
```
75-level-list-mismatch.export    # Wrong number of level args
76-imax-nested-edge.export       # Nested IMax edge cases
```

---

## 10. Parser & Export Format

**Files:** `Export/Parser.idr:220-649`

| Area | Risk | Status | Notes |
|------|------|--------|-------|
| Forward references | 🟡 | Partial | Test 4 covers basic |
| Circular expressions | 🟠 | Partial | Test 1 covers basic |
| BVar in closed expr | 🟡 | Partial | Test 2 covers basic |
| Hex string malformed | 🟢 | Untested | Invalid UTF-8 |

**Test ideas:**
```
77-forward-ref-complex.export    # Complex forward reference chain
78-hex-string-malformed.export   # Invalid hex in string literal
```

---

## 11. Unimplemented Features

| Feature | Location | Risk | Notes |
|---------|----------|------|-------|
| **Projection typing** | TypeChecker.idr:700 | 🔴 | Fails safe with error |
| Implicit arguments | All files | 🟡 | Parsed, not validated |
| Instance arguments | All files | 🟡 | Parsed, not validated |
| Strict implicit | All files | 🟡 | Parsed, not validated |
| OpaqueDecl special handling | TypeChecker.idr:1170 | 🟢 | Treated as DefDecl |

---

## Summary

| Category | Total | 🔴 | 🟠 | 🟡 | 🟢 |
|----------|-------|-----|-----|-----|-----|
| Environment | 4 | 0 | 2 | 2 | 0 |
| Local Context | 4 | 1 | 2 | 1 | 0 |
| Iota Reduction | 5 | 0 | 1 | 4 | 0 |
| Projection | 4 | 1 | 2 | 1 | 0 |
| Quotient | 4 | 0 | 1 | 3 | 0 |
| DefEq | 5 | 2 | 0 | 3 | 0 |
| Type Inference | 3 | 1 | 0 | 2 | 0 |
| Declarations | 4 | 0 | 0 | 3 | 1 |
| Substitution | 4 | 0 | 1 | 3 | 0 |
| Parser | 4 | 0 | 1 | 2 | 1 |
| Unimplemented | 5 | 1 | 0 | 3 | 1 |
| **TOTAL** | **46** | **6** | **10** | **27** | **3** |

---

## When to Revisit

Update this roadmap when:
1. Projection typing is implemented
2. Mathlib exports work (after fixing issue #1)
3. New declaration types are added
4. Quotient axiom validation is added

---

## Test File Numbering

Current tests: 01-54
Next available: 55+

Suggested allocation:
- 55-59: Environment & Context
- 60-64: Iota & Projection
- 65-70: Quotient & DefEq
- 71-74: Type Inference & Declarations
- 75-78: Substitution & Parser
