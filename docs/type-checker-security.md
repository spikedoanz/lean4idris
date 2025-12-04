# Type Checker Security: Failure Modes and Attack Vectors

This document catalogs common vulnerabilities in dependent type checker implementations, using the lean4idris type checker as a case study. Understanding these attack vectors is essential for anyone implementing or auditing a proof assistant kernel.

## Why Type Checker Security Matters

A type checker for a proof assistant is a **trust anchor**. When it accepts a proof of `theorem P`, users trust that P is actually true. If the type checker has bugs:

1. **False proofs become possible** - proving `False` means proving anything
2. **Unsafe code extraction** - "verified" programs may crash or have security holes
3. **Blockchain/smart contract exploits** - verified contracts may be unsound
4. **Formal verification is worthless** - the entire point is defeated

The attack surface is the **kernel**: the minimal trusted code that validates proofs. Everything outside the kernel (tactics, elaboration, pretty printing) can have bugs without affecting soundness.

---

## Attack Vector Taxonomy

### 1. Parser-Level Attacks

These attacks exploit the parser/deserializer to construct malformed internal representations that bypass later checks.

#### 1.1 Circular References

**Attack**: Create expressions that reference each other, forming cycles.

```
# Expression 2 references expression 3, expression 3 references expression 2
2 #EA 3 1    -- App(expr3, expr1)
3 #EA 2 1    -- App(expr2, expr1)
```

**Impact**: Infinite loops during type checking, potential stack overflow, or confused type inference.

**Defense**: Validate that expression indices only reference previously-defined expressions. In lean4idris, the parser rejects with "Invalid expr index".

#### 1.2 Forward References

**Attack**: Reference expressions that haven't been defined yet.

```
1 #EA 99 1   -- References expr 99, but only expr 1 exists
```

**Impact**: Memory corruption, use of uninitialized data, or crashes.

**Defense**: Bounds checking on all index lookups. Parser should reject invalid indices.

#### 1.3 Free Bound Variables

**Attack**: Use a bound variable (de Bruijn index) outside its binding scope.

```
# BVar 0 at top level (not inside any lambda/pi)
1 #EV 0
#AX myAxiom 1   -- axiom with type = BVar 0 ???
```

**Impact**: If accepted, could allow type confusion or accessing arbitrary memory.

**Defense**: Well-scoped expression types (`Expr n` where `n` is the binding depth). In lean4idris, `Expr 0` (closed expressions) cannot contain `BVar` at all - it's statically impossible. The parser validates depth during construction.

#### 1.4 Universe Level Gaps

**Attack**: Reference universe levels that don't exist.

```
1 #US 0        -- level 1 = succ(level 0), but level 0 is base
1 #ES 2        -- Sort(level 2), but only level 1 exists!
```

**Impact**: Use of uninitialized level data, potential for universe inconsistency.

**Defense**: Track defined levels and reject invalid indices.

---

### 2. Type Inference Attacks

These attacks exploit gaps in the type inference/checking logic.

#### 2.1 Lambda Body Type Not Checked

**Attack**: Create a lambda where the body type doesn't match the expected return type.

```idris
-- Declare: bad : Nat → Bool
-- Define:  bad = λ(x : Nat). Bool   -- returns TYPE Bool, not VALUE of type Bool!
```

**Impact**: Construct inhabitants of any type. If `bad : Nat → Bool` but `bad n` actually returns a Type, you can cast between arbitrary types.

**Proof of exploit**:
```
-- bad : Nat → Bool := λx. Bool
-- Now (bad 0) has declared type Bool but actual type Type
-- Use this to confuse the type system
```

**Defense**: When type-checking `λ(x : A). body`, extend the local context with `x : A`, infer the type of `body` in that context, and verify it matches the expected return type.

**lean4idris fix**: Delegate lambda type inference to `inferTypeOpen` which properly extends the local context.

#### 2.2 Application Argument Type Not Checked

**Attack**: Apply a function to an argument of the wrong type.

```idris
-- f : Nat → Nat
-- bad : Nat := f Bool   -- applying f to Bool instead of Nat!
```

**Impact**: Type confusion. If the checker doesn't verify the argument type matches the domain, any type can flow where another is expected.

**Defense**: In the App case, after inferring `f : (x : A) → B`, infer the type of `arg` and verify it equals `A` (up to definitional equality).

**lean4idris fix**: Added argument type check in `inferType` for `App`.

#### 2.3 Pi Codomain Universe Not Validated

**Attack**: Declare a Pi type with a codomain in the wrong universe.

```idris
-- Claim: T : Type 0
-- But T = (x : Type 0) → Type 1   -- codomain is Type 1, not Type 0!
```

**Impact**: Universe inconsistency. Could lead to Type : Type or similar paradoxes.

**Defense**: For `(x : A) → B`, the universe of the Pi is `max(univ(A), univ(B))` (with special rules for Prop). Verify declared universe matches computed universe.

#### 2.4 Let Binding Value Type Mismatch

**Attack**: Create a let binding where the value type doesn't match the declared type.

```idris
let x : Bool = Nat in ...   -- x declared as Bool, bound to type Nat
```

**Impact**: Type confusion in the body of the let.

**Defense**: Verify `value : declaredType` before extending context.

---

### 3. Definition Validation Attacks

These attacks target the declaration validation phase.

#### 3.1 Self-Referential Definitions

**Attack**: Define a constant in terms of itself (non-recursive context).

```idris
def loop : Type := loop   -- refers to itself before being added to env
```

**Impact**: If the definition value is checked before the name exists, this should fail. If not, could create logical inconsistency.

**Defense**: Check definition values in an environment that does NOT include the definition being checked (unless it's properly recursive via a recursor).

**lean4idris behavior**: Correctly rejects with "unknown constant: loop".

#### 3.2 Duplicate Declarations

**Attack**: Declare the same name twice with different types/values.

```idris
axiom Nat : Type
axiom Nat : Prop   -- redefine Nat as Prop!
```

**Impact**: Type confusion. Code expecting `Nat : Type` may interact with code using `Nat : Prop`.

**Defense**: Check name freshness before adding any declaration.

#### 3.3 Duplicate Universe Parameters

**Attack**: Declare a definition with duplicate universe parameter names.

```idris
def T.{u, u} : Sort u := Sort u   -- two params named 'u'
```

**Impact**: Ambiguity in level instantiation. Could cause incorrect level substitution.

**Defense**: Check universe parameter list for duplicates.

#### 3.4 Theorem Not a Prop

**Attack**: Declare a theorem whose type is not a proposition.

```idris
theorem T : Nat := 0   -- Nat is not a Prop!
```

**Impact**: Theorems are treated specially (proof irrelevance, erasure). A non-Prop theorem breaks these assumptions.

**Defense**: Verify theorem types live in `Prop` (Sort 0) before accepting.

#### 3.5 Definition Type Mismatch

**Attack**: Declare a definition with a type that doesn't match its value.

```idris
def bad : Bool := Nat   -- value has type Type, declared type is Bool
```

**Impact**: The declared type is what other code sees. If it doesn't match the value, type safety is violated.

**Defense**: Infer value type and check definitional equality with declared type.

---

### 4. Reduction and Equality Attacks

#### 4.1 Non-Terminating Reduction

**Attack**: Construct terms that don't terminate during reduction.

```idris
-- If recursive definitions aren't guarded:
def omega : Nat := omega   -- loops forever
```

**Impact**: Type checker hangs. Denial of service, or worse if timeouts aren't handled safely.

**Defense**:
- Use fuel/gas for reduction steps
- Require termination proofs for recursive definitions
- Lean's kernel uses well-founded recursion

#### 4.2 Eta Expansion Bypass

**Attack**: Exploit missing eta-equality to distinguish extensionally equal functions.

```idris
-- These should be equal:
f : Nat → Nat
λx. f x : Nat → Nat

-- If eta isn't implemented, they may be considered different
```

**Impact**: Proofs that should work don't. Less severe than accepting invalid proofs, but still a bug.

**Defense**: Implement eta expansion in definitional equality.

#### 4.3 Proof Irrelevance Bypass

**Attack**: Distinguish proofs of the same proposition.

```idris
-- p1 : P and p2 : P should be equal (proof irrelevance)
-- If not, proofs leak computational content
```

**Impact**: Can observe differences between proofs, breaking the assumption that Prop is erasable.

**Defense**: In definitional equality, if both terms have type in Prop, consider them equal.

---

### 5. Inductive Type Attacks

#### 4.1 Positivity Violation

**Attack**: Define an inductive type where the recursive occurrence is negative.

```idris
-- BAD: recursive occurrence in negative position
inductive Bad where
  | mk : (Bad → Bool) → Bad   -- Bad occurs left of arrow!
```

**Impact**: Enables defining non-terminating functions without recursion, proving False.

**Defense**: Strict positivity checking. The type being defined can only appear in strictly positive positions (right of all arrows).

#### 4.2 Universe Inconsistency in Inductives

**Attack**: Place a large type inside a small universe via inductive definition.

```idris
-- Try to put Type inside Prop
inductive Wrap : Prop where
  | mk : Type → Wrap   -- Type is too large!
```

**Impact**: Universe inconsistency, type-in-type, logical paradox.

**Defense**: Universe checking for inductive constructors. Large elimination restrictions for Prop.

#### 4.3 Recursor Rule Mismatch

**Attack**: Define recursor rules that don't match the constructors.

```idris
-- Claim recursor handles all cases, but skip one
-- Or compute the wrong type in a rule
```

**Impact**: Partial functions, type mismatches in iota reduction.

**Defense**: Verify recursor rules cover all constructors with correct types.

---

### 6. Quotient Type Attacks

#### 6.1 Premature Quot Reduction

**Attack**: Reduce quotient operations before the quotient module is initialized.

```idris
-- Before quotient axioms are added:
Quot.lift f h (Quot.mk r a)   -- shouldn't reduce yet!
```

**Impact**: Could allow inconsistent reasoning about quotients.

**Defense**: Track quotient initialization in environment. Only enable Quot reduction after `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` are all defined.

**lean4idris implementation**: Uses `quotInit` flag in `TCEnv`.

#### 6.2 Missing Quot Axiom

**Attack**: Use quotient operations without all axioms present.

**Impact**: Incomplete axiom set may allow deriving contradictions.

**Defense**: Verify all quotient constants exist before enabling quotient reduction.

---

### 7. Resource Exhaustion Attacks

#### 7.1 Deep Nesting

**Attack**: Create extremely deeply nested expressions.

```idris
-- 10000 nested applications
App(App(App(...App(f, x)...), x), x)
```

**Impact**: Stack overflow, memory exhaustion.

**Defense**: Depth limits, iterative instead of recursive processing.

#### 7.2 Exponential Blowup

**Attack**: Expressions that expand exponentially during normalization.

```idris
-- let x = <big> in (x, x)  -- doubles size
-- Nest multiple times for exponential growth
```

**Impact**: Time/space exhaustion.

**Defense**: Fuel limits, sharing-aware reduction (hash-consing).

---

## Defense Principles

### 1. Well-Scoped by Construction

Use indexed types to make invalid states unrepresentable:

```idris
-- de Bruijn indices are bounded by context size
data Expr : Nat -> Type where
  BVar : Fin n -> Expr n              -- Can't have free variables!
  Lam : Expr (S n) -> Expr n          -- Body has one more binding
```

### 2. Validate at Parse Time

Reject malformed input immediately:
- Check all indices in bounds
- Verify well-scopedness
- Reject cycles

### 3. Verify Everything in Type Inference

Never trust structure; always verify:
- Lambda: check body type in extended context
- Application: check argument type matches domain
- Let: check value type matches declared type
- Pi: compute universe from components

### 4. Fail Safe

When in doubt, reject:
```idris
case complexCheck of
  Left err => reject
  Right ok => proceed
```

### 5. Limit Resources

Prevent denial of service:
- Fuel for reduction
- Depth limits for recursion
- Timeouts for long operations

---

## Testing Strategy

### 1. Parser Fuzzing

Generate random byte sequences and expression trees. Verify:
- No crashes
- No memory corruption
- Clear error messages

### 2. Soundness Test Suite

Craft specific attack vectors (like in `test/redteam/`):
- Each test tries one attack
- Expected result: REJECT
- Failure means soundness bug

### 3. Property Testing

Generate random well-formed terms and verify:
- Type inference terminates
- Inferred types are valid
- Reduction preserves types (subject reduction)

### 4. Reference Testing

Compare against a known-correct implementation:
- Same terms should get same types
- Same equality judgments

---

## Summary Table

| Attack Class | Example | Impact | Defense |
|--------------|---------|--------|---------|
| Circular refs | Expr cycle | Infinite loop | Forward-only references |
| Free bvars | BVar outside scope | Type confusion | Well-scoped types |
| Lambda body | Wrong return type | False proofs | Check body in context |
| App arg | Wrong arg type | Type confusion | Check arg type |
| Self-ref def | `x := x` | Inconsistency | Check before adding |
| Non-termination | Infinite reduction | DoS | Fuel limits |
| Positivity | Negative occurrence | False proofs | Strict positivity |
| Universe escape | Large in small | Type-in-type | Universe checking |

---

## References

- [Checking Dependent Types with Normalization by Evaluation](https://davidchristiansen.dk/tutorials/nbe/) - Tutorial on sound implementation
- [lean4lean](https://github.com/digama0/lean4lean) - Reference Lean 4 type checker in Lean
- [Formal Verification of a Proof Assistant](https://www.cs.princeton.edu/~appel/papers/coqincoq.pdf) - Coq in Coq
- [Type Theory and Formal Proof](https://www.cambridge.org/core/books/type-theory-and-formal-proof/0472640AAD34E045C7F140B46A57A67C) - Comprehensive reference

---

## Appendix: lean4idris Red Team Results

The `test/redteam/` directory contains 13 attack test cases:

| # | Attack | Result |
|---|--------|--------|
| 01 | Circular references | REJECT (parser) |
| 02 | Free bound variable | REJECT (parser) |
| 03 | Bad projection index | REJECT (not implemented) |
| 04 | Forward reference | REJECT (parser) |
| 05 | Self-referential def | REJECT (unknown const) |
| 06 | Deep nesting | REJECT (function expected) |
| 07 | Type mismatch def | REJECT (type mismatch) |
| 08 | Universe escape | REJECT (parser) |
| 09 | Fake prop proof | REJECT (type mismatch) |
| 10 | Lambda wrong body | REJECT (type mismatch) ✓ Fixed |
| 11 | Valid identity fn | ACCEPT (correct) |
| 12 | Pi universe wrong | REJECT (type mismatch) |
| 13 | App wrong arg type | REJECT (app mismatch) ✓ Fixed |

All 13 tests pass, demonstrating defense against these attack vectors.
