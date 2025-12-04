---
title: typing under binders, or how to check λx. x
---

# typing under binders, or how to check λx. x

---
> the first walkthrough covered closed terms. but what happens when we
> go under a lambda? the body `x` has a free variable - how do we type it?
>
> in which we add a local context and learn to type open terms.
>
> see also: [src/Walkthrough.lidr](../src/Walkthrough.lidr) for the basics
---

the [previous walkthrough](walkthrough.md) covered the core machinery:
names, levels, well-scoped expressions, substitution, and reduction.
but there was a gap - we could only type *closed* expressions.

consider the identity function:

```
λ(x : Nat). x
```

to type this, we need to:
1. check that `Nat` is a type
2. check that the body `x` has type `Nat`

step 1 is easy - `Nat` is closed. but step 2 is problematic: `x` is a
bound variable. in our representation, the body is `BVar FZ` - a reference
to de bruijn index 0. what's its type?

-------------------------------------------------------------------------------

## the problem: open terms

an *open term* is an expression with free (bound) variables. in `Expr n`,
the `n` tells us how many variables are in scope:

```idris
-- Closed: no free variables
ClosedExpr : Type
ClosedExpr = Expr 0

-- Open: one free variable (index 0)
Expr 1

-- Open: two free variables (indices 0 and 1)
Expr 2
```

when we have `λ(x : Nat). body`, the body has type `Expr 1` - it can
reference variable 0 (which is `x`).

the question is: how do we know what type `BVar FZ` has?

-------------------------------------------------------------------------------

## the solution: local context

the answer is a *local context* - a mapping from variable indices to their
types. when we go under a binder, we record what type that variable has.

```idris
||| Local context entry
record LocalEntry where
  constructor MkLocalEntry
  name : Name           -- for error messages
  type : ClosedExpr     -- the variable's type
  value : Maybe ClosedExpr  -- if this is a let-binding

||| Context for n bound variables
LocalCtx : Nat -> Type
LocalCtx n = Vect n LocalEntry
```

the key insight: we store types as *closed* expressions. when we go
under a binder `λ(x : A). body`, we:
1. close `A` to get a `ClosedExpr`
2. push it onto the context
3. type the body with the extended context

-------------------------------------------------------------------------------

## example: typing λ(x : Nat). x

let's trace through typing the identity function step by step.

```
inferTypeOpen env [] (Lam "x" Default Nat (BVar FZ))
```

**step 1: check the domain is a type**

```
domTy <- inferTypeOpen env [] Nat
-- domTy = Sort 1 (Nat is a Type)

_ <- ensureSort env domTy
-- ok, Sort 1 is indeed a sort
```

**step 2: extend context with x : Nat**

```
let domClosed = Nat  -- already closed
let ctx' = extendCtx "x" Nat []
-- ctx' = [MkLocalEntry "x" Nat Nothing]
```

**step 3: type the body with extended context**

```
bodyTy <- inferTypeOpen env ctx' (BVar FZ)
```

now we hit the `BVar` case:

```idris
inferTypeOpen _ ctx (BVar i) = Right (lookupCtx i ctx).type
```

we look up index 0 in the context and get `Nat`. so `bodyTy = Nat`.

**step 4: construct the result type**

```
Right (Pi "x" Default Nat (weaken1 Nat))
-- = (x : Nat) -> Nat
```

the result is a pi type. we weaken `bodyTy` because the pi's codomain
is under a binder (it could reference variable 0).

-------------------------------------------------------------------------------

## the closing trick

there's a subtlety. when we type an application:

```
inferTypeOpen env ctx (App f arg)
```

we get `fTy : ClosedExpr` which might be `(x : A) -> B`. the codomain `B`
has a free variable (x). when we substitute `arg` for x, we need `arg`
to be closed.

but `arg : Expr n` - it's an open term! we can't directly substitute.

the solution is `closeWithPlaceholders`:

```idris
closeWithPlaceholders : LocalCtx n -> Expr n -> ClosedExpr
closeWithPlaceholders [] e = e
closeWithPlaceholders (entry :: ctx) e =
  let placeholder = Const (Str "_local" entry.name) []
      e' = subst0 e placeholder
  in closeWithPlaceholders ctx e'
```

we substitute each bound variable with a unique placeholder constant.
this gives us a closed expression we can use for substitution.

is this sound? yes, because:
1. we only use closed expressions for *structural* operations (substitution)
2. the placeholder names are unique per variable
3. type equality checks will see matching placeholders as equal

-------------------------------------------------------------------------------

## example: typing λ(x : Nat). λ(y : Nat). x

a more complex example - the const function:

```
λ(x : Nat). λ(y : Nat). x
```

in our representation:
```idris
Lam "x" Default Nat
  (Lam "y" Default (weaken1 Nat)
    (BVar (FS FZ)))  -- x is index 1, not 0!
```

note: `x` is `BVar (FS FZ)` (index 1) because `y` is the innermost binder.

**tracing the type inference:**

```
inferTypeOpen env [] (Lam "x" ...)
  -- extend context: ctx1 = ["x" : Nat]

  inferTypeOpen env ctx1 (Lam "y" ...)
    -- extend context: ctx2 = ["y" : Nat, "x" : Nat]

    inferTypeOpen env ctx2 (BVar (FS FZ))
      -- look up index 1 → "x" : Nat
      -- return Nat

    -- inner lambda type: (y : Nat) -> Nat

  -- outer lambda type: (x : Nat) -> (y : Nat) -> Nat
```

the context grows as we descend, and variable indices count from the
innermost binder outward.

-------------------------------------------------------------------------------

## pi types and universe levels

when we type a pi type `(x : A) -> B`, we need to compute the result universe:

```idris
inferTypeOpen env ctx (Pi name bi domExpr codExpr) = do
  domTy <- inferTypeOpen env ctx domExpr
  domLevel <- ensureSort env domTy

  let ctx' = extendCtx name (closeWithPlaceholders ctx domExpr) ctx
  codTy <- inferTypeOpen env ctx' codExpr
  codLevel <- ensureSort env codTy

  Right (Sort (simplify (IMax domLevel codLevel)))
```

the universe of `(x : A) -> B` is `imax(level(A), level(B))`.

why `imax` and not `max`? because of prop's impredicativity:
- if `B : Prop` (level 0), then `(x : A) -> B : Prop` regardless of `A`
- `imax(l, 0) = 0` for any `l`

we also `simplify` the result:
- `imax(1, 1)` → `1`
- `imax(0, l)` → `l`
- `max(l, l)` → `l`

this is why `(x : Nat) -> Nat : Type 1` instead of `Type (imax 1 1)`.

-------------------------------------------------------------------------------

## let bindings

let bindings are similar to lambdas, but we also track the value:

```idris
inferTypeOpen env ctx (Let name tyExpr valExpr body) = do
  tyTy <- inferTypeOpen env ctx tyExpr
  _ <- ensureSort env tyTy

  let tyClosed = closeWithPlaceholders ctx tyExpr
  let valClosed = closeWithPlaceholders ctx valExpr

  let ctx' = extendCtxLet name tyClosed valClosed ctx
  inferTypeOpen env ctx' body
```

the value is stored in the context entry. this matters for reduction:
when we encounter a `BVar` that's a let-binding, we can unfold it.

-------------------------------------------------------------------------------

## projection reduction

structures in lean are single-constructor inductives. a projection
`s.1` extracts a field from a structure value.

```
Proj "Prod" 0 (Prod.mk a b)  →  a
Proj "Prod" 1 (Prod.mk a b)  →  b
```

in our implementation:

```idris
tryProjReduction env (Proj structName idx struct) whnfStep = do
  -- reduce struct to WHNF
  let struct' = iterWhnfStep whnfStep struct 100

  -- check if it's a constructor application
  let (head, args) = getAppSpine struct'
  (ctorName, _) <- getConstHead head
  (_, _, numParams, numFields) <- getConstructorInfo env ctorName

  -- extract field at index (after params)
  guard (idx < numFields)
  listNth args (numParams + idx)

tryProjReduction _ _ _ = Nothing
```

the key detail: constructor arguments include *parameters* before fields.
for `Prod.mk {α} {β} a b`, there are 2 params and 2 fields:
- `args[0]` = α (param)
- `args[1]` = β (param)
- `args[2]` = a (field 0)
- `args[3]` = b (field 1)

so `Proj "Prod" 0` extracts `args[numParams + 0] = args[2] = a`.

-------------------------------------------------------------------------------

## putting it together

the reduction pipeline now handles five kinds of reduction:

```
whnf env e = whnfFuel 1000 e
  where
    whnfFuel (S k) e =
      -- 1. beta/let reduction
      case whnfStepCore e of
        Just e' => whnfFuel k e'
        Nothing =>
          -- 2. projection reduction
          case tryProjReduction env e whnfStepWithDelta of
            Just e' => whnfFuel k e'
            Nothing =>
              -- 3. iota reduction (recursors)
              case tryIotaReduction env e whnfStepWithDelta of
                Just e' => whnfFuel k e'
                Nothing =>
                  -- 4. delta reduction (constants)
                  case unfoldHead env e of
                    Just e' => whnfFuel k e'
                    Nothing => Right e
```

the order matters:
1. beta/let first (structural, always safe)
2. projection (simple, common in structures)
3. iota (recursors, more expensive to check)
4. delta (unfold definitions, can create more redexes)

-------------------------------------------------------------------------------

## test cases

here are the tests we added:

```idris
-- With context [x : Nat], infer type of 'x'
-- Expected: Nat
let ctx1 = extendCtx "x" nat emptyCtx
inferTypeOpen env ctx1 (BVar FZ)  -- Right Nat

-- λ(x : Nat). x
-- Expected: (x : Nat) -> Nat
inferTypeOpen env emptyCtx idLam  -- Right ((x : Nat) -> Nat)

-- (x : Nat) -> Nat
-- Expected: Sort 1
inferTypeOpen env emptyCtx piTy  -- Right (Sort 1)

-- λ(x : Nat). λ(y : Nat). x
-- Expected: (x : Nat) -> (y : Nat) -> Nat
inferTypeOpen env emptyCtx constLam  -- Right ((x : Nat) -> ((y : Nat) -> Nat))
```

all pass with the correct types.

-------------------------------------------------------------------------------

## what's still missing

the kernel is now ~70-75% complete. remaining features:

| feature | difficulty | notes |
|---------|------------|-------|
| proof irrelevance | easy | all proofs of `Prop` are equal |
| quotient types | medium | `Quot.mk`, `Quot.lift`, `Quot.ind` |
| declaration validation | medium | check new decls are well-formed |
| nat/string literal reduction | easy | `2 + 3 → 5` via `OfNat` |

proof irrelevance is the most impactful - it's needed for many equality
proofs in mathlib. the idea is simple: if `p q : P` where `P : Prop`,
then `p = q` definitionally.

-------------------------------------------------------------------------------

## summary

we added:

1. **local context** - tracks types of bound variables
2. **open term inference** - `inferTypeOpen` works on `Expr n`
3. **projection reduction** - `s.field` reduces when `s` is a constructor
4. **universe normalization** - `imax(1,1) → 1`

the key insight is that we can represent variable types as closed expressions,
using placeholder constants to close open terms when needed for substitution.

```
           ┌─────────────────────────────────────────────────────┐
           │                   LocalCtx n                        │
           │  Vect n LocalEntry                                  │
           │  [x₀ : T₀, x₁ : T₁, ..., xₙ₋₁ : Tₙ₋₁]              │
           └─────────────────────────────────────────────────────┘
                                    │
                                    ▼
           ┌─────────────────────────────────────────────────────┐
           │               inferTypeOpen env ctx e               │
           │                                                     │
           │  BVar i  →  lookupCtx i ctx                        │
           │  Lam     →  extend ctx, recurse on body            │
           │  Pi      →  extend ctx, infer codomain level       │
           │  App     →  close arg, substitute into codomain    │
           └─────────────────────────────────────────────────────┘
                                    │
                                    ▼
           ┌─────────────────────────────────────────────────────┐
           │                   ClosedExpr                        │
           │  The result type is always closed                  │
           └─────────────────────────────────────────────────────┘
```

-------------------------------------------------------------------------------

## references

- [lean4lean TypeChecker.lean](https://github.com/digama0/lean4lean) - reference implementation
- [type checking in lean 4](https://ammkrn.github.io/type_checking_in_lean4/) - documentation
- [de bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index) - variable representation
