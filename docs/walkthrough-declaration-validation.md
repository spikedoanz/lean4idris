---
title: trusting the source, or how to validate declarations
---

# trusting the source, or how to validate declarations

---
> we can type check expressions. we can reduce them. we can compare them.
> but when someone hands us a new declaration, how do we know it's legit?
>
> in which we learn to validate axioms, definitions, and theorems.
>
> see also: [walkthrough-local-context.md](walkthrough-local-context.md) for open terms
---

the kernel's job isn't just to type check expressions - it's to build a
*trusted environment* of declarations. when we add a new axiom or definition,
we need to verify it's well-formed before it becomes part of our trusted base.

this is the final piece of the kernel: declaration validation.

-------------------------------------------------------------------------------

## what can go wrong?

there are several ways a declaration can be invalid:

1. **name collision** - the name is already declared
2. **duplicate universe parameters** - `def foo.{u, u}` has `u` twice
3. **ill-formed type** - the declared type isn't actually a type
4. **type mismatch** - the value's type doesn't match the declared type
5. **non-prop theorem** - theorems must have type in `Prop`

let's handle each of these.

-------------------------------------------------------------------------------

## check 1: name not already declared

the simplest check - is this name fresh?

```idris
checkNameNotDeclared : TCEnv -> Name -> TC ()
checkNameNotDeclared env name =
  case lookupDecl name env of
    Just _ => Left (OtherError $ "already declared: " ++ show name)
    Nothing => Right ()
```

if you try to declare `Nat` twice, you get an error.

-------------------------------------------------------------------------------

## check 2: no duplicate universe parameters

lean allows polymorphic definitions like `def id.{u} (α : Sort u) ...`.
but `def broken.{u, u}` has `u` listed twice - that's invalid.

```idris
checkNoDuplicateUnivParams : List Name -> TC ()
checkNoDuplicateUnivParams [] = Right ()
checkNoDuplicateUnivParams (p :: ps) =
  if elem p ps
    then Left (OtherError $ "duplicate universe parameter: " ++ show p)
    else checkNoDuplicateUnivParams ps
```

simple quadratic check - good enough for the small parameter lists we see.

-------------------------------------------------------------------------------

## check 3: type is well-formed

when someone declares `axiom foo : T`, we need to verify that `T` is actually
a type. that means `T` must have type `Sort l` for some level `l`.

```idris
checkIsType : TCEnv -> ClosedExpr -> TC Level
checkIsType env e = do
  ty <- inferType env e
  ensureSort env ty
```

this returns the universe level, which we'll need for theorems.

-------------------------------------------------------------------------------

## validating axioms

an axiom is the simplest declaration: just a name and a type.

```idris
checkAxiomDecl : TCEnv -> Name -> ClosedExpr -> List Name -> TC ()
checkAxiomDecl env name ty levelParams = do
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env ty
  Right ()
```

that's it. if all checks pass, we can add the axiom to the environment.

```idris
addAxiomChecked : TCEnv -> Name -> ClosedExpr -> List Name -> TC TCEnv
addAxiomChecked env name ty levelParams = do
  checkAxiomDecl env name ty levelParams
  Right (addDecl (AxiomDecl name ty levelParams) env)
```

-------------------------------------------------------------------------------

## validating definitions

definitions are harder - we have both a type *and* a value, and they must
agree.

```idris
checkDefDecl : TCEnv -> Name -> ClosedExpr -> ClosedExpr -> List Name -> TC ()
checkDefDecl env name ty value levelParams = do
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env ty
  valueTy <- inferType env value
  eq <- isDefEq env valueTy ty
  if eq
    then Right ()
    else Left (OtherError $ "definition type mismatch for " ++ show name)
```

the key step is `isDefEq env valueTy ty` - we infer the type of the value,
then check it's definitionally equal to the declared type. this handles
cases where the types are the same up to reduction.

example:
```
def id : Nat → Nat := λx. x
```

- declared type: `Nat → Nat`
- value: `λx. x`
- inferred type of value: `(x : Nat) → Nat` (which is `Nat → Nat`)
- `isDefEq` confirms they match

-------------------------------------------------------------------------------

## validating theorems

theorems have an extra constraint: their type must be a proposition.

```idris
checkThmDecl : TCEnv -> Name -> ClosedExpr -> ClosedExpr -> List Name -> TC ()
checkThmDecl env name ty value levelParams = do
  checkNameNotDeclared env name
  checkNoDuplicateUnivParams levelParams
  tyLevel <- checkIsType env ty
  -- Theorem type must be a Prop (Sort 0)
  if simplify tyLevel /= Zero
    then Left (OtherError $ "theorem type must be a Prop: " ++ show name)
    else do
      valueTy <- inferType env value
      eq <- isDefEq env valueTy ty
      if eq
        then Right ()
        else Left (OtherError $ "theorem proof type mismatch for " ++ show name)
```

`tyLevel` is the universe level of the type. for a theorem, we require
`tyLevel = 0`, meaning the type lives in `Prop`.

why does this matter? because of proof irrelevance. if `P : Prop`, then
any two proofs of `P` are definitionally equal. but if `P : Type`, that's
not true. theorems get special treatment in the kernel.

-------------------------------------------------------------------------------

## the unified entry point

```idris
addDeclChecked : TCEnv -> Declaration -> TC TCEnv
addDeclChecked env (AxiomDecl name ty levelParams) =
  addAxiomChecked env name ty levelParams
addDeclChecked env (DefDecl name ty value hint safety levelParams) =
  addDefChecked env name ty value hint safety levelParams
addDeclChecked env (ThmDecl name ty value levelParams) =
  addThmChecked env name ty value levelParams
addDeclChecked env (OpaqueDecl name ty value levelParams) = do
  checkDefDecl env name ty value levelParams
  Right (addDecl (OpaqueDecl name ty value levelParams) env)
addDeclChecked env QuotDecl =
  Right (enableQuot env)
addDeclChecked env decl@(IndDecl info levelParams) = do
  checkNameNotDeclared env info.name
  checkNoDuplicateUnivParams levelParams
  _ <- checkIsType env info.type
  Right (addDecl decl env)
-- ... similar for CtorDecl, RecDecl
```

this dispatches to the appropriate validator based on declaration type.

-------------------------------------------------------------------------------

## what we don't check (yet)

full inductive validation is complex. lean4lean has ~800 lines just for
`Inductive/Add.lean`. our basic checks verify:

- name is fresh
- no duplicate universe params
- the type is well-formed

but we don't verify:
- constructor types are valid for the inductive
- positivity (no `data Bad = MkBad (Bad -> Bad)`)
- universe constraints between parameters and indices
- recursor formation rules

these would be needed for a production kernel, but the core machinery
(type inference, reduction, definitional equality) is complete.

-------------------------------------------------------------------------------

## example: building a trusted environment

```idris
-- Start with empty environment
env0 : TCEnv
env0 = emptyEnv

-- Add Nat : Type
env1 <- addAxiomChecked env0 "Nat" (Sort 1) []

-- Add zero : Nat
env2 <- addAxiomChecked env1 "zero" Nat []

-- Add id : Nat → Nat := λx. x
env3 <- addDefChecked env2 "id" (Nat → Nat) (λx. x) Abbrev Safe []

-- Try to add Nat again - fails!
-- addAxiomChecked env3 "Nat" (Sort 1) []
-- Error: "already declared: Nat"

-- Try to add broken def - fails!
-- addDefChecked env3 "broken" (Nat → Nat) (Sort 0) Abbrev Safe []
-- Error: "definition type mismatch for broken"
```

each step validates the declaration before adding it. the environment
only grows with well-formed declarations.

-------------------------------------------------------------------------------

## the trust story

the kernel maintains a simple invariant:

> every declaration in the environment has been validated

this means:
1. all types are well-formed
2. all definitions type-check
3. all theorems prove propositions

when you use `addDeclChecked`, you get this guarantee. when you use
plain `addDecl`, you bypass validation (useful for testing, dangerous
for production).

-------------------------------------------------------------------------------

## summary

declaration validation is the gatekeeper of the kernel. we check:

| declaration | checks |
|-------------|--------|
| axiom | name fresh, params unique, type well-formed |
| definition | + value type matches declared type |
| theorem | + type must be Prop |
| opaque | same as definition |
| inductive | basic name/type checks (full validation is complex) |

```
           ┌─────────────────────────────────────────────────────┐
           │              Declaration Validation                  │
           └─────────────────────────────────────────────────────┘
                                    │
                    ┌───────────────┼───────────────┐
                    ▼               ▼               ▼
           ┌─────────────┐  ┌─────────────┐  ┌─────────────┐
           │   Axiom     │  │ Definition  │  │   Theorem   │
           │             │  │             │  │             │
           │ • name      │  │ • name      │  │ • name      │
           │ • params    │  │ • params    │  │ • params    │
           │ • type      │  │ • type      │  │ • type:Prop │
           │             │  │ • value≡ty  │  │ • value≡ty  │
           └─────────────┘  └─────────────┘  └─────────────┘
                                    │
                                    ▼
           ┌─────────────────────────────────────────────────────┐
           │              Trusted Environment                     │
           │  (only well-formed declarations)                    │
           └─────────────────────────────────────────────────────┘
```

-------------------------------------------------------------------------------

## the complete kernel

with declaration validation, lean4idris now has all the core components:

1. **parsing** - read lean4export format
2. **expressions** - well-scoped terms with de bruijn indices
3. **type inference** - `inferType` for closed and open terms
4. **reduction** - beta, let, delta, iota, projection, quotient
5. **definitional equality** - structural + reduction + eta + proof irrelevance
6. **declaration validation** - verify before trust

this is a functional type checker for lean 4's kernel language.

-------------------------------------------------------------------------------

## references

- [lean4lean Environment.lean](https://github.com/digama0/lean4lean) - reference implementation
- [type checking in lean 4](https://ammkrn.github.io/type_checking_in_lean4/) - documentation
- [lean kernel](https://github.com/leanprover/lean4) - the real thing
