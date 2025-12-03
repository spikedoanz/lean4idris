---
title: a lean 4 kernel in idris, from the ground up
---

# a lean 4 kernel in idris, from the ground up

---
> in which we trace through the machinery of a lean 4 type checker,
> from parsing export files to reduction and definitional equality.
>
> see also: [src/Walkthrough.lidr](../src/Walkthrough.lidr) for an interactive version
> that you can load with `pack repl src/Walkthrough.lidr`
---

this document walks through [lean4idris](https://github.com/...), a lean 4
type checker written in idris 2. we'll follow the data as it flows from
a raw export file through parsing, into the type checker's core operations:
type inference, weak head normal form reduction, and definitional equality.

the [lean4export](https://github.com/leanprover/lean4export) format is a
line-based serialization of lean's kernel-level terms. every definition,
theorem, and inductive type in a lean project can be exported and verified
by an independent checker - which is exactly what we're building.

-------------------------------------------------------------------------------

## the export format

lean4export produces files that look like this:

```
0.0.0
1 #NS 0 Nat
2 #NS 1 zero
3 #NS 1 succ
1 #US 0
1 #ES 1
2 #EC 1
3 #EP #BD 0 2 1
...
```

each line has an index, a command (prefixed with `#`), and arguments.
the format is designed for streaming: every reference is to a previously
defined index, so we can parse in a single pass.

the commands break down into categories:

| category    | commands                          | purpose                        |
|-------------|-----------------------------------|--------------------------------|
| names       | `#NS`, `#NI`                      | hierarchical identifiers       |
| universes   | `#US`, `#UM`, `#UIM`, `#UP`       | universe levels                |
| expressions | `#EV`, `#ES`, `#EC`, `#EA`, ...   | the core term language         |
| binders     | `#BD`, `#BI`, `#BS`, `#BC`        | implicit/explicit annotations  |
| declarations| `#AX`, `#DEF`, `#THM`, `#IND`, ...|  top-level definitions         |

-------------------------------------------------------------------------------

## layer 1: names

everything in lean has a name. names are hierarchical - `Nat.succ` is
the name `succ` under the namespace `Nat`, which itself is under the
anonymous root.

```idris
-- from src/Lean4Idris/Name.idr

||| Hierarchical names in Lean
public export
data Name : Type where
  ||| The root/anonymous name
  Anonymous : Name
  ||| A string segment: parent.segment
  Str : String -> Name -> Name
  ||| A numeric segment: parent.42
  Num : Nat -> Name -> Name
```

the export format builds names incrementally:

```
0           -- index 0 is always anonymous (implicit)
1 #NS 0 Nat -- index 1 = anonymous.Nat = "Nat"
2 #NS 1 zero -- index 2 = Nat.zero
```

`#NS` appends a string segment, `#NI` appends a numeric segment.
names are interned by index for efficient comparison.

-------------------------------------------------------------------------------

## layer 2: universe levels

lean is a predicative type theory with a hierarchy of universes:
`Prop`, `Type`, `Type 1`, `Type 2`, etc. universe levels track
where each type lives in this hierarchy.

```idris
-- from src/Lean4Idris/Level.idr

||| Universe levels
public export
data Level : Type where
  ||| Level 0 (Prop or Type 0)
  Zero : Level
  ||| Successor level (l + 1)
  Succ : Level -> Level
  ||| Maximum of two levels
  Max : Level -> Level -> Level
  ||| "Impredicative" max: 0 if second is 0, else max
  IMax : Level -> Level -> Level
  ||| Universe parameter (for polymorphism)
  Param : Name -> Level
```

the `IMax` constructor is crucial for lean's impredicativity: `Prop`
(level 0) is impredicative, meaning `(A : Prop) -> B` lives in `Prop`
when `B` does, regardless of `A`.

```
IMax l1 l2 = 0      if l2 = 0
           = Max l1 l2  otherwise
```

export format:
```
1 #US 0     -- succ(0) = 1
2 #UM 0 1   -- max(0, 1) = 1
3 #UP 1     -- level parameter with name at index 1
```

-------------------------------------------------------------------------------

## layer 3: expressions (the heart of the kernel)

here's where things get interesting. lean's core calculus has just a
handful of expression forms, but they're enough to encode all of
mathematics.

```idris
-- from src/Lean4Idris/Expr.idr

||| Well-scoped expressions indexed by binding depth
public export
data Expr : (depth : Nat) -> Type where
  ||| Bound variable (de Bruijn index)
  BVar : Fin n -> Expr n
  ||| Sort (Type at some universe level)
  Sort : Level -> Expr n
  ||| Constant reference with universe instantiation
  Const : Name -> List Level -> Expr n
  ||| Function application
  App : Expr n -> Expr n -> Expr n
  ||| Lambda abstraction
  Lam : Name -> BinderInfo -> Expr n -> Expr (S n) -> Expr n
  ||| Pi type (dependent function type)
  Pi : Name -> BinderInfo -> Expr n -> Expr (S n) -> Expr n
  ||| Let binding
  Let : Name -> Expr n -> Expr n -> Expr (S n) -> Expr n
  ||| Structure projection
  Proj : Name -> Nat -> Expr n -> Expr n
  ||| Natural number literal
  NatLit : Nat -> Expr n
  ||| String literal
  StringLit : String -> Expr n
```

### well-scoped by construction

the key insight is that `Expr n` is indexed by `n`, the number of
bound variables in scope. a `BVar` (bound variable) is a `Fin n` -
a natural number strictly less than `n`. this makes ill-scoped
terms *unrepresentable*.

```idris
-- Fin n is the type of natural numbers less than n
-- Fin 0 is empty (no values)
-- Fin 3 has values FZ, FS FZ, FS (FS FZ) representing 0, 1, 2

-- A closed expression has no free variables
ClosedExpr : Type
ClosedExpr = Expr 0
```

when we go under a binder (lambda, pi, or let), the depth increases:

```idris
-- λ(x : Nat). x
-- The body has access to one bound variable (index 0)
example : ClosedExpr
example = Lam "x" Default natType (BVar FZ)
  where
    natType : Expr 0
    natType = Const (Str "Nat" Anonymous) []
```

### de bruijn indices

we use [de bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index)
rather than named variables. `BVar FZ` always refers to the innermost
binder, `BVar (FS FZ)` to the next one out, etc.

```
λx. λy. x   becomes   λ. λ. BVar 1
λx. λy. y   becomes   λ. λ. BVar 0
```

this eliminates alpha-equivalence issues entirely - two terms are
syntactically equal iff they're alpha-equivalent.

-------------------------------------------------------------------------------

## layer 4: parsing the export format

the parser transforms the text format into our typed AST. the key
challenge is handling forward references and building well-scoped
expressions.

```idris
-- from src/Lean4Idris/Export/Parser.idr

||| Parser state accumulates parsed entities by index
record ParseState where
  constructor MkParseState
  names : List (Nat, Name)
  levels : List (Nat, Level)
  exprs : List (Nat, ClosedExpr)
  recRules : List (Nat, RecursorRule)
  decls : List Declaration
```

### the scoped expression trick

expressions in the export format use raw indices for bound variables:

```
5 #EL #BD 0 3 4   -- lambda with body referring to var 0
```

but we need to build `Expr n` where `n` is statically known. the trick
is to use a "scoped expression" - a function that, given any depth,
produces an expression at that depth (if valid):

```idris
||| A scoped expression can be instantiated at any depth
ScopedExpr : Type
ScopedExpr = (n : Nat) -> Maybe (Expr n)

||| Lift a closed expression to any scope
liftClosed : ClosedExpr -> ScopedExpr
liftClosed e = \n => Just (weakenToN n e)

||| Create a bound variable reference (succeeds if in scope)
scopedBVar : Nat -> ScopedExpr
scopedBVar k = \n =>
  case natToFin k n of
    Just i  => Just (BVar i)
    Nothing => Nothing  -- out of scope!
```

when parsing a lambda body, we track that we're one binder deeper:

```idris
parseLam : ... -> Parser ScopedExpr
parseLam bi nameIdx domExpr bodyExpr = do
  name <- lookupName nameIdx
  pure $ \n =>
    -- domain is at current depth
    dom <- domExpr n
    -- body is one deeper, so pass (S n)
    body <- bodyExpr (S n)
    Just (Lam name bi dom body)
```

-------------------------------------------------------------------------------

## layer 5: declarations

declarations are the top-level entities: axioms, definitions, theorems,
inductive types, etc.

```idris
-- from src/Lean4Idris/Decl.idr

data Declaration : Type where
  ||| Axiom: postulated constant
  AxiomDecl : Name -> ClosedExpr -> List Name -> Declaration

  ||| Definition with reducibility hint
  DefDecl : Name -> ClosedExpr -> ClosedExpr ->
            ReducibilityHint -> Safety -> List Name -> Declaration

  ||| Theorem (proof-irrelevant)
  ThmDecl : Name -> ClosedExpr -> ClosedExpr -> List Name -> Declaration

  ||| Inductive type
  IndDecl : InductiveInfo -> List Name -> Declaration

  ||| Constructor
  CtorDecl : Name -> ClosedExpr -> Name ->
             Nat -> Nat -> Nat -> List Name -> Declaration

  ||| Recursor
  RecDecl : RecursorInfo -> List Name -> Declaration
```

### reducibility hints

definitions come with hints about when to unfold them:

```idris
data ReducibilityHint : Type where
  Abbrev : ReducibilityHint   -- always unfold (like `abbrev` in lean)
  Opaq : ReducibilityHint     -- never unfold (like `opaque`)
  Regular : Nat -> ReducibilityHint  -- unfold based on heuristics
```

this matters for performance and for controlling definitional equality.
`abbrev` definitions are transparent; `opaque` ones are not.

-------------------------------------------------------------------------------

## layer 6: the type checker environment

the environment holds all known declarations, indexed by name:

```idris
-- from src/Lean4Idris/TypeChecker.idr

record TCEnv where
  constructor MkTCEnv
  decls : SortedMap Name Declaration

lookupDecl : Name -> TCEnv -> Maybe Declaration
lookupDecl n env = lookup n env.decls
```

to check an expression, we look up constants in the environment and
verify they're used consistently with their declared types and
universe parameters.

-------------------------------------------------------------------------------

## layer 7: substitution

before we can reduce terms, we need substitution. this is where the
well-scoped representation pays off - substitution is a *total* function
with strong type guarantees.

```idris
-- from src/Lean4Idris/Subst.idr

||| Substitute a closed expression for variable 0
subst0 : Expr (S n) -> Expr n -> Expr n

||| Weaken an expression (shift all indices up by 1)
weaken1 : Expr n -> Expr (S n)
```

the implementation handles each case:

```idris
-- Substituting into a bound variable
subst0 (BVar FZ) replacement = replacement
subst0 (BVar (FS k)) _ = BVar k  -- shift down

-- Going under a binder: weaken the replacement
subst0 (Lam name bi dom body) replacement =
  Lam name bi
      (subst0 dom replacement)
      (subst0 body (weaken1 replacement))
```

-------------------------------------------------------------------------------

## layer 8: weak head normal form (whnf)

the workhorse of type checking is reduction to *weak head normal form*.
this is "lazy" evaluation - we only reduce enough to see the head
constructor.

```idris
-- from src/Lean4Idris/TypeChecker.idr

whnf : TCEnv -> ClosedExpr -> TC ClosedExpr
```

whnf performs four kinds of reduction:

### beta reduction

```
(λx. body) arg  →  body[x := arg]
```

```idris
whnfStepCore (App (Lam _ _ _ body) arg) = Just (subst0 body arg)
```

### let reduction

```
let x = val in body  →  body[x := val]
```

```idris
whnfStepCore (Let _ _ val body) = Just (subst0 body val)
```

### delta reduction (constant unfolding)

```
myId  →  λx. x    (if myId is defined as λx. x)
```

```idris
unfoldConst : TCEnv -> Name -> List Level -> Maybe ClosedExpr
unfoldConst env name levels = do
  decl <- lookupDecl name env
  value <- getDeclValue decl  -- Nothing for axioms, opaques
  pure (instantiateLevelParams (declLevelParams decl) levels value)
```

### iota reduction (recursor computation)

this is the "computation rule" for inductive types. when a recursor
is applied to a constructor, we can compute:

```
Nat.rec motive zero_case succ_case Nat.zero
  →  zero_case

Nat.rec motive zero_case succ_case (Nat.succ n)
  →  succ_case n (Nat.rec motive zero_case succ_case n)
```

```idris
tryIotaReduction : TCEnv -> ClosedExpr -> ... -> Maybe ClosedExpr
tryIotaReduction env e whnfStep = do
  -- decompose into head and args
  let (head, args) = getAppSpine e
  (recName, recLevels) <- getConstHead head
  recInfo <- getRecursorInfo env recName

  -- get the major premise (the value being recursed on)
  let majorIdx = recInfo.numParams + recInfo.numMotives +
                 recInfo.numMinors + recInfo.numIndices
  major <- listNth args majorIdx

  -- reduce major to see if it's a constructor
  let major' = iterWhnfStep whnfStep major 100
  let (majorHead, majorArgs) = getAppSpine major'
  (ctorName, _) <- getConstHead majorHead

  -- find the matching recursor rule
  rule <- findRecRule recInfo.rules ctorName

  -- apply the rule's RHS to the appropriate arguments
  ...
```

### the reduction loop

whnf iterates these steps until no more reductions apply:

```idris
whnf env e = whnfFuel 1000 e
  where
    whnfFuel : Nat -> ClosedExpr -> TC ClosedExpr
    whnfFuel 0 e = Right e  -- fuel exhausted
    whnfFuel (S k) e =
      case whnfStepCore e of
        Just e' => whnfFuel k e'
        Nothing =>
          case tryIotaReduction env e whnfStepWithDelta of
            Just e' => whnfFuel k e'
            Nothing =>
              case unfoldHead env e of
                Just e' => whnfFuel k e'
                Nothing => Right e  -- normal form reached
```

-------------------------------------------------------------------------------

## layer 9: type inference

type inference computes the type of an expression:

```idris
inferType : TCEnv -> ClosedExpr -> TC ClosedExpr
```

the rules follow lean's type theory:

```idris
-- Sort : Sort (succ level)
-- Type n : Type (n+1)
inferType _ (Sort l) = Right (Sort (Succ l))

-- Constants: look up type and instantiate universes
inferType env (Const name levels) = do
  decl <- lookupDecl name env
  ty <- declType decl
  let params = declLevelParams decl
  guard (length params == length levels)
  Right (instantiateLevelParams params levels ty)

-- Application: if f : (x : A) -> B and arg : A, then (f arg) : B[x := arg]
inferType env (App f arg) = do
  fTy <- inferType env f
  (_, _, dom, cod) <- ensurePi env fTy
  Right (subst0 cod arg)

-- Lambda: type is Pi
inferType env (Lam name bi ty body) = do
  _ <- ensureSort env =<< inferType env ty
  Right (Pi name bi ty body)  -- simplified; real impl checks body

-- Pi: compute universe level
inferType env (Pi name bi dom cod) = do
  domLevel <- ensureSort env =<< inferType env dom
  -- codomain check requires local context (simplified here)
  Right (Sort (Max domLevel Zero))
```

-------------------------------------------------------------------------------

## layer 10: definitional equality

two types are *definitionally equal* if they reduce to the same normal
form. this is the core judgment that makes type checking work.

```idris
isDefEq : TCEnv -> ClosedExpr -> ClosedExpr -> TC Bool
isDefEq env e1 e2 = do
  e1' <- whnf env e1
  e2' <- whnf env e2
  isDefEqWhnf e1' e2'
```

after reducing to whnf, we compare structurally:

```idris
isDefEqWhnf : ClosedExpr -> ClosedExpr -> TC Bool

-- Sorts: compare levels
isDefEqWhnf (Sort l1) (Sort l2) = Right (levelEq l1 l2)

-- Constants: same name and universe levels
isDefEqWhnf (Const n1 ls1) (Const n2 ls2) =
  Right (n1 == n2 && levelListEq ls1 ls2)

-- Applications: check both parts
isDefEqWhnf (App f1 a1) (App f2 a2) = do
  eqF <- isDefEq env f1 f2
  if eqF then isDefEq env a1 a2 else Right False

-- Lambdas: check type and body
isDefEqWhnf (Lam _ _ ty1 body1) (Lam _ _ ty2 body2) = do
  eqTy <- isDefEq env ty1 ty2
  if eqTy then isDefEqBody body1 body2 else Right False
```

### eta expansion

a key feature is eta-equivalence for functions:

```
λx. f x  =  f    (when x is not free in f)
```

this is essential for lean's type theory. we implement it by
expanding the non-lambda side:

```idris
tryEtaExpansion : TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
tryEtaExpansion env t s =
  case t of
    Lam name bi ty body =>
      case s of
        Lam _ _ _ _ => Right Nothing  -- both lambdas, no eta needed
        _ => do
          -- try to eta-expand s
          sTy <- inferType env s
          case !(whnf env sTy) of
            Pi piName piBi dom cod =>
              -- expand s to: λ(piName : dom). s x
              let sExpanded = Lam piName piBi dom (App (weaken1 s) (BVar FZ))
              result <- isDefEq env t sExpanded
              Right (Just result)
            _ => Right Nothing
    _ => Right Nothing
```

-------------------------------------------------------------------------------

## putting it all together: the data flow

```
┌─────────────────────────────────────────────────────────────────────┐
│                        lean4export file                             │
│  "1 #NS 0 Nat\n2 #NS 1 zero\n3 #EP #BD 0 2 1\n..."                  │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│                           Lexer                                     │
│  Token.idr: TCommand, TNat, TIdent, THex, TNewline                  │
│  "1 #NS 0 Nat" → [TNat 1, TCommand NS, TNat 0, TIdent "Nat", ...]   │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│                           Parser                                    │
│  Parser.idr: ParseState with names, levels, exprs, decls            │
│  Builds well-scoped Expr n using ScopedExpr trick                   │
│  Outputs: List Declaration, indexed Name/Level/Expr lookups         │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│                         Environment                                 │
│  TCEnv: SortedMap Name Declaration                                  │
│  Populated with all parsed declarations                             │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│                        Type Checker                                 │
│                                                                     │
│   inferType ◄────────────────────────────────┐                      │
│       │                                      │                      │
│       ▼                                      │                      │
│     whnf ─────► beta/let/delta/iota ─────────┘                      │
│       │              reduction                                      │
│       ▼                                                             │
│   isDefEq ◄──── structural comparison + eta                         │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

-------------------------------------------------------------------------------

## example: checking `Nat.zero : Nat`

let's trace through checking that `Nat.zero` has type `Nat`:

1. **lookup** `Nat.zero` in environment
   - find `CtorDecl "Nat.zero" ty "Nat" 0 0 0 []`
   - `ty` = `Const (Str "Nat" Anonymous) []`

2. **inferType** `(Const "Nat.zero" [])`
   - lookup declaration → `CtorDecl` with type `Nat`
   - no universe params to instantiate
   - return `Const "Nat" []`

3. **isDefEq** `(Const "Nat" [])` `(Const "Nat" [])`
   - whnf of `Const "Nat" []` is itself (no reduction)
   - structural comparison: same name, same levels
   - return `True`

-------------------------------------------------------------------------------

## example: reducing `Nat.rec`

consider reducing `Nat.rec (λ_. Type) Unit (λn ih. ih) zero`:

1. **getAppSpine**: head = `Nat.rec`, args = `[motive, hz, hs, zero]`

2. **getRecursorInfo**: lookup `Nat.rec`
   - numParams = 0, numMotives = 1, numMinors = 2, numIndices = 0
   - majorIdx = 0 + 1 + 2 + 0 = 3

3. **get major premise**: `args[3]` = `zero`

4. **whnf major**: `zero` → `Const "Nat.zero" []` (already whnf)

5. **decompose major**: head = `Nat.zero`, no args

6. **find rule**: rule for `Nat.zero` has `nfields = 0`, `rhs = BVar 1`
   (the zero case handler)

7. **build result**:
   - instantiate rhs with params/motives/minors: `hz`
   - apply constructor fields: (none)
   - result: `hz` = `Unit`

-------------------------------------------------------------------------------

## what's next?

the current implementation handles ~60-65% of a complete lean kernel:

**working:**
- names, levels, expressions
- parsing all export format commands
- beta, let, delta, iota reduction
- definitional equality with eta

**missing:**
- local context (for open terms)
- universe level normalization
- proof irrelevance
- quotient type reduction
- projection reduction
- declaration validation

the biggest gap is the local context - currently we only handle closed
terms. adding `FVar` support and a `LocalContext` would enable checking
arbitrary terms, not just top-level definitions.

-------------------------------------------------------------------------------

## references

- [lean4lean](https://github.com/digama0/lean4lean) - lean kernel in lean
- [nanoda_lib](https://github.com/ammkrn/nanoda_lib) - lean kernel in rust
- [type checking in lean 4](https://ammkrn.github.io/type_checking_in_lean4/) - documentation
- [lean4export](https://github.com/leanprover/lean4export) - the export format

```
@misc{lean4idris2025,
  title = {lean4idris: a lean 4 kernel in idris 2},
  url = {https://github.com/.../lean4idris},
  year = {2025}
}
```
