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
>
> a guest post by claude opus
---

this document walks through [lean4idris](https://github.com/spikedoanz/lean4idris), a lean 4
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
| declarations| `#AX`, `#DEF`, `#THM`, `#IND`, `#OPAQ`, ... | top-level definitions |

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

### level simplification

universe levels need normalization for definitional equality checks.
a key optimization is **succ factoring**: pulling common successor
prefixes out of max expressions.

```idris
-- max (a+n) (b+n) = (max a b) + n
-- Example: max u+1 v+1 = (max u v) + 1
simplify (Max l1 l2) =
  let l1' = simplify l1
      l2' = simplify l2
      offset = min (succCount l1') (succCount l2')
  in addSucc offset (Max (stripSucc offset l1') (stripSucc offset l2'))
```

this handles common patterns like `ReaderT` where the inferred type
`Sort (max u+1 v+1)` must match the declared type `Sort ((max u v)+1)`.

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

  ||| Opaque definition (never unfolds)
  OpaqueDecl : Name -> ClosedExpr -> ClosedExpr -> List Name -> Declaration

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
`abbrev` definitions are transparent; `opaque` ones are not. the parser
now handles `#OPAQ` declarations which define constants that should
never be unfolded during type checking.

-------------------------------------------------------------------------------

## layer 6: the type checker environment

the environment holds all known declarations, indexed by name:

```idris
-- from src/Lean4Idris/TypeChecker/Monad.idr

record TCEnv where
  constructor MkTCEnv
  decls : SortedMap Name Declaration
  quotInit : Bool                        -- Quot primitives enabled?
  placeholders : SortedMap Name ClosedExpr
  nextPlaceholder : Nat

lookupDecl : Name -> TCEnv -> Maybe Declaration
lookupDecl n env = lookup n env.decls
```

to check an expression, we look up constants in the environment and
verify they're used consistently with their declared types and
universe parameters.

### local context

to type check expressions under binders (like lambda bodies), we
maintain a local context:

```idris
-- from src/Lean4Idris/TypeChecker/Monad.idr

record LocalEntry where
  constructor MkLocalEntry
  name : Name
  type : ClosedExpr
  value : Maybe ClosedExpr       -- for let-bound variables
  placeholder : Maybe ClosedExpr  -- for theorem checking

LocalCtx : Nat -> Type
LocalCtx n = Vect n LocalEntry
```

the context is a vector indexed by `n`, matching the expression depth.
this ensures we always have type information for every bound variable.

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
-- from src/Lean4Idris/TypeChecker/Reduction.idr

whnf : TCEnv -> ClosedExpr -> TC ClosedExpr
```

whnf performs several kinds of reduction:

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

delta reduction respects reducibility hints:
- `Abbrev`: always unfolds
- `Opaq`/`OpaqueDecl`: never unfolds
- `Regular n`: unfolds based on heuristics

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

### projection reduction

structure field access computes when the structure is a constructor:

```
{ x := 1, y := 2 }.x  →  1
```

### quotient reduction

lean's quotient types have special computation rules:

```
Quot.lift f h (Quot.mk r a)  →  f a
Quot.ind p h (Quot.mk r a)   →  p a
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
-- from src/Lean4Idris/TypeChecker/Infer.idr

inferType : TCEnv -> ClosedExpr -> TC ClosedExpr
inferTypeOpen : TCEnv -> LocalCtx n -> Expr n -> TC ClosedExpr
```

there are two variants: `inferType` for closed terms (no free variables)
and `inferTypeOpen` for terms with bound variables in a local context.

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

-- Lambda: infer body type in extended context
inferTypeOpen env ctx (Lam name bi dom body) = do
  _ <- ensureSortOpen env ctx dom
  let ctx' = extendCtx name (closeExpr ctx dom) ctx
  codTy <- inferTypeOpen env ctx' body
  Right (closePi name bi (closeExpr ctx dom) codTy)

-- Pi: compute universe level
inferType env (Pi name bi dom cod) = do
  domLevel <- ensureSort env =<< inferType env dom
  -- codomain checked in extended context
  codLevel <- ...
  Right (Sort (IMax domLevel codLevel))
```

-------------------------------------------------------------------------------

## layer 10: definitional equality

two types are *definitionally equal* if they reduce to the same normal
form. this is the core judgment that makes type checking work.

```idris
-- from src/Lean4Idris/TypeChecker/DefEq.idr

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

### proof irrelevance

all proofs of propositions (`Prop`) are definitionally equal:

```idris
-- If both e1 and e2 have type T where T : Prop, then e1 = e2
checkProofIrrelevance : TCEnv -> ClosedExpr -> ClosedExpr -> TC (Maybe Bool)
checkProofIrrelevance env e1 e2 = do
  ty <- inferType env e1
  tyTy <- inferType env ty
  case tyTy of
    Sort Zero => Right (Just True)  -- both are proofs, equal!
    _ => Right Nothing
```

-------------------------------------------------------------------------------

## layer 11: declaration validation

when loading export files, we validate each declaration:

```idris
-- from src/Lean4Idris/TypeChecker/Validate.idr

validateDecl : TCEnv -> Declaration -> TC ()
```

### axiom validation

axioms must have a well-formed type:

```idris
validateDecl env (AxiomDecl name ty _) = do
  _ <- ensureSort env =<< inferType env ty
  pure ()
```

### definition validation

definitions must have matching types:

```idris
validateDecl env (DefDecl name ty val _ _ _) = do
  _ <- ensureSort env =<< inferType env ty
  valTy <- inferType env val
  unless !(isDefEq env ty valTy) $
    throw (OtherError "definition type mismatch")
```

### theorem validation

theorems are similar but use proof placeholders:

```idris
validateDecl env (ThmDecl name ty proof _) = do
  _ <- ensureSort env =<< inferType env ty
  proofTy <- inferType env proof
  unless !(isDefEq env ty proofTy) $
    throw (OtherError "theorem proof type mismatch")
```

### constructor validation

constructors must:
- return their inductive type
- have the correct field count
- satisfy positivity (no negative occurrences of the inductive type)

-------------------------------------------------------------------------------

## layer 12: caching

for large export files, type checking can be slow. lean4idris includes
a global cache to avoid re-checking declarations:

```idris
-- from src/Lean4Idris/Cache.idr

record CacheState where
  constructor MkCacheState
  version : String
  passedDecls : SortedSet String
```

the cache:
- stores which declarations have passed type checking
- persists to disk (`~/.cache/lean4idris/<version>.cache`)
- invalidates when the type checker binary changes
- uses an FNV-1a hash of the binary for version tracking

```bash
# Run without cache
pack run lean4idris --no-cache input.export

# With caching (default)
pack run lean4idris input.export
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
│  Handles #AX, #DEF, #THM, #IND, #CTOR, #REC, #OPAQ, ...             │
│  Outputs: List Declaration, indexed Name/Level/Expr lookups         │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│                         Environment                                 │
│  TCEnv: SortedMap Name Declaration                                  │
│  Populated with all parsed declarations                             │
│  Tracks: quotInit, placeholders, nextPlaceholder                    │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│                         Cache Check                                 │
│  Cache.idr: Load/save passed declarations                           │
│  Skip declarations already verified in previous runs                │
└─────────────────────────────────────────────────────────────────────┘
                                  │
                                  ▼
┌─────────────────────────────────────────────────────────────────────┐
│                        Type Checker                                 │
│                                                                     │
│   ┌──────────────────────────────────────────────────────────┐      │
│   │  Monad.idr: TCEnv, LocalCtx, TC monad, errors            │      │
│   └──────────────────────────────────────────────────────────┘      │
│                           │                                         │
│   ┌───────────────────────┼───────────────────────────┐             │
│   │                       ▼                           │             │
│   │  Infer.idr ◄──────────────────────────┐           │             │
│   │  inferType, inferTypeOpen             │           │             │
│   │       │                               │           │             │
│   │       ▼                               │           │             │
│   │  Reduction.idr                        │           │             │
│   │  whnf: beta/let/delta/iota/proj/quot  │           │             │
│   │       │                               │           │             │
│   │       ▼                               │           │             │
│   │  DefEq.idr ◄──── structural + eta + proof irrel   │             │
│   │  isDefEq                                          │             │
│   └───────────────────────────────────────────────────┘             │
│                           │                                         │
│                           ▼                                         │
│   ┌──────────────────────────────────────────────────────────┐      │
│   │  Validate.idr: validateDecl for axioms, defs, thms, ...  │      │
│   └──────────────────────────────────────────────────────────┘      │
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

## project structure

```
src/Lean4Idris/
  Name.idr              -- Hierarchical names
  Level.idr             -- Universe levels with simplification
  Expr.idr              -- Well-scoped expressions (Expr n)
  Decl.idr              -- Declarations (axiom, def, thm, opaque, ind, ctor, rec)
  Subst.idr             -- Substitution operations
  Pretty.idr            -- Pretty printing
  Cache.idr             -- Global file-based caching
  Main.idr              -- CLI with --no-cache, --fuel, --verbose flags

  TypeChecker/          -- Refactored type checker (was monolithic)
    Monad.idr           -- TC monad, environment, local context, errors
    Reduction.idr       -- WHNF reduction (beta, let, delta, iota, proj, quot)
    Infer.idr           -- Type inference (closed and open terms)
    DefEq.idr           -- Definitional equality
    Validate.idr        -- Declaration validation
    TypeChecker.idr     -- Re-exports all submodules

  Export/
    Token.idr           -- Export format tokens
    Lexer.idr           -- Tokenizer
    Parser.idr          -- Parser (handles all declaration types including OPAQ)

  Proofs/               -- Formal metatheory (see below)
```

-------------------------------------------------------------------------------

## mechanized metatheory

lean4idris includes mechanized proofs of key metatheoretic properties
in idris 2. these live in `src/Lean4Idris/Proofs/`:

| module              | status   | what it proves                                    |
|---------------------|----------|---------------------------------------------------|
| Syntax.idr          | complete | intrinsically-scoped expressions                  |
| Substitution.idr    | complete | renaming, substitution, composition lemmas        |
| Typing.idr          | complete | typing judgment definition                        |
| Weakening.idr       | complete | `Γ ⊢ e : T → Γ,x:A ⊢ weaken(e) : weaken(T)`       |
| SubstitutionLemma.idr| complete | substitution preserves typing                    |
| Reduction.idr       | partial  | beta/zeta reduction                               |
| DefEq.idr           | complete | definitional equality is an equivalence           |
| SubjectReduction.idr| partial  | type preservation (5 holes)                       |
| CtxConversion.idr   | partial  | context conversion lemmas                         |

the proofs use intrinsically-scoped syntax where `Expr n` is indexed by
scope depth, making variable scoping correct by construction.

-------------------------------------------------------------------------------

## current status

the type checker handles ~90% of lean's Init library:

| Export File       | Decls | Passed | Failed | Coverage |
|-------------------|-------|--------|--------|----------|
| Init.Prelude      | 2036  | 1832   | 204    | 90.0%    |
| Init.Core         | 3748  | 3402   | 346    | 90.8%    |
| Init.Classical    | 8044  | 6577   | 1467   | 81.8%    |
| Init.Data.Nat.Basic| 4586 | 4050   | 536    | 88.3%    |

**working:**
- names, levels, expressions
- parsing all export format commands (including OPAQ)
- beta, let, delta, iota, projection, quotient reduction
- definitional equality with eta and proof irrelevance
- universe level normalization with succ factoring
- local context for open terms
- declaration validation
- global caching

**known limitations:**
- some complex nested inductives
- deeply nested binders in certain theorems
- tier 5+ mathlib coverage incomplete

-------------------------------------------------------------------------------

## references

- [lean4lean](https://github.com/digama0/lean4lean) - lean kernel in lean
- [nanoda_lib](https://github.com/ammkrn/nanoda_lib) - lean kernel in rust
- [type checking in lean 4](https://ammkrn.github.io/type_checking_in_lean4/) - documentation
- [lean4export](https://github.com/leanprover/lean4export) - the export format

```
@misc{lean4idris2025,
  title = {lean4idris: a lean 4 kernel in idris 2},
  url = {https://github.com/spikedoanz/lean4idris},
  year = {2025}
}
```
