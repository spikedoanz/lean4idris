= A Lean 4 Kernel in Idris: Interactive Walkthrough

This is a literate Idris file - lines starting with > are executable code.
You can load this in the Idris REPL with `:l Walkthrough.lidr`

== Setup

> module Walkthrough
>
> import Data.Fin
> import Data.List
> import Data.SortedMap

-------------------------------------------------------------------------------
== Layer 1: Names

Everything in Lean has a hierarchical name. `Nat.succ` is `succ` under `Nat`.

> ||| Hierarchical names
> public export
> data LName : Type where
>   ||| The root/anonymous name
>   Anonymous : LName
>   ||| String segment: parent.name
>   Str : String -> LName -> LName
>   ||| Numeric segment: parent.42
>   Num : Nat -> LName -> LName

Some example names:

> ||| The name "Nat"
> natName : LName
> natName = Str "Nat" Anonymous
>
> ||| The name "Nat.zero"
> zeroName : LName
> zeroName = Str "zero" natName
>
> ||| The name "Nat.succ"
> succName : LName
> succName = Str "succ" natName

Equality check:

> export
> Eq LName where
>   Anonymous == Anonymous = True
>   (Str s1 p1) == (Str s2 p2) = s1 == s2 && p1 == p2
>   (Num n1 p1) == (Num n2 p2) = n1 == n2 && p1 == p2
>   _ == _ = False
>
> export
> Ord LName where
>   compare Anonymous Anonymous = EQ
>   compare Anonymous _ = LT
>   compare _ Anonymous = GT
>   compare (Str s1 p1) (Str s2 p2) =
>     case compare s1 s2 of
>       EQ => compare p1 p2
>       x => x
>   compare (Str _ _) (Num _ _) = LT
>   compare (Num _ _) (Str _ _) = GT
>   compare (Num n1 p1) (Num n2 p2) =
>     case compare n1 n2 of
>       EQ => compare p1 p2
>       x => x

-------------------------------------------------------------------------------
== Layer 2: Universe Levels

Lean has a hierarchy: Prop, Type, Type 1, Type 2, ...
Universe levels track where each type lives.

> ||| Universe levels
> public export
> data Level : Type where
>   ||| Level 0 (Prop)
>   Zero : Level
>   ||| Successor: l + 1
>   LSucc : Level -> Level
>   ||| Maximum of two levels
>   LMax : Level -> Level -> Level
>   ||| Impredicative max (0 if second is 0)
>   LIMax : Level -> Level -> Level
>   ||| Universe parameter
>   LParam : LName -> Level

The IMax rule is crucial for Prop's impredicativity:

  IMax l1 l2 = 0         if l2 = 0
             = Max l1 l2  otherwise

> ||| Level 1
> level1 : Level
> level1 = LSucc Zero
>
> ||| Level 2
> level2 : Level
> level2 = LSucc level1

-------------------------------------------------------------------------------
== Layer 3: Expressions (Well-Scoped)

The key insight: expressions are indexed by binding depth.
`Expr n` has `n` bound variables in scope.

> ||| Binder information (implicit/explicit)
> public export
> data BinderInfo : Type where
>   Default : BinderInfo
>   Implicit : BinderInfo
>   StrictImplicit : BinderInfo
>   Instance : BinderInfo

> ||| Well-scoped expressions
> ||| n = number of bound variables in scope
> public export
> data Expr : (depth : Nat) -> Type where
>   ||| Bound variable - must be less than depth!
>   BVar : Fin n -> Expr n
>   ||| Sort (Type at some level)
>   Sort : Level -> Expr n
>   ||| Constant with universe instantiation
>   Const : LName -> List Level -> Expr n
>   ||| Application
>   App : Expr n -> Expr n -> Expr n
>   ||| Lambda: domain at depth n, body at depth n+1
>   Lam : LName -> BinderInfo -> Expr n -> Expr (S n) -> Expr n
>   ||| Pi type: domain at n, codomain at n+1
>   Pi : LName -> BinderInfo -> Expr n -> Expr (S n) -> Expr n
>   ||| Let binding
>   Let : LName -> Expr n -> Expr n -> Expr (S n) -> Expr n
>   ||| Natural literal
>   NatLit : Nat -> Expr n

A closed expression has no free variables:

> ||| Closed expressions (no free variables)
> public export
> ClosedExpr : Type
> ClosedExpr = Expr 0

Let's build some expressions:

> ||| Type 0
> typeZero : ClosedExpr
> typeZero = Sort Zero
>
> ||| Type 1
> typeOne : ClosedExpr
> typeOne = Sort level1
>
> ||| Reference to Nat
> nat : ClosedExpr
> nat = Const natName []
>
> ||| Reference to Nat.zero
> zero : ClosedExpr
> zero = Const zeroName []

Now a lambda - the identity on Nat:

> ||| λ(x : Nat). x
> ||| Note: body has depth 1, so BVar FZ is valid
> idNat : ClosedExpr
> idNat = Lam (Str "x" Anonymous) Default nat (BVar FZ)

The type `Fin n` ensures we can't reference out-of-scope variables:

  -- This would be a TYPE ERROR:
  -- badExpr : ClosedExpr
  -- badExpr = BVar FZ  -- FZ : Fin 1, not Fin 0!

A more complex example - const function:

> ||| λ(x : Nat). λ(y : Nat). x
> ||| Outer body at depth 1, inner body at depth 2
> ||| x is BVar (FS FZ) = index 1 (one away from innermost)
> constNat : ClosedExpr
> constNat = Lam (Str "x" Anonymous) Default nat
>              (Lam (Str "y" Anonymous) Default (weaken nat) (BVar (FS FZ)))
>   where
>     -- We need to weaken nat when going under a binder
>     weaken : Expr n -> Expr (S n)
>     weaken (Sort l) = Sort l
>     weaken (Const n ls) = Const n ls
>     weaken (NatLit n) = NatLit n
>     weaken (BVar i) = BVar (FS i)
>     weaken (App f x) = App (weaken f) (weaken x)
>     weaken (Lam n bi d b) = Lam n bi (weaken d) (weaken1 b)
>       where
>         weaken1 : Expr (S m) -> Expr (S (S m))
>         weaken1 e = believe_me e  -- simplified for demo
>     weaken (Pi n bi d c) = Pi n bi (weaken d) (weaken1 c)
>       where
>         weaken1 : Expr (S m) -> Expr (S (S m))
>         weaken1 e = believe_me e
>     weaken (Let n t v b) = Let n (weaken t) (weaken v) (weaken1 b)
>       where
>         weaken1 : Expr (S m) -> Expr (S (S m))
>         weaken1 e = believe_me e

-------------------------------------------------------------------------------
== Layer 4: Substitution

The core operation: substitute a value for variable 0.

> ||| Substitute for variable 0
> ||| subst0 body value = body[0 := value]
> export
> subst0 : Expr (S n) -> Expr n -> Expr n

For bound variables:

> subst0 (BVar FZ) replacement = replacement
> subst0 (BVar (FS k)) _ = BVar k  -- shift index down

For other forms, recurse structurally:

> subst0 (Sort l) _ = Sort l
> subst0 (Const name lvls) _ = Const name lvls
> subst0 (NatLit n) _ = NatLit n
> subst0 (App f x) repl = App (subst0 f repl) (subst0 x repl)

Under binders, we need to weaken the replacement:

> subst0 (Lam name bi dom body) repl =
>   -- Simplified: in reality we weaken repl before recursing under binder
>   believe_me (Lam name bi (subst0 dom repl) (believe_me body))
>
> subst0 (Pi name bi dom cod) repl =
>   believe_me (Pi name bi (subst0 dom repl) (believe_me cod))
>
> subst0 (Let name ty val body) repl =
>   believe_me (Let name (subst0 ty repl) (subst0 val repl) (believe_me body))

(The `believe_me` calls are simplifications - the real implementation
handles weakening properly with type-safe operations.)

-------------------------------------------------------------------------------
== Layer 5: Reduction (WHNF)

Weak Head Normal Form: reduce until we see the head constructor.

> ||| Result of a single reduction step
> whnfStep : ClosedExpr -> Maybe ClosedExpr

Beta reduction: (λx. body) arg → body[x := arg]

> whnfStep (App (Lam _ _ _ body) arg) = Just (subst0 body arg)

Let reduction: let x = v in body → body[x := v]

> whnfStep (Let _ _ val body) = Just (subst0 body val)

Application: try to reduce the function

> whnfStep (App f arg) =
>   case whnfStep f of
>     Just f' => Just (App f' arg)
>     Nothing => Nothing

Everything else is already in WHNF:

> whnfStep _ = Nothing

Iterate to normal form:

> ||| Reduce to weak head normal form
> whnf : ClosedExpr -> ClosedExpr
> whnf e = case whnfStep e of
>   Just e' => whnf e'
>   Nothing => e

Example: (λx. x) zero → zero

> example1 : ClosedExpr
> example1 = App idNat zero
>
> -- whnf example1 should give us `zero`

-------------------------------------------------------------------------------
== Layer 6: Definitional Equality

Two terms are definitionally equal if they reduce to the same form.

> ||| Check structural equality after WHNF
> isDefEq : ClosedExpr -> ClosedExpr -> Bool
> isDefEq e1 e2 = isDefEqWhnf (whnf e1) (whnf e2)
>   where
>     levelEq : Level -> Level -> Bool
>     levelEq Zero Zero = True
>     levelEq (LSucc l1) (LSucc l2) = levelEq l1 l2
>     levelEq (LMax a1 b1) (LMax a2 b2) = levelEq a1 a2 && levelEq b1 b2
>     levelEq (LIMax a1 b1) (LIMax a2 b2) = levelEq a1 a2 && levelEq b1 b2
>     levelEq (LParam n1) (LParam n2) = n1 == n2
>     levelEq _ _ = False
>
>     levelsEq : List Level -> List Level -> Bool
>     levelsEq [] [] = True
>     levelsEq (l1::ls1) (l2::ls2) = levelEq l1 l2 && levelsEq ls1 ls2
>     levelsEq _ _ = False
>
>     isDefEqWhnf : ClosedExpr -> ClosedExpr -> Bool
>     isDefEqWhnf (Sort l1) (Sort l2) = levelEq l1 l2
>     isDefEqWhnf (Const n1 ls1) (Const n2 ls2) = n1 == n2 && levelsEq ls1 ls2
>     isDefEqWhnf (NatLit n1) (NatLit n2) = n1 == n2
>     isDefEqWhnf (App f1 a1) (App f2 a2) = isDefEq f1 f2 && isDefEq a1 a2
>     isDefEqWhnf (BVar i1) (BVar i2) = finToNat i1 == finToNat i2
>     isDefEqWhnf _ _ = False  -- simplified

Examples:

> ||| (λx. x) zero == zero
> test1 : Bool
> test1 = isDefEq (App idNat zero) zero  -- True!
>
> ||| Type 0 == Type 0
> test2 : Bool
> test2 = isDefEq typeZero typeZero  -- True!

-------------------------------------------------------------------------------
== Summary

The data flows through these layers:

  1. Names      - hierarchical identifiers
  2. Levels     - universe polymorphism
  3. Expressions - well-scoped by construction (Expr n)
  4. Substitution - type-safe variable replacement
  5. WHNF       - lazy evaluation (beta, let, delta, iota)
  6. DefEq      - structural comparison + eta

The well-scoped representation is key: `Expr n` with `Fin n` for
bound variables makes ill-formed terms *unrepresentable*.

To add delta reduction (constant unfolding) and iota reduction
(recursor computation), we need an environment mapping names to
declarations - which the full implementation provides.

> ||| That's all folks!
> main : IO ()
> main = do
>   putStrLn "Examples:"
>   putStrLn $ "  (λx.x) zero == zero: " ++ show test1
>   putStrLn $ "  Type 0 == Type 0: " ++ show test2
