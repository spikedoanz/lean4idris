= Typing Under Binders: Local Context Walkthrough

This literate Idris file demonstrates local context and open term typing.
Load with: pack repl src/WalkthroughLocalCtx.lidr

> module WalkthroughLocalCtx
>
> import Data.Fin
> import Data.Vect
> import Data.List

-------------------------------------------------------------------------------
== The Problem: Open Terms

When we type λ(x : Nat). x, the body 'x' is a bound variable.
We need to know its type - but that depends on the binder we're under.

> ||| Well-scoped expressions (simplified from the real implementation)
> public export
> data Expr : Nat -> Type where
>   BVar : Fin n -> Expr n
>   Sort : Nat -> Expr n  -- simplified: just use Nat for level
>   Const : String -> Expr n
>   App : Expr n -> Expr n -> Expr n
>   Lam : String -> Expr n -> Expr (S n) -> Expr n
>   Pi : String -> Expr n -> Expr (S n) -> Expr n
>
> ||| Closed expression (no free variables)
> ClosedExpr : Type
> ClosedExpr = Expr 0

Let's look at the identity function:

> ||| λ(x : Nat). x
> ||| Domain: Nat (closed)
> ||| Body: BVar FZ (index 0, references x)
> idNat : ClosedExpr
> idNat = Lam "x" (Const "Nat") (BVar FZ)

The body BVar FZ has type Expr 1 - one variable in scope.
To type it, we need to track that variable 0 has type Nat.

-------------------------------------------------------------------------------
== Local Context

A local context maps each bound variable to its type.

> ||| Entry for a bound variable
> public export
> record LocalEntry where
>   constructor MkEntry
>   name : String
>   type : ClosedExpr

> ||| Context with n bound variables
> public export
> LocalCtx : Nat -> Type
> LocalCtx n = Vect n LocalEntry

> ||| Empty context (for closed terms)
> emptyCtx : LocalCtx 0
> emptyCtx = []

> ||| Extend context when going under a binder
> extendCtx : String -> ClosedExpr -> LocalCtx n -> LocalCtx (S n)
> extendCtx name ty ctx = MkEntry name ty :: ctx

> ||| Look up a variable's type
> lookupCtx : Fin n -> LocalCtx n -> LocalEntry
> lookupCtx FZ (e :: _) = e
> lookupCtx (FS k) (_ :: ctx) = lookupCtx k ctx

-------------------------------------------------------------------------------
== Typing Open Terms

Now we can type open expressions by tracking context.

> ||| Weaken: shift all indices up by 1
> weaken : Expr n -> Expr (S n)
> weaken (BVar i) = BVar (FS i)
> weaken (Sort l) = Sort l
> weaken (Const c) = Const c
> weaken (App f x) = App (weaken f) (weaken x)
> weaken (Lam n t b) = Lam n (weaken t) (weaken1 b)
>   where
>     weaken1 : Expr (S m) -> Expr (S (S m))
>     weaken1 e = believe_me e  -- simplified
> weaken (Pi n t b) = Pi n (weaken t) (weaken1 b)
>   where
>     weaken1 : Expr (S m) -> Expr (S (S m))
>     weaken1 e = believe_me e

> ||| Close an expression by substituting placeholders
> ||| (Simplified - real impl uses subst0)
> closeExpr : LocalCtx n -> Expr n -> ClosedExpr
> closeExpr [] e = e
> closeExpr (_ :: ctx) e = closeExpr ctx (believe_me e)

> ||| Type inference result
> data TCResult = Ok ClosedExpr | Err String

> ||| Infer type of an open expression
> inferTypeOpen : LocalCtx n -> Expr n -> TCResult

BVar: look up in context

> inferTypeOpen ctx (BVar i) = Ok (lookupCtx i ctx).type

Sort: type is Sort (level + 1)

> inferTypeOpen _ (Sort l) = Ok (Sort (S l))

Const: simplified - just return a placeholder

> inferTypeOpen _ (Const c) = Ok (Sort 1)

App: infer function type, return codomain
(simplified - real impl substitutes arg into codomain)

> inferTypeOpen ctx (App f x) =
>   case inferTypeOpen ctx f of
>     Err e => Err e
>     Ok (Pi _ dom cod) => Ok (believe_me cod)  -- should subst x
>     Ok _ => Err "expected function type"

Lam: type is Pi

> inferTypeOpen ctx (Lam name dom body) =
>   let domClosed = closeExpr ctx dom
>       ctx' = extendCtx name domClosed ctx
>   in case inferTypeOpen ctx' body of
>        Err e => Err e
>        Ok bodyTy => Ok (Pi name domClosed (weaken bodyTy))

Pi: type is Sort (max of domain and codomain levels)

> inferTypeOpen ctx (Pi name dom cod) =
>   let domClosed = closeExpr ctx dom
>       ctx' = extendCtx name domClosed ctx
>   in case (inferTypeOpen ctx dom, inferTypeOpen ctx' cod) of
>        (Ok (Sort l1), Ok (Sort l2)) => Ok (Sort (max l1 l2))
>        _ => Err "expected sorts"

-------------------------------------------------------------------------------
== Examples

> ||| Show a closed expression (simplified)
> showExpr : ClosedExpr -> String
> showExpr (Sort l) = "Sort " ++ show l
> showExpr (Const c) = c
> showExpr (Pi n d _) = "(" ++ n ++ " : " ++ showExpr d ++ ") -> ..."
> showExpr _ = "<expr>"

> ||| Show result
> showResult : TCResult -> String
> showResult (Ok e) = showExpr e
> showResult (Err s) = "Error: " ++ s

Example 1: BVar in context

> example1 : TCResult
> example1 =
>   let ctx = extendCtx "x" (Const "Nat") emptyCtx
>   in inferTypeOpen ctx (BVar FZ)
> -- Result: Nat

Example 2: Identity function λ(x : Nat). x

> example2 : TCResult
> example2 = inferTypeOpen emptyCtx idNat
> -- Result: (x : Nat) -> ...

Example 3: Nested lambdas λ(x : Nat). λ(y : Nat). x

> constNat : ClosedExpr
> constNat = Lam "x" (Const "Nat")
>              (Lam "y" (weaken (Const "Nat"))
>                (BVar (FS FZ)))  -- x is index 1!

> example3 : TCResult
> example3 = inferTypeOpen emptyCtx constNat

-------------------------------------------------------------------------------
== The Key Insight

When typing λ(x : A). body:

1. Close A to get a ClosedExpr (for the context)
2. Extend context: ctx' = [x : A] ++ ctx
3. Type body in ctx' - now BVar FZ has type A
4. Result is Pi x A (type of body)

The context grows as we go under binders:

  inferTypeOpen []           (Lam "x" Nat ...)
    inferTypeOpen [x:Nat]      (Lam "y" Nat ...)
      inferTypeOpen [y:Nat, x:Nat]  (BVar (FS FZ))
        -- look up index 1 → x : Nat

Variable indices count from innermost binder outward.

-------------------------------------------------------------------------------
== Run Examples

> main : IO ()
> main = do
>   putStrLn "Local Context Examples"
>   putStrLn "======================"
>   putStrLn ""
>   putStrLn "Example 1: With ctx [x : Nat], type of 'x'"
>   putStrLn $ "  Result: " ++ showResult example1
>   putStrLn ""
>   putStrLn "Example 2: Type of λ(x : Nat). x"
>   putStrLn $ "  Result: " ++ showResult example2
>   putStrLn ""
>   putStrLn "Example 3: Type of λ(x : Nat). λ(y : Nat). x"
>   putStrLn $ "  Result: " ++ showResult example3
