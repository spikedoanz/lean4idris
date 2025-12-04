||| Substitution operations for well-scoped expressions
|||
||| This module provides the core operations needed for beta reduction:
||| - Opening: substituting a value for the outermost bound variable
||| - Lifting: adjusting de Bruijn indices when going under binders
|||
||| Following the approach from lean4lean's VExpr.lean
module Lean4Idris.Subst

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Data.Fin
import Data.Nat
import Data.List
import Data.Vect

%default total

||| Substitute the outermost bound variable (index 0) with the given expression.
||| This is the key operation for beta reduction: (λx.body) arg → body[0 := arg]
|||
||| The implementation:
||| - BVar FZ (index 0): replace with the argument
||| - BVar (FS i): shift down by 1 (since we're removing a binder)
||| - Everything else: recurse, incrementing depth when entering binders
public export
subst0 : Expr (S n) -> Expr n -> Expr n
subst0 (BVar FZ) arg = arg
subst0 (BVar (FS i)) _ = BVar i
subst0 (Sort l) _ = Sort l
subst0 (Const name lvls) _ = Const name lvls
subst0 (App f x) arg = App (subst0 f arg) (subst0 x arg)
subst0 (Lam name bi ty body) arg =
  Lam name bi (subst0 ty arg) (subst0 body (weaken1 arg))
subst0 (Pi name bi ty body) arg =
  Pi name bi (subst0 ty arg) (subst0 body (weaken1 arg))
subst0 (Let name ty val body) arg =
  Let name (subst0 ty arg) (subst0 val arg) (subst0 body (weaken1 arg))
subst0 (Proj sname idx s) arg = Proj sname idx (subst0 s arg)
subst0 (NatLit k) _ = NatLit k
subst0 (StringLit s) _ = StringLit s

||| Substitute universe level parameters in an expression
public export covering
substLevelParams : List (Name, Level) -> Expr n -> Expr n
substLevelParams ps (BVar i) = BVar i
substLevelParams ps (Sort l) = Sort (substParams ps l)
substLevelParams ps (Const name lvls) = Const name (map (substParams ps) lvls)
substLevelParams ps (App f x) = App (substLevelParams ps f) (substLevelParams ps x)
substLevelParams ps (Lam name bi ty body) =
  Lam name bi (substLevelParams ps ty) (substLevelParams ps body)
substLevelParams ps (Pi name bi ty body) =
  Pi name bi (substLevelParams ps ty) (substLevelParams ps body)
substLevelParams ps (Let name ty val body) =
  Let name (substLevelParams ps ty) (substLevelParams ps val) (substLevelParams ps body)
substLevelParams ps (Proj sname idx s) = Proj sname idx (substLevelParams ps s)
substLevelParams ps (NatLit k) = NatLit k
substLevelParams ps (StringLit s) = StringLit s

||| Safely substitute universe level parameters with occur check
||| Returns Nothing if any substitution would create a cycle
public export covering
substLevelParamsSafe : List (Name, Level) -> Expr n -> Maybe (Expr n)
substLevelParamsSafe ps (BVar i) = Just (BVar i)
substLevelParamsSafe ps (Sort l) = Sort <$> substParamsSafe ps l
substLevelParamsSafe ps (Const name lvls) = Const name <$> traverse (substParamsSafe ps) lvls
substLevelParamsSafe ps (App f x) =
  [| App (substLevelParamsSafe ps f) (substLevelParamsSafe ps x) |]
substLevelParamsSafe ps (Lam name bi ty body) =
  [| Lam (pure name) (pure bi) (substLevelParamsSafe ps ty) (substLevelParamsSafe ps body) |]
substLevelParamsSafe ps (Pi name bi ty body) =
  [| Pi (pure name) (pure bi) (substLevelParamsSafe ps ty) (substLevelParamsSafe ps body) |]
substLevelParamsSafe ps (Let name ty val body) =
  [| Let (pure name) (substLevelParamsSafe ps ty) (substLevelParamsSafe ps val) (substLevelParamsSafe ps body) |]
substLevelParamsSafe ps (Proj sname idx s) = Proj sname idx <$> substLevelParamsSafe ps s
substLevelParamsSafe ps (NatLit k) = Just (NatLit k)
substLevelParamsSafe ps (StringLit s) = Just (StringLit s)

||| Instantiate universe level parameters from a list
||| Given param names and corresponding level values, substitute them
public export covering
instantiateLevelParams : List Name -> List Level -> Expr n -> Expr n
instantiateLevelParams names levels e =
  substLevelParams (zip names levels) e

||| Safely instantiate universe level parameters with occur check
||| Returns Nothing if any substitution would create a cycle
public export covering
instantiateLevelParamsSafe : List Name -> List Level -> Expr n -> Maybe (Expr n)
instantiateLevelParamsSafe names levels e =
  substLevelParamsSafe (zip names levels) e

------------------------------------------------------------------------
-- Simultaneous substitution (closing open terms)
------------------------------------------------------------------------

||| Weaken a closed expression to any scope depth (uses believe_me since
||| ClosedExpr has no BVars, indices don't need adjustment)
weakenBy : (d : Nat) -> ClosedExpr -> Expr d
weakenBy d e = believe_me e

||| Substitute all free variables simultaneously with closed expressions.
||| This is the correct operation for closing an open term: given `Expr n`
||| and a vector of n replacements, substitute all BVar i with the i-th replacement.
|||
||| Unlike iterative subst0, this handles nested binders correctly because
||| we track the current depth and adjust indices accordingly.
|||
||| @args Vector of closed expressions to substitute for each free variable
||| @e The expression with n free variables
||| Helper for substAll - recursively substitute with depth tracking
||| Uses explicit Nat index to avoid type complexity with Fin
||| @depth Number of local binders we're under
||| @args List of replacements for free variables (index 0 in args = outermost free var)
goSubstAllNat : (depth : Nat) -> List ClosedExpr -> Nat -> ClosedExpr
goSubstAllNat depth args idx =
  if idx < depth
    then BVar (believe_me idx)  -- Local variable, keep it (index stays same)
    else case getAt (minus idx depth) args of
           Just replacement => replacement  -- Free variable, substitute
           Nothing => BVar (believe_me idx)  -- Shouldn't happen

covering
goSubstAll : (depth : Nat) -> List ClosedExpr -> ClosedExpr -> ClosedExpr
goSubstAll depth args (BVar idx) = goSubstAllNat depth args (finToNat idx)
goSubstAll depth args (Sort l) = Sort l
goSubstAll depth args (Const name lvls) = Const name lvls
goSubstAll depth args (App f x) = App (goSubstAll depth args f) (goSubstAll depth args x)
goSubstAll depth args (Lam name bi ty body) =
  Lam name bi (goSubstAll depth args ty) (believe_me (goSubstAll (S depth) args (believe_me body)))
goSubstAll depth args (Pi name bi ty body) =
  Pi name bi (goSubstAll depth args ty) (believe_me (goSubstAll (S depth) args (believe_me body)))
goSubstAll depth args (Let name ty val body) =
  Let name (goSubstAll depth args ty) (goSubstAll depth args val) (believe_me (goSubstAll (S depth) args (believe_me body)))
goSubstAll depth args (Proj sname fieldIdx s) = Proj sname fieldIdx (goSubstAll depth args s)
goSubstAll depth args (NatLit k) = NatLit k
goSubstAll depth args (StringLit s) = StringLit s

covering export
substAll : Vect n ClosedExpr -> Expr n -> ClosedExpr
substAll args e = goSubstAll 0 (toList args) (believe_me e)

||| Substitute the outermost bound variable at ALL depths with the given expression.
||| Unlike subst0, this replaces BVar 0 at depth 0, BVar 1 at depth 1, etc.
||| This is the correct operation for instantiating a binder for comparison purposes.
|||
||| For example, in `((a : #0) -> ((b : #1) -> T))` where both #0 and #1 refer to
||| the same outer binding, `subst0Single` will replace BOTH with the substitution,
||| whereas `subst0` would only replace #0 and shift #1 down to #0.
covering export
subst0Single : Expr 1 -> ClosedExpr -> ClosedExpr
subst0Single e arg = goSubstAll 0 [arg] (believe_me e)

||| Generalized version of subst0Single that works at any scope depth.
||| Given (Expr (S n)) and (Expr n), substitutes the outermost bound variable.
||| This is useful for beta reduction in open contexts.
|||
||| Uses believe_me internally since we just need to substitute BVar 0
||| (at all depths) with the argument, treating all other vars as free.
covering export
subst0SingleN : {n : Nat} -> Expr (S n) -> Expr n -> Expr n
subst0SingleN body arg = believe_me (goSubstAll 0 [believe_me arg] (believe_me body))
