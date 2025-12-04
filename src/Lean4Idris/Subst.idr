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
public export
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
public export
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
public export
instantiateLevelParams : List Name -> List Level -> Expr n -> Expr n
instantiateLevelParams names levels e =
  substLevelParams (zip names levels) e

||| Safely instantiate universe level parameters with occur check
||| Returns Nothing if any substitution would create a cycle
public export
instantiateLevelParamsSafe : List Name -> List Level -> Expr n -> Maybe (Expr n)
instantiateLevelParamsSafe names levels e =
  substLevelParamsSafe (zip names levels) e
