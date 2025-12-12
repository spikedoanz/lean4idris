||| Substitution operations for expressions
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
import Data.Nat
import Data.List
import Data.Vect

%default total

------------------------------------------------------------------------
-- Lifting (adjusting de Bruijn indices)
------------------------------------------------------------------------

||| Lift loose bound variables by `n` starting at depth `s`.
||| Variables with index >= s get increased by n.
||| This is used to adjust the substitution argument when going under binders.
covering export
liftLooseBVars : (s : Nat) -> (n : Nat) -> Expr -> Expr
liftLooseBVars s n e = go s e
  where
    go : Nat -> Expr -> Expr
    go s (BVar idx) =
      if idx < s
        then BVar idx  -- Below cutoff, keep same
        else BVar (idx + n)  -- At or above cutoff, lift
    go s (Local id name) = Local id name  -- Free vars not affected by lifting
    go s (Sort l) = Sort l
    go s (Const name lvls) = Const name lvls
    go s (App f x) = App (go s f) (go s x)
    go s (Lam name bi ty body) = Lam name bi (go s ty) (go (S s) body)
    go s (Pi name bi ty body) = Pi name bi (go s ty) (go (S s) body)
    go s (Let name ty val body) = Let name (go s ty) (go s val) (go (S s) body)
    go s (Proj sname fieldIdx x) = Proj sname fieldIdx (go s x)
    go s (NatLit k) = NatLit k
    go s (StringLit str) = StringLit str

------------------------------------------------------------------------
-- Instantiate (proper beta reduction with depth tracking)
------------------------------------------------------------------------

||| Instantiate a single variable at depth `d` with the substitution `subst`.
||| This is the correct operation for beta reduction, tracking depth properly.
|||
||| For BVar i:
||| - If i < d: local variable bound by inner lambda, keep unchanged
||| - If i = d: the variable being substituted, replace with subst lifted by d
||| - If i > d: outer free variable, shift down by 1 (i.e., i-1)
|||
||| Following lean4lean's instantiate1' implementation.
covering export
instantiate1 : Expr -> Expr -> Expr
instantiate1 e subst = go 0 e
  where
    go : Nat -> Expr -> Expr
    go d (BVar idx) =
      if idx < d
        then BVar idx  -- Local variable, keep unchanged
        else if idx == d
          then liftLooseBVars 0 d subst  -- The variable being substituted
          else BVar (minus idx 1)  -- Outer free variable, shift down
    go d (Local id name) = Local id name  -- Free vars unchanged
    go d (Sort l) = Sort l
    go d (Const name lvls) = Const name lvls
    go d (App f x) = App (go d f) (go d x)
    go d (Lam name bi ty body) = Lam name bi (go d ty) (go (S d) body)
    go d (Pi name bi ty body) = Pi name bi (go d ty) (go (S d) body)
    go d (Let name ty val body) = Let name (go d ty) (go d val) (go (S d) body)
    go d (Proj sname fieldIdx x) = Proj sname fieldIdx (go d x)
    go d (NatLit k) = NatLit k
    go d (StringLit str) = StringLit str

------------------------------------------------------------------------
-- Level parameter substitution
------------------------------------------------------------------------

||| Substitute universe level parameters in an expression
public export covering
substLevelParams : List (Name, Level) -> Expr -> Expr
substLevelParams ps (BVar i) = BVar i
substLevelParams ps (Local id name) = Local id name
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
substLevelParamsSafe : List (Name, Level) -> Expr -> Maybe Expr
substLevelParamsSafe ps (BVar i) = Just (BVar i)
substLevelParamsSafe ps (Local id name) = Just (Local id name)
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
instantiateLevelParams : List Name -> List Level -> Expr -> Expr
instantiateLevelParams names levels e =
  substLevelParams (zip names levels) e

||| Safely instantiate universe level parameters with occur check
||| Returns Nothing if any substitution would create a cycle
public export covering
instantiateLevelParamsSafe : List Name -> List Level -> Expr -> Maybe Expr
instantiateLevelParamsSafe names levels e =
  substLevelParamsSafe (zip names levels) e

------------------------------------------------------------------------
-- Simultaneous substitution (closing open terms)
------------------------------------------------------------------------

||| Helper for substAll - recursively substitute with depth tracking
||| @depth Number of local binders we're under
||| @args List of replacements for free variables (index 0 in args = outermost free var)
goSubstAllNat : (depth : Nat) -> List Expr -> Nat -> Expr
goSubstAllNat depth args idx =
  if idx < depth
    then BVar idx  -- Local variable, keep it (index stays same)
    else case getAt (minus idx depth) args of
           Just replacement => replacement  -- Free variable, substitute
           Nothing => BVar idx  -- Shouldn't happen

covering
goSubstAll : (depth : Nat) -> List Expr -> Expr -> Expr
goSubstAll depth args (BVar idx) = goSubstAllNat depth args idx
goSubstAll depth args (Local id name) = Local id name
goSubstAll depth args (Sort l) = Sort l
goSubstAll depth args (Const name lvls) = Const name lvls
goSubstAll depth args (App f x) = App (goSubstAll depth args f) (goSubstAll depth args x)
goSubstAll depth args (Lam name bi ty body) =
  Lam name bi (goSubstAll depth args ty) (goSubstAll (S depth) args body)
goSubstAll depth args (Pi name bi ty body) =
  Pi name bi (goSubstAll depth args ty) (goSubstAll (S depth) args body)
goSubstAll depth args (Let name ty val body) =
  Let name (goSubstAll depth args ty) (goSubstAll depth args val) (goSubstAll (S depth) args body)
goSubstAll depth args (Proj sname fieldIdx s) = Proj sname fieldIdx (goSubstAll depth args s)
goSubstAll depth args (NatLit k) = NatLit k
goSubstAll depth args (StringLit s) = StringLit s

||| Substitute all free variables simultaneously with closed expressions.
||| This is the correct operation for closing an open term: given an Expr
||| with n free variables and a vector of n replacements, substitute all
||| BVar i with the i-th replacement.
|||
||| @args Vector of expressions to substitute for each free variable
||| @e The expression with free variables
covering export
substAll : Vect n Expr -> Expr -> Expr
substAll args e = goSubstAll 0 (toList args) e

||| Substitute the outermost bound variable at ALL depths with the given expression.
||| Unlike instantiate1, this replaces BVar 0 at depth 0, BVar 1 at depth 1, etc.
||| This is the correct operation for instantiating a binder for comparison purposes.
|||
||| For example, in `((a : #0) -> ((b : #1) -> T))` where both #0 and #1 refer to
||| the same outer binding, `subst0Single` will replace BOTH with the substitution,
||| whereas `instantiate1` would only replace #0 and shift #1 down to #0.
covering export
subst0Single : Expr -> Expr -> Expr
subst0Single e arg = goSubstAll 0 [arg] e

------------------------------------------------------------------------
-- Local substitution (replacing Local placeholders)
------------------------------------------------------------------------

||| Check if a specific Local ID exists in an expression.
||| Used to short-circuit substLocal on expressions that don't contain the target.
covering export
containsLocal : Nat -> Expr -> Bool
containsLocal targetId = go
  where
    go : Expr -> Bool
    go (Local id _) = id == targetId
    go (BVar _) = False
    go (Sort _) = False
    go (Const _ _) = False
    go (App f x) = go f || go x
    go (Lam _ _ ty body) = go ty || go body
    go (Pi _ _ dom cod) = go dom || go cod
    go (Let _ ty val body) = go ty || go val || go body
    go (Proj _ _ s) = go s
    go (NatLit _) = False
    go (StringLit _) = False

||| Substitute a specific Local ID with a replacement expression.
||| This is used to replace escaped Local placeholders in inferred types.
||| Short-circuits if the target Local doesn't exist in the expression.
covering export
substLocal : Nat -> Expr -> Expr -> Expr
substLocal targetId replacement expr =
  if containsLocal targetId expr
    then go expr
    else expr
  where
    go : Expr -> Expr
    go (Local id name) = if id == targetId then replacement else Local id name
    go (BVar i) = BVar i
    go (Sort l) = Sort l
    go (Const name lvls) = Const name lvls
    go (App f x) = App (go f) (go x)
    go (Lam name bi ty body) = Lam name bi (go ty) (go body)
    go (Pi name bi dom cod) = Pi name bi (go dom) (go cod)
    go (Let name ty val body) = Let name (go ty) (go val) (go body)
    go (Proj sname idx s) = Proj sname idx (go s)
    go (NatLit k) = NatLit k
    go (StringLit s) = StringLit s
