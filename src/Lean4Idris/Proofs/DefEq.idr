||| Definitional Equality
|||
||| This module defines definitional equality (≡) for dependent type theory.
||| Two expressions are definitionally equal if they reduce to a common form.
|||
||| Key properties:
||| - Reflexivity: e ≡ e
||| - Symmetry: e₁ ≡ e₂ → e₂ ≡ e₁
||| - Transitivity: e₁ ≡ e₂ → e₂ ≡ e₃ → e₁ ≡ e₃
||| - Congruence: equality is preserved by all term constructors
||| - Reduction: e → e' implies e ≡ e'
|||
||| This is the relation used in the TConv typing rule.
module Lean4Idris.Proofs.DefEq

import Data.Fin
import Lean4Idris.Proofs.Syntax
import Lean4Idris.Proofs.Substitution
import Lean4Idris.Proofs.Reduction

%default total

------------------------------------------------------------------------
-- Definitional Equality Relation
------------------------------------------------------------------------

||| Definitional equality: e₁ ≡ e₂
|||
||| This is defined as a congruence closure over reduction.
||| Two terms are definitionally equal if they can be connected
||| by a sequence of reductions and congruence rules.
|||
||| We use a direct inductive definition with:
||| - Reflexivity, symmetry, transitivity (equivalence relation)
||| - One-step reduction in either direction
||| - Congruence under all constructors
public export
data DefEq : Expr n -> Expr n -> Type where

  -- Equivalence relation

  ||| Reflexivity: e ≡ e
  DERefl : DefEq e e

  ||| Symmetry: e₁ ≡ e₂ → e₂ ≡ e₁
  DESym : DefEq e1 e2 -> DefEq e2 e1

  ||| Transitivity: e₁ ≡ e₂ → e₂ ≡ e₃ → e₁ ≡ e₃
  DETrans : DefEq e1 e2 -> DefEq e2 e3 -> DefEq e1 e3

  -- Reduction rules

  ||| Forward reduction: e → e' implies e ≡ e'
  DEStep : Step e e' -> DefEq e e'

  -- Note: backward reduction is derivable via DESym (DEStep s)

  -- Congruence rules

  ||| Pi congruence: A ≡ A' → B ≡ B' → (x:A) → B ≡ (x:A') → B'
  DEPi : DefEq dom dom' -> DefEq cod cod'
      -> DefEq (Pi dom cod) (Pi dom' cod')

  ||| Lambda congruence: A ≡ A' → b ≡ b' → λ(x:A). b ≡ λ(x:A'). b'
  DELam : DefEq ty ty' -> DefEq body body'
       -> DefEq (Lam ty body) (Lam ty' body')

  ||| Application congruence: f ≡ f' → x ≡ x' → f x ≡ f' x'
  DEApp : DefEq f f' -> DefEq x x'
       -> DefEq (App f x) (App f' x')

  ||| Let congruence
  DELet : DefEq ty ty' -> DefEq val val' -> DefEq body body'
       -> DefEq (Let ty val body) (Let ty' val' body')

  ||| Projection congruence: s ≡ s' → Proj name idx s ≡ Proj name idx s'
  DEProj : DefEq struct struct'
        -> DefEq (Proj name idx struct) (Proj name idx struct')

------------------------------------------------------------------------
-- Basic Properties
------------------------------------------------------------------------

||| Multi-step reduction implies definitional equality
public export
stepsDefEq : Steps e e' -> DefEq e e'
stepsDefEq Refl = DERefl
stepsDefEq (Trans step rest) = DETrans (DEStep step) (stepsDefEq rest)

||| Backward step: e' → e implies e ≡ e'
public export
defEqStepBack : Step e e' -> DefEq e' e
defEqStepBack step = DESym (DEStep step)

------------------------------------------------------------------------
-- Renaming Preserves DefEq
------------------------------------------------------------------------

||| Renaming preserves definitional equality.
|||
||| If e₁ ≡ e₂, then rename r e₁ ≡ rename r e₂.
public export
defEqRename : (r : Ren n m) -> DefEq e1 e2 -> DefEq (rename r e1) (rename r e2)
defEqRename r DERefl = DERefl
defEqRename r (DESym eq) = DESym (defEqRename r eq)
defEqRename r (DETrans eq1 eq2) = DETrans (defEqRename r eq1) (defEqRename r eq2)
defEqRename r (DEStep step) = DEStep (stepRename r step)
defEqRename r (DEPi dom cod) = DEPi (defEqRename r dom) (defEqRename (liftRen r) cod)
defEqRename r (DELam ty body) = DELam (defEqRename r ty) (defEqRename (liftRen r) body)
defEqRename r (DEApp f x) = DEApp (defEqRename r f) (defEqRename r x)
defEqRename r (DELet ty val body) = DELet (defEqRename r ty) (defEqRename r val) (defEqRename (liftRen r) body)
defEqRename r (DEProj s) = DEProj (defEqRename r s)

||| If e₁ ≡ e₂, then weaken e₁ ≡ weaken e₂
|||
||| This is needed for working with binders.
public export
defEqWeaken : DefEq e1 e2 -> DefEq (weaken e1) (weaken e2)
defEqWeaken = defEqRename FS

------------------------------------------------------------------------
-- Substitution Respects DefEq
------------------------------------------------------------------------

||| If e₁ ≡ e₂, then subst s e₁ ≡ subst s e₂
|||
||| Substitution preserves definitional equality.
public export
defEqSubst : (s : Sub n m) -> DefEq e1 e2 -> DefEq (subst s e1) (subst s e2)
defEqSubst s DERefl = DERefl
defEqSubst s (DESym eq) = DESym (defEqSubst s eq)
defEqSubst s (DETrans eq1 eq2) = DETrans (defEqSubst s eq1) (defEqSubst s eq2)
defEqSubst s (DEStep step) = DEStep (stepSubst s step)
defEqSubst s (DEPi dom cod) = DEPi (defEqSubst s dom) (defEqSubst (liftSub s) cod)
defEqSubst s (DELam ty body) = DELam (defEqSubst s ty) (defEqSubst (liftSub s) body)
defEqSubst s (DEApp f x) = DEApp (defEqSubst s f) (defEqSubst s x)
defEqSubst s (DELet ty val body) = DELet (defEqSubst s ty) (defEqSubst s val) (defEqSubst (liftSub s) body)
defEqSubst s (DEProj st) = DEProj (defEqSubst s st)

||| Single substitution preserves DefEq
public export
defEqSubst0 : DefEq e1 e2 -> (arg : Expr n) -> DefEq (subst0 e1 arg) (subst0 e2 arg)
defEqSubst0 eq arg = defEqSubst (singleSub arg) eq

||| Pointwise DefEq of substitutions
|||
||| Two substitutions are DefEq pointwise if for all i, s1 i ≡ s2 i.
public export
0 SubDefEq : Sub n m -> Sub n m -> Type
SubDefEq s1 s2 = (i : Fin n) -> DefEq (s1 i) (s2 i)

||| Lift preserves pointwise SubDefEq
public export
liftSubDefEq : SubDefEq s1 s2 -> SubDefEq (liftSub s1) (liftSub s2)
liftSubDefEq sEq FZ = DERefl  -- Both are Var FZ
liftSubDefEq sEq (FS i) = defEqWeaken (sEq i)

||| If s1 ≡ s2 pointwise, then subst s1 e ≡ subst s2 e (same expression)
public export
defEqSubstSame : {n : Nat} -> {m : Nat} -> {s1 : Sub n m} -> {s2 : Sub n m}
              -> SubDefEq s1 s2 -> (e : Expr n) -> DefEq (subst s1 e) (subst s2 e)
defEqSubstSame sEq (Var i) = sEq i
defEqSubstSame sEq (Sort l) = DERefl
defEqSubstSame sEq (Pi dom cod) = DEPi (defEqSubstSame sEq dom) (defEqSubstSame (liftSubDefEq sEq) cod)
defEqSubstSame sEq (Lam ty body) = DELam (defEqSubstSame sEq ty) (defEqSubstSame (liftSubDefEq sEq) body)
defEqSubstSame sEq (App f x) = DEApp (defEqSubstSame sEq f) (defEqSubstSame sEq x)
defEqSubstSame sEq (Let ty val body) = DELet (defEqSubstSame sEq ty) (defEqSubstSame sEq val) (defEqSubstSame (liftSubDefEq sEq) body)
defEqSubstSame sEq (Const n ls) = DERefl  -- Constants have no free variables
defEqSubstSame sEq (Proj sn idx s) = DEProj (defEqSubstSame sEq s)

||| If s1 ≡ s2 pointwise and e1 ≡ e2, then subst s1 e1 ≡ subst s2 e2
|||
||| Note: Full proof requires careful handling of implicit arguments across
||| recursive calls. For now, we use a hole for the complex cases.
public export
defEqSubstBoth : {n : Nat} -> {m : Nat} -> {s1 : Sub n m} -> {s2 : Sub n m}
              -> {e1 : Expr n} -> {e2 : Expr n}
              -> SubDefEq s1 s2 -> DefEq e1 e2 -> DefEq (subst s1 e1) (subst s2 e2)
defEqSubstBoth {e1} sEq DERefl = defEqSubstSame sEq e1
defEqSubstBoth sEq (DESym eq) = ?defEqSubstBoth_DESym
defEqSubstBoth sEq (DETrans eq1 eq2) = ?defEqSubstBoth_DETrans
defEqSubstBoth sEq (DEStep step) = ?defEqSubstBoth_DEStep
defEqSubstBoth sEq (DEPi dom cod) = DEPi (defEqSubstBoth sEq dom) (defEqSubstBoth (liftSubDefEq sEq) cod)
defEqSubstBoth sEq (DELam ty body) = DELam (defEqSubstBoth sEq ty) (defEqSubstBoth (liftSubDefEq sEq) body)
defEqSubstBoth sEq (DEApp f x) = DEApp (defEqSubstBoth sEq f) (defEqSubstBoth sEq x)
defEqSubstBoth sEq (DELet ty val body) = DELet (defEqSubstBoth sEq ty) (defEqSubstBoth sEq val) (defEqSubstBoth (liftSubDefEq sEq) body)
defEqSubstBoth sEq (DEProj s) = DEProj (defEqSubstBoth sEq s)

||| singleSub preserves DefEq
public export
singleSubDefEq : DefEq arg1 arg2 -> SubDefEq (singleSub arg1) (singleSub arg2)
singleSubDefEq eq FZ = eq
singleSubDefEq eq (FS i) = DERefl

||| Substituting equal arguments gives equal results
public export
defEqSubst0Arg : {n : Nat} -> {arg1 : Expr n} -> {arg2 : Expr n}
              -> (body : Expr (S n)) -> DefEq arg1 arg2 -> DefEq (subst0 body arg1) (subst0 body arg2)
defEqSubst0Arg body eq = defEqSubstBoth (singleSubDefEq eq) DERefl

------------------------------------------------------------------------
-- Key Properties for Subject Reduction
------------------------------------------------------------------------

||| If e → e', then for any context C, C[e] ≡ C[e']
||| This is captured by the congruence rules above.

||| Reduction in argument position preserves type equality
||| If arg → arg', then B[x := arg] ≡ B[x := arg']
|||
||| This is the key lemma needed for SAppR case of subject reduction.
public export
substDefEq : {n : Nat} -> {arg : Expr n} -> {arg' : Expr n}
          -> (body : Expr (S n)) -> Step arg arg'
          -> DefEq (subst0 body arg) (subst0 body arg')
substDefEq body step = defEqSubst0Arg body (DEStep step)

------------------------------------------------------------------------
-- DefEq for Types
------------------------------------------------------------------------

||| Types are definitionally equal if they reduce to a common form.
||| (Same as DefEq, but semantically meant for types.)
public export
0 TypeEq : Expr n -> Expr n -> Type
TypeEq = DefEq

||| Pi types with equal components are equal
public export
piTypeEq : TypeEq dom1 dom2 -> TypeEq cod1 cod2
        -> TypeEq (Pi dom1 cod1) (Pi dom2 cod2)
piTypeEq = DEPi

-- Context equivalence and conversion moved to CtxConversion.idr
-- to break circular dependency with Typing.idr

