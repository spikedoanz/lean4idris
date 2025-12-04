||| Reduction Relations
|||
||| This module defines the reduction relation for dependent type theory:
||| - β-reduction: (λx.b) a → b[x := a]
||| - ζ-reduction: let x = v in e → e[x := v]
||| - Congruence rules for reducing under constructors
|||
||| We define both single-step reduction and multi-step reduction.
module Lean4Idris.Proofs.Reduction

import Data.Fin
import Lean4Idris.Proofs.Syntax
import Lean4Idris.Proofs.Substitution

%default total

------------------------------------------------------------------------
-- Single-Step Reduction
------------------------------------------------------------------------

||| Single-step reduction: e → e'
|||
||| This relation captures one step of computation.
||| A term is in normal form if no rule applies.
public export
data Step : Expr n -> Expr n -> Type where

  ||| β-reduction: (λ(x:A). b) a → b[x := a]
  |||
  ||| The fundamental computation rule for lambda calculus.
  ||| Applying a lambda to an argument substitutes the argument
  ||| for the bound variable in the body.
  SBeta : Step (App (Lam ty body) arg) (subst0 body arg)

  ||| ζ-reduction: let x : A = v in e → e[x := v]
  |||
  ||| Let bindings are just sugar for β-reduction.
  SZeta : Step (Let ty val body) (subst0 body val)

  ||| Congruence: reduce the function in an application
  |||
  |||   f → f'
  ||| ───────────
  |||   f x → f' x
  SAppL : Step f f' -> Step (App f x) (App f' x)

  ||| Congruence: reduce the argument in an application
  |||
  |||   x → x'
  ||| ───────────
  |||   f x → f x'
  SAppR : Step x x' -> Step (App f x) (App f x')

  ||| Congruence: reduce under lambda (in the body)
  |||
  |||   b → b'
  ||| ─────────────────
  |||   λ(x:A). b → λ(x:A). b'
  SLamBody : Step body body' -> Step (Lam ty body) (Lam ty body')

  ||| Congruence: reduce the type annotation in lambda
  |||
  |||   A → A'
  ||| ─────────────────
  |||   λ(x:A). b → λ(x:A'). b
  SLamTy : Step ty ty' -> Step (Lam ty body) (Lam ty' body)

  ||| Congruence: reduce in Pi domain
  |||
  |||   A → A'
  ||| ─────────────────────
  |||   (x : A) → B → (x : A') → B
  SPiDom : Step dom dom' -> Step (Pi dom cod) (Pi dom' cod)

  ||| Congruence: reduce in Pi codomain
  |||
  |||   B → B'
  ||| ─────────────────────
  |||   (x : A) → B → (x : A) → B'
  SPiCod : Step cod cod' -> Step (Pi dom cod) (Pi dom cod')

  ||| Congruence: reduce in let type
  SLetTy : Step ty ty' -> Step (Let ty val body) (Let ty' val body)

  ||| Congruence: reduce in let value
  SLetVal : Step val val' -> Step (Let ty val body) (Let ty val' body)

  ||| Congruence: reduce in let body
  SLetBody : Step body body' -> Step (Let ty val body) (Let ty val body')

------------------------------------------------------------------------
-- Multi-Step Reduction (Reflexive-Transitive Closure)
------------------------------------------------------------------------

||| Multi-step reduction: e →* e'
|||
||| Zero or more steps of reduction.
public export
data Steps : Expr n -> Expr n -> Type where
  ||| Zero steps: e →* e
  Refl : Steps e e

  ||| One or more steps: e → e' →* e''
  Trans : Step e e' -> Steps e' e'' -> Steps e e''

||| Single step is also multi-step
public export
single : Step e e' -> Steps e e'
single s = Trans s Refl

||| Compose multi-step reductions
public export
(++) : Steps e1 e2 -> Steps e2 e3 -> Steps e1 e3
(++) Refl s2 = s2
(++) (Trans s1 s1') s2 = Trans s1 (s1' ++ s2)

------------------------------------------------------------------------
-- Normal Forms
------------------------------------------------------------------------

||| A term is in normal form if it cannot reduce
public export
NormalForm : Expr n -> Type
NormalForm e = (e' : Expr n) -> Step e e' -> Void

||| Values: canonical forms that are "done computing"
||| (In full dependent types, this is more subtle)
public export
data Value : Expr n -> Type where
  VSort : Value (Sort l)
  VPi : Value (Pi dom cod)
  VLam : Value (Lam ty body)
  VVar : Value (Var i)  -- Neutral: stuck on a variable

------------------------------------------------------------------------
-- Properties of Reduction
------------------------------------------------------------------------

||| β-reduction is deterministic at the head
||| (Full reduction is not deterministic due to choice of redex)
public export
betaDeterministic : Step (App (Lam ty body) arg) e1
                 -> Step (App (Lam ty body) arg) e2
                 -> (e1 = e2) `Either` (Step e1 e2, Step e2 e1)
betaDeterministic SBeta SBeta = Left Refl
betaDeterministic SBeta (SAppL (SLamBody _)) = ?betaDet1
betaDeterministic SBeta (SAppL (SLamTy _)) = ?betaDet2
betaDeterministic SBeta (SAppR _) = ?betaDet3
betaDeterministic (SAppL s) SBeta = ?betaDet4
betaDeterministic (SAppL s1) (SAppL s2) = ?betaDet5
betaDeterministic (SAppL s1) (SAppR s2) = ?betaDet6
betaDeterministic (SAppR s) SBeta = ?betaDet7
betaDeterministic (SAppR s1) (SAppL s2) = ?betaDet8
betaDeterministic (SAppR s1) (SAppR s2) = ?betaDet9

------------------------------------------------------------------------
-- Congruence Lemmas
------------------------------------------------------------------------

||| If e →* e', then App e x →* App e' x
public export
stepsAppL : Steps f f' -> Steps (App f x) (App f' x)
stepsAppL Refl = Refl
stepsAppL (Trans s rest) = Trans (SAppL s) (stepsAppL rest)

||| If e →* e', then App f e →* App f e'
public export
stepsAppR : Steps x x' -> Steps (App f x) (App f x')
stepsAppR Refl = Refl
stepsAppR (Trans s rest) = Trans (SAppR s) (stepsAppR rest)

||| If body →* body', then Lam ty body →* Lam ty body'
public export
stepsLam : Steps body body' -> Steps (Lam ty body) (Lam ty body')
stepsLam Refl = Refl
stepsLam (Trans s rest) = Trans (SLamBody s) (stepsLam rest)

------------------------------------------------------------------------
-- Weak Head Normal Form
------------------------------------------------------------------------

||| An expression is in weak head normal form (WHNF) if it's not
||| a β-redex or let at the head.
public export
data WHNF : Expr n -> Type where
  WSort : WHNF (Sort l)
  WPi : WHNF (Pi dom cod)
  WLam : WHNF (Lam ty body)
  WVar : WHNF (Var i)
  -- App is WHNF only if head is not a lambda
  WApp : WHNF f -> (notLam : (ty : Expr n) -> (body : Expr (S n)) -> f = Lam ty body -> Void)
      -> WHNF (App f x)

||| WHNF terms don't β-reduce at the head
public export
whnfNoHead : WHNF e -> Step e e' -> Either (WHNF e') (e' = e)
whnfNoHead WSort s = absurd (sortNoStep s)
  where
    sortNoStep : Step (Sort l) e -> Void
    sortNoStep s impossible
whnfNoHead WPi (SPiDom s) = Left WPi  -- Can reduce inside
whnfNoHead WPi (SPiCod s) = Left WPi
whnfNoHead WLam (SLamBody s) = Left WLam
whnfNoHead WLam (SLamTy s) = Left WLam
whnfNoHead WVar s = absurd (varNoStep s)
  where
    varNoStep : Step (Var i) e -> Void
    varNoStep s impossible
whnfNoHead (WApp wf notLam) SBeta = absurd (notLam _ _ Refl)
whnfNoHead (WApp wf notLam) (SAppL s) = ?whnfApp1
whnfNoHead (WApp wf notLam) (SAppR s) = Left (WApp wf notLam)
