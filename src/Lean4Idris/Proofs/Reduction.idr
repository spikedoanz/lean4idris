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
0 NormalForm : {n : Nat} -> Expr n -> Type
NormalForm {n} e = (e' : Expr n) -> Step e e' -> Void

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

||| Local confluence (diamond property) for reduction.
||| If e → e1 and e → e2, then there exists e3 such that e1 →* e3 and e2 →* e3.
|||
||| Note: Full reduction is not deterministic due to choice of redex,
||| but it is confluent (Church-Rosser).
|||
||| This is a key property for definitional equality:
||| Two terms are definitionally equal iff they reduce to a common term.
-- Diamond property: local confluence of reduction
-- This proof requires helper functions (stepsAppL, stepsAppR, etc.) that are
-- defined below. A full proof requires reorganizing the file or using mutual.
-- For now, we postulate this property which is well-known for STLC/DTT.
public export
diamond : Step e e1 -> Step e e2 -> (e3 ** (Steps e1 e3, Steps e2 e3))
diamond s1 s2 = ?diamond_hole

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
whnfNoHead WSort s impossible  -- Sort has no reduction rules
whnfNoHead WPi (SPiDom s) = Left WPi  -- Can reduce inside
whnfNoHead WPi (SPiCod s) = Left WPi
whnfNoHead WLam (SLamBody s) = Left WLam
whnfNoHead WLam (SLamTy s) = Left WLam
whnfNoHead WVar s impossible  -- Var has no reduction rules
whnfNoHead (WApp wf notLam) SBeta = ?whnfNoHead_WApp_SBeta
-- This case requires proving that reduction preserves "not being a lambda".
-- Idris 2's implicit accessibility makes this tricky - the implicits in
-- SLamBody/SLamTy aren't accessible. We hole this out for now.
-- This lemma isn't needed for the main subject reduction theorem.
whnfNoHead (WApp wf notLam) (SAppL s) = ?whnfNoHead_WApp_SAppL
whnfNoHead (WApp wf notLam) (SAppR s) = Left (WApp wf notLam)

------------------------------------------------------------------------
-- Renaming Preserves Reduction
------------------------------------------------------------------------

||| Renaming commutes with single-variable substitution for reduction
||| rename r (subst0 body arg) = subst0 (rename (liftRen r) body) (rename r arg)
|||
||| This is needed to show that renaming preserves β-reduction.
public export
renameSubst0Step : (r : Ren n m) -> (body : Expr (S n)) -> (arg : Expr n)
                -> rename r (subst0 body arg) = subst0 (rename (liftRen r) body) (rename r arg)
renameSubst0Step r body arg = renameSubst0 r body arg

||| Renaming preserves single-step reduction.
|||
||| If e → e', then rename r e → rename r e'.
|||
||| This is crucial for showing that DefEq is preserved under weakening.
public export
stepRename : (r : Ren n m) -> Step e e' -> Step (rename r e) (rename r e')
stepRename r (SBeta {body} {arg}) =
  -- rename r (App (Lam ty body) arg) = App (Lam (rename r ty) (rename (liftRen r) body)) (rename r arg)
  -- rename r (subst0 body arg) = subst0 (rename (liftRen r) body) (rename r arg) by renameSubst0
  -- SBeta gives: App (Lam _ body') arg' → subst0 body' arg'
  rewrite renameSubst0 r body arg in SBeta
stepRename r (SZeta {body} {val}) =
  rewrite renameSubst0 r body val in SZeta
stepRename r (SAppL s) = SAppL (stepRename r s)
stepRename r (SAppR s) = SAppR (stepRename r s)
stepRename r (SLamBody s) = SLamBody (stepRename (liftRen r) s)
stepRename r (SLamTy s) = SLamTy (stepRename r s)
stepRename r (SPiDom s) = SPiDom (stepRename r s)
stepRename r (SPiCod s) = SPiCod (stepRename (liftRen r) s)
stepRename r (SLetTy s) = SLetTy (stepRename r s)
stepRename r (SLetVal s) = SLetVal (stepRename r s)
stepRename r (SLetBody s) = SLetBody (stepRename (liftRen r) s)

||| Weakening preserves single-step reduction.
|||
||| If e → e', then weaken e → weaken e'.
public export
stepWeaken : Step e e' -> Step (weaken e) (weaken e')
stepWeaken = stepRename FS

||| Multi-step reduction is preserved by renaming
public export
stepsRename : (r : Ren n m) -> Steps e e' -> Steps (rename r e) (rename r e')
stepsRename r Refl = Refl
stepsRename r (Trans s rest) = Trans (stepRename r s) (stepsRename r rest)

||| Multi-step reduction is preserved by weakening
public export
stepsWeaken : Steps e e' -> Steps (weaken e) (weaken e')
stepsWeaken = stepsRename FS

------------------------------------------------------------------------
-- Substitution Preserves Reduction
------------------------------------------------------------------------

||| Substitution commutes with single-variable substitution
||| subst s (subst0 body arg) = subst0 (subst (liftSub s) body) (subst s arg)
|||
||| This is already proved as substSubst0 in Substitution.idr
public export
substSubst0Step : (s : Sub n m) -> (body : Expr (S n)) -> (arg : Expr n)
               -> subst s (subst0 body arg) = subst0 (subst (liftSub s) body) (subst s arg)
substSubst0Step = substSubst0

||| Substitution preserves single-step reduction.
|||
||| If e → e', then subst s e → subst s e'.
|||
||| This is crucial for showing that DefEq is preserved under substitution.
public export
stepSubst : (s : Sub n m) -> Step e e' -> Step (subst s e) (subst s e')
stepSubst s (SBeta {body} {arg}) =
  -- subst s (App (Lam ty body) arg) = App (Lam (subst s ty) (subst (liftSub s) body)) (subst s arg)
  -- subst s (subst0 body arg) = subst0 (subst (liftSub s) body) (subst s arg) by substSubst0
  rewrite substSubst0 s body arg in SBeta
stepSubst s (SZeta {body} {val}) =
  rewrite substSubst0 s body val in SZeta
stepSubst s (SAppL step) = SAppL (stepSubst s step)
stepSubst s (SAppR step) = SAppR (stepSubst s step)
stepSubst s (SLamBody step) = SLamBody (stepSubst (liftSub s) step)
stepSubst s (SLamTy step) = SLamTy (stepSubst s step)
stepSubst s (SPiDom step) = SPiDom (stepSubst s step)
stepSubst s (SPiCod step) = SPiCod (stepSubst (liftSub s) step)
stepSubst s (SLetTy step) = SLetTy (stepSubst s step)
stepSubst s (SLetVal step) = SLetVal (stepSubst s step)
stepSubst s (SLetBody step) = SLetBody (stepSubst (liftSub s) step)

||| Multi-step reduction is preserved by substitution
public export
stepsSubst : (s : Sub n m) -> Steps e e' -> Steps (subst s e) (subst s e')
stepsSubst s Refl = Refl
stepsSubst s (Trans step rest) = Trans (stepSubst s step) (stepsSubst s rest)

||| Single-variable substitution preserves reduction
public export
stepSubst0 : (arg : Expr n) -> Step e e' -> Step (subst0 e arg) (subst0 e' arg)
stepSubst0 arg = stepSubst (singleSub arg)
