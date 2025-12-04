||| Subject Reduction (Type Preservation)
|||
||| The main theorem: If Γ ⊢ e : T and e → e', then Γ ⊢ e' : T.
|||
||| This says that reduction preserves types. It's one of the two
||| key safety properties (the other being Progress).
|||
||| Together they imply: well-typed programs don't get stuck.
module Lean4Idris.Proofs.SubjectReduction

import Data.Fin
import Lean4Idris.Proofs.Syntax
import Lean4Idris.Proofs.Substitution
import Lean4Idris.Proofs.Typing
import Lean4Idris.Proofs.Reduction
import Lean4Idris.Proofs.Weakening
import Lean4Idris.Proofs.SubstitutionLemma
import Lean4Idris.Proofs.DefEq
import Lean4Idris.Proofs.CtxConversion

%default total

------------------------------------------------------------------------
-- Subject Reduction (Single Step)
------------------------------------------------------------------------

||| Type Preservation / Subject Reduction
|||
||| If Γ ⊢ e : T and e → e', then Γ ⊢ e' : T.
|||
||| Proof by induction on the reduction step.
public export
subjectReduction : {n : Nat} -> {ctx : Ctx n} -> {e : Expr n} -> {e' : Expr n} -> {ty : Expr n}
                -> HasType ctx e ty
                -> Step e e'
                -> HasType ctx e' ty

------------------------------------------------------------------------
-- β-reduction: (λx.b) a → b[x := a]
------------------------------------------------------------------------

-- The key case! When we have:
--   ctx ⊢ (λ(x:A). b) a : B[x := a]
-- And we reduce to:
--   b[x := a]
-- We need to show:
--   ctx ⊢ b[x := a] : B[x := a]
--
-- From TApp, we have:
--   fTyping : ctx ⊢ λ(x:A). b : (x:A) → B
--   argTyping : ctx ⊢ a : A
--
-- From TLam (inverting fTyping), we have:
--   tyWf : ctx ⊢ A : Type l
--   bodyTyping : ctx, x:A ⊢ b : B
--
-- By the substitution lemma:
--   ctx ⊢ b[x := a] : B[x := a]  ✓

-- Case when function is directly a TLam
subjectReduction (TApp l ty cod (Lam ty body) arg (TLam _ _ _ _ tyWf bodyTyping) argTyping codWf) SBeta =
  substitutionLemma bodyTyping argTyping

-- Case when function is typed via TConv (e.g., (Lam ..) : (converted Pi type))
-- This requires inversion through the conversion, which is complex
subjectReduction (TApp l dom cod (Lam ty body) arg (TConv _ _ _ _ fTyping eq tyWf2) argTyping codWf) SBeta =
  ?subjectReduction_SBeta_TConv_hole

------------------------------------------------------------------------
-- ζ-reduction: let x = v in e → e[x := v]
------------------------------------------------------------------------

-- Similar to β-reduction.
-- From TLet, we have:
--   tyWf : ctx ⊢ A : Type l
--   valTyping : ctx ⊢ v : A
--   bodyTyping : ctx, x:A ⊢ e : B
--
-- By substitution lemma:
--   ctx ⊢ e[x := v] : B[x := v]  ✓

subjectReduction (TLet l1 l2 ty val body bodyTy tyWf valTyping bodyTyping bodyTyWf) SZeta =
  substitutionLemma bodyTyping valTyping

------------------------------------------------------------------------
-- Congruence: reduce function in application
------------------------------------------------------------------------

-- If f → f' and ctx ⊢ f x : T, show ctx ⊢ f' x : T
--
-- From TApp:
--   fTyping : ctx ⊢ f : (x:A) → B
--   argTyping : ctx ⊢ x : A
--   T = B[x := arg]
--
-- By IH: ctx ⊢ f' : (x:A) → B
--   (Wait, this isn't quite right - we need f' to have the SAME type as f)
--   This requires that reduction preserves types, which is what we're proving!
--
-- Key insight: we need to show f and f' have the same type.
-- Since f : (x:A) → B and f → f', by IH, f' : (x:A) → B.
-- Then TApp gives us ctx ⊢ f' x : B[x := arg].

subjectReduction (TApp l dom cod f arg fTyping argTyping codWf) (SAppL fStep) =
  let fTyping' = subjectReduction fTyping fStep
  in TApp l dom cod _ arg fTyping' argTyping codWf

------------------------------------------------------------------------
-- Congruence: reduce argument in application
------------------------------------------------------------------------

-- If x → x' and ctx ⊢ f x : T, show ctx ⊢ f x' : T
--
-- This is trickier! The type T = B[x := arg], and if arg changes to arg',
-- we get B[x := arg'] which might be different!
--
-- But wait: by IH, arg' : A (same type as arg).
-- And the *declared* result type is B[x := arg].
-- After reduction, we have f x' where x' : A.
-- So f x' : B[x := x'].
--
-- We need: B[x := arg] = B[x := arg']
-- This is NOT generally true unless arg and arg' are definitionally equal!
--
-- Solution: we need the Conversion rule (TConv).
-- If arg and arg' are definitionally equal (arg ≡ arg'),
-- then B[x := arg] ≡ B[x := arg'], so we can convert.
--
-- For now, we use a hole - a full proof requires defining ≡.

-- SAppR uses the step arg -> arg' which we bind via {x'=arg'}
subjectReduction (TApp l dom cod f arg fTyping argTyping codWf) (SAppR {x'=arg'} argStep) =
  let argTyping' = subjectReduction argTyping argStep
      -- TApp fTyping argTyping' codWf : HasType ctx (App f arg') (subst0 cod arg')
      -- We need: HasType ctx (App f arg') (subst0 cod arg)
      -- Since arg → arg', we have DefEq arg arg' by DEStep
      -- Thus DefEq (subst0 cod arg') (subst0 cod arg) by DESym (defEqSubst0Arg ...)
      tyEq : DefEq (subst0 cod arg') (subst0 cod arg)
      tyEq = DESym (defEqSubst0Arg cod (DEStep argStep))
      appTyping : HasType ctx (App f arg') (subst0 cod arg')
      appTyping = TApp l dom cod f arg' fTyping argTyping' codWf
      -- Use typeOfType to get the well-typedness of subst0 cod arg
      -- We have codWf : HasType (Extend ctx dom) cod (Sort l)
      -- By substitution lemma with argTyping : HasType ctx arg dom
      -- We get: HasType ctx (subst0 cod arg) (Sort l)
      tyWf : HasType ctx (subst0 cod arg) (Sort l)
      tyWf = substitutionLemma codWf argTyping
  in TConv l (App f arg') (subst0 cod arg') (subst0 cod arg) appTyping tyEq tyWf

------------------------------------------------------------------------
-- Congruence: reduce in lambda body
------------------------------------------------------------------------

subjectReduction (TLam l ty body bodyTy tyWf bodyTyping) (SLamBody bodyStep) =
  let bodyTyping' = subjectReduction bodyTyping bodyStep
  in TLam l ty _ bodyTy tyWf bodyTyping'

------------------------------------------------------------------------
-- Congruence: reduce in lambda type annotation
------------------------------------------------------------------------

-- If A → A' and ctx ⊢ λ(x:A). b : (x:A) → B
-- Show ctx ⊢ λ(x:A'). b : (x:A) → B
--
-- Hmm, this also needs conversion: (x:A) → B ≡ (x:A') → B when A ≡ A'.

-- SLamTy case requires ctxConversion which has holes
-- Hole this out for now
subjectReduction (TLam l ty body bodyTy tyWf bodyTyping) (SLamTy tyStep) =
  ?subjectReduction_SLamTy_hole

------------------------------------------------------------------------
-- Congruence: reduce in Pi domain
------------------------------------------------------------------------

-- SPiDom case requires ctxConversion which has holes
-- Hole this out for now
subjectReduction (TPi l1 l2 dom cod domWf codWf) (SPiDom domStep) =
  ?subjectReduction_SPiDom_hole

------------------------------------------------------------------------
-- Congruence: reduce in Pi codomain
------------------------------------------------------------------------

subjectReduction (TPi l1 l2 dom cod domWf codWf) (SPiCod codStep) =
  let codWf' = subjectReduction codWf codStep
  in TPi l1 l2 dom _ domWf codWf'

------------------------------------------------------------------------
-- Congruence: reduce in let
------------------------------------------------------------------------

-- SLetTy case requires ctxConversion which has holes
-- Hole this out for now
subjectReduction (TLet l1 l2 ty val body bodyTy tyWf valTyping bodyTyping bodyTyWf) (SLetTy tyStep) =
  ?subjectReduction_SLetTy_hole

-- SLetVal uses the step val -> val' which we bind via {val'=val'}
subjectReduction (TLet l1 l2 ty val body bodyTy tyWf valTyping bodyTyping bodyTyWf) (SLetVal {val'=val'} valStep) =
  let valTyping' = subjectReduction valTyping valStep
      -- Result type is subst0 bodyTy val, but we get subst0 bodyTy val'
      -- These are DefEq since val ≡ val'
      tyEq : DefEq (subst0 bodyTy val') (subst0 bodyTy val)
      tyEq = DESym (defEqSubst0Arg bodyTy (DEStep valStep))
      letTyping : HasType ctx (Let ty val' body) (subst0 bodyTy val')
      letTyping = TLet l1 l2 ty val' body bodyTy tyWf valTyping' bodyTyping bodyTyWf
      -- Well-typedness of the result type
      -- bodyTyWf : HasType (Extend ctx ty) bodyTy (Sort l2)
      -- valTyping : HasType ctx val ty
      -- By substitution lemma: HasType ctx (subst0 bodyTy val) (Sort l2)
      resultTyWf : HasType ctx (subst0 bodyTy val) (Sort l2)
      resultTyWf = substitutionLemma bodyTyWf valTyping
  in TConv l2 (Let ty val' body) (subst0 bodyTy val') (subst0 bodyTy val) letTyping tyEq resultTyWf

subjectReduction (TLet l1 l2 ty val body bodyTy tyWf valTyping bodyTyping bodyTyWf) (SLetBody bodyStep) =
  let bodyTyping' = subjectReduction bodyTyping bodyStep
  in TLet l1 l2 ty val _ bodyTy tyWf valTyping bodyTyping' bodyTyWf

------------------------------------------------------------------------
-- Conversion cases
------------------------------------------------------------------------

subjectReduction (TConv l e ty1 ty2 eTyping eq tyWf) step =
  let eTyping' = subjectReduction eTyping step
  in TConv l _ ty1 ty2 eTyping' eq tyWf

------------------------------------------------------------------------
-- Multi-Step Subject Reduction
------------------------------------------------------------------------

||| Subject reduction extends to multiple steps.
|||
||| If Γ ⊢ e : T and e →* e', then Γ ⊢ e' : T.
|||
||| Note: The intermediate expression in Trans is not accessible in Idris 2.
||| We need a helper function that takes the intermediate expression explicitly.
public export
subjectReductionMulti : {n : Nat} -> {ctx : Ctx n} -> {e : Expr n} -> {e' : Expr n} -> {ty : Expr n}
                     -> HasType ctx e ty
                     -> Steps e e'
                     -> HasType ctx e' ty
subjectReductionMulti eTyping Refl = eTyping
subjectReductionMulti {n} {ctx} {e} {ty} eTyping (Trans step rest) =
  -- Idris 2 implicit accessibility issue: the intermediate expression from Trans
  -- is not accessible. We hole this out for now.
  ?subjectReductionMulti_Trans_hole

------------------------------------------------------------------------
-- What's Missing for a Complete Proof
------------------------------------------------------------------------

{-
The holes above require:

1. **Definitional Equality** (≡)
   - Define when two types are definitionally equal
   - Show reduction steps produce definitionally equal terms
   - e → e' implies e ≡ e'

2. **Conversion Compatibility**
   - If A ≡ A' and ctx ⊢ e : A, then ctx ⊢ e : A'
   - This is the TConv rule, but we need ≡ to use it

3. **Context Equivalence**
   - If A ≡ A', then (ctx, x:A) is equivalent to (ctx, x:A')
   - Derivations in one context can be converted to the other

4. **Substitution Respects Equality**
   - If A ≡ A', then B[x := A] ≡ B[x := A']

These form a coherent theory of definitional equality that
interacts well with the typing judgment. The lean4lean project
provides all of these.

For Lean specifically, definitional equality includes:
- α-equivalence (renaming bound variables)
- β-equivalence (function application)
- δ-equivalence (unfolding definitions)
- ι-equivalence (recursor computation)
- η-equivalence (function extensionality)
- Proof irrelevance (all proofs of a Prop are equal)
-}
