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
subjectReduction : {ctx : Ctx n} -> {e : Expr n} -> {e' : Expr n} -> {ty : Expr n}
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

subjectReduction (TApp (TLam tyWf bodyTyping) argTyping) SBeta =
  substitutionLemma bodyTyping argTyping

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

subjectReduction (TLet tyWf valTyping bodyTyping) SZeta =
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

subjectReduction (TApp fTyping argTyping) (SAppL fStep) =
  let fTyping' = subjectReduction fTyping fStep
  in TApp fTyping' argTyping

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

subjectReduction (TApp {dom} {cod} fTyping argTyping) (SAppR argStep) =
  let argTyping' = subjectReduction argTyping argStep
      -- TApp fTyping argTyping' : HasType ctx (App f arg') (subst0 cod arg')
      -- We need: HasType ctx (App f arg') (subst0 cod arg)
      -- Since arg → arg', we have DefEq arg arg' by DEStep
      -- Thus DefEq (subst0 cod arg) (subst0 cod arg') by defEqSubst0Arg
      tyEq : DefEq (subst0 cod arg') (subst0 cod arg)
      tyEq = DESym (defEqSubst0Arg cod (DEStep argStep))
      appTyping : HasType ctx (App f arg') (subst0 cod arg')
      appTyping = TApp fTyping argTyping'
  -- To use TConv, we need a proof that subst0 cod arg is well-typed.
  -- This requires the "type of type" lemma. For now we use a hole.
  in ?appR_needs_tyWf  -- TConv appTyping tyEq ?tyWf

------------------------------------------------------------------------
-- Congruence: reduce in lambda body
------------------------------------------------------------------------

subjectReduction (TLam tyWf bodyTyping) (SLamBody bodyStep) =
  let bodyTyping' = subjectReduction bodyTyping bodyStep
  in TLam tyWf bodyTyping'

------------------------------------------------------------------------
-- Congruence: reduce in lambda type annotation
------------------------------------------------------------------------

-- If A → A' and ctx ⊢ λ(x:A). b : (x:A) → B
-- Show ctx ⊢ λ(x:A'). b : (x:A) → B
--
-- Hmm, this also needs conversion: (x:A) → B ≡ (x:A') → B when A ≡ A'.

subjectReduction (TLam {ty} {ty'} {body} {bodyTy} tyWf bodyTyping) (SLamTy tyStep) =
  -- ty → ty', so TLam gives us Lam ty' body : Pi ty' bodyTy
  -- But we need: Lam ty' body : Pi ty bodyTy
  -- The result types Pi ty bodyTy and Pi ty' bodyTy are DefEq
  let tyWf' = subjectReduction tyWf tyStep
      -- We need bodyTyping' : HasType (Extend ctx ty') body bodyTy
      -- Currently we have bodyTyping : HasType (Extend ctx ty) body bodyTy
      -- The contexts are CtxEq since ty ≡ ty'
      ctxEq : CtxEq (Extend ctx ty) (Extend ctx ty')
      ctxEq = CEExtend (ctxEqRefl ctx) (DEStep tyStep)
      (bodyTy'' ** (bodyTyping', bodyTyEq)) = ctxConversion ctxEq bodyTyping
      -- Now we can form TLam with ty' in the annotation
      -- But the bodyTy might have changed... we need the original bodyTy
      -- This is getting complicated. Let's use a hole for now.
  in ?lamTy_hole

------------------------------------------------------------------------
-- Congruence: reduce in Pi domain
------------------------------------------------------------------------

subjectReduction (TPi {dom} {dom'} {cod} domWf codWf) (SPiDom domStep) =
  let domWf' = subjectReduction domWf domStep
      -- codWf : HasType (Extend ctx dom) cod (Sort l2)
      -- We need: HasType (Extend ctx dom') cod (Sort l2)
      ctxEq : CtxEq (Extend ctx dom) (Extend ctx dom')
      ctxEq = CEExtend (ctxEqRefl ctx) (DEStep domStep)
      (codTy' ** (codWf', codTyEq)) = ctxConversion ctxEq codWf
      -- codTy' should be Sort l2 (up to DefEq)
      -- But TPi requires exactly Sort l2
      -- Result type Sort (lmax l1 l2) is unchanged
  in ?piDom_hole

------------------------------------------------------------------------
-- Congruence: reduce in Pi codomain
------------------------------------------------------------------------

subjectReduction (TPi domWf codWf) (SPiCod codStep) =
  let codWf' = subjectReduction codWf codStep
  in TPi domWf codWf'

------------------------------------------------------------------------
-- Congruence: reduce in let
------------------------------------------------------------------------

subjectReduction (TLet {ty} {ty'} tyWf valTyping bodyTyping) (SLetTy tyStep) =
  let tyWf' = subjectReduction tyWf tyStep
      -- valTyping : HasType ctx val ty, but now type annotation is ty'
      -- bodyTyping : HasType (Extend ctx ty) body bodyTy
      -- Need context conversion for body
      ctxEq : CtxEq (Extend ctx ty) (Extend ctx ty')
      ctxEq = CEExtend (ctxEqRefl ctx) (DEStep tyStep)
      (bodyTy' ** (bodyTyping', bodyTyEq)) = ctxConversion ctxEq bodyTyping
      -- Also need to convert valTyping to ty'
      -- This requires TConv with ty ≡ ty'
  in ?letTy_hole

subjectReduction (TLet {val} {val'} {bodyTy} tyWf valTyping bodyTyping) (SLetVal valStep) =
  let valTyping' = subjectReduction valTyping valStep
      -- Result type is subst0 bodyTy val, but we get subst0 bodyTy val'
      -- These are DefEq since val ≡ val'
      tyEq : DefEq (subst0 bodyTy val') (subst0 bodyTy val)
      tyEq = DESym (defEqSubst0Arg bodyTy (DEStep valStep))
      letTyping : HasType ctx (Let ty val' body) (subst0 bodyTy val')
      letTyping = TLet tyWf valTyping' bodyTyping
  in ?letVal_hole  -- Need TConv with tyEq

subjectReduction (TLet tyWf valTyping bodyTyping) (SLetBody bodyStep) =
  let bodyTyping' = subjectReduction bodyTyping bodyStep
  in TLet tyWf valTyping bodyTyping'

------------------------------------------------------------------------
-- Conversion cases
------------------------------------------------------------------------

subjectReduction (TConv eTyping eq tyWf) step =
  let eTyping' = subjectReduction eTyping step
  in TConv eTyping' eq tyWf

------------------------------------------------------------------------
-- Multi-Step Subject Reduction
------------------------------------------------------------------------

||| Subject reduction extends to multiple steps.
|||
||| If Γ ⊢ e : T and e →* e', then Γ ⊢ e' : T.
public export
subjectReductionMulti : HasType ctx e ty
                     -> Steps e e'
                     -> HasType ctx e' ty
subjectReductionMulti eTyping Refl = eTyping
subjectReductionMulti eTyping (Trans step rest) =
  let eTyping' = subjectReduction eTyping step
  in subjectReductionMulti eTyping' rest

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
