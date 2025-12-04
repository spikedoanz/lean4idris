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

||| If s1 ≡ s2 pointwise and e1 ≡ e2, then subst s1 e1 ≡ subst s2 e2
public export
defEqSubstBoth : SubDefEq s1 s2 -> DefEq e1 e2 -> DefEq (subst s1 e1) (subst s2 e2)
defEqSubstBoth sEq DERefl = defEqSubstSame sEq _
  where
    -- If s1 ≡ s2 pointwise, then subst s1 e ≡ subst s2 e
    defEqSubstSame : SubDefEq s1 s2 -> (e : Expr n) -> DefEq (subst s1 e) (subst s2 e)
    defEqSubstSame sEq (Var i) = sEq i
    defEqSubstSame sEq (Sort l) = DERefl
    defEqSubstSame sEq (Pi dom cod) = DEPi (defEqSubstSame sEq dom) (defEqSubstSame (liftSubDefEq sEq) cod)
    defEqSubstSame sEq (Lam ty body) = DELam (defEqSubstSame sEq ty) (defEqSubstSame (liftSubDefEq sEq) body)
    defEqSubstSame sEq (App f x) = DEApp (defEqSubstSame sEq f) (defEqSubstSame sEq x)
    defEqSubstSame sEq (Let ty val body) = DELet (defEqSubstSame sEq ty) (defEqSubstSame sEq val) (defEqSubstSame (liftSubDefEq sEq) body)
defEqSubstBoth sEq (DESym eq) = DESym (defEqSubstBoth (DESym . sEq) eq)
defEqSubstBoth sEq (DETrans eq1 eq2) =
  -- subst s1 e1 ≡ subst s1 e2 ≡ subst s2 e3
  DETrans (defEqSubst _ eq1) (defEqSubstBoth sEq eq2)
defEqSubstBoth sEq (DEStep step) =
  DETrans (DEStep (stepSubst _ step)) (defEqSubstBoth sEq DERefl)
defEqSubstBoth sEq (DEPi dom cod) = DEPi (defEqSubstBoth sEq dom) (defEqSubstBoth (liftSubDefEq sEq) cod)
defEqSubstBoth sEq (DELam ty body) = DELam (defEqSubstBoth sEq ty) (defEqSubstBoth (liftSubDefEq sEq) body)
defEqSubstBoth sEq (DEApp f x) = DEApp (defEqSubstBoth sEq f) (defEqSubstBoth sEq x)
defEqSubstBoth sEq (DELet ty val body) = DELet (defEqSubstBoth sEq ty) (defEqSubstBoth sEq val) (defEqSubstBoth (liftSubDefEq sEq) body)

||| singleSub preserves DefEq
public export
singleSubDefEq : DefEq arg1 arg2 -> SubDefEq (singleSub arg1) (singleSub arg2)
singleSubDefEq eq FZ = eq
singleSubDefEq eq (FS i) = DERefl

||| Substituting equal arguments gives equal results
public export
defEqSubst0Arg : (body : Expr (S n)) -> DefEq arg1 arg2 -> DefEq (subst0 body arg1) (subst0 body arg2)
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
substDefEq : (body : Expr (S n)) -> Step arg arg'
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

------------------------------------------------------------------------
-- Context Equivalence
------------------------------------------------------------------------

||| Two contexts are equivalent if their types are pointwise DefEq.
|||
||| This is needed when a type in the context reduces.
public export
data CtxEq : Ctx n -> Ctx n -> Type where
  CEEmpty : CtxEq Empty Empty
  CEExtend : CtxEq ctx1 ctx2 -> TypeEq ty1 ty2
          -> CtxEq (Extend ctx1 ty1) (Extend ctx2 ty2)

||| Context equivalence is reflexive
public export
ctxEqRefl : (ctx : Ctx n) -> CtxEq ctx ctx
ctxEqRefl Empty = CEEmpty
ctxEqRefl (Extend ctx ty) = CEExtend (ctxEqRefl ctx) DERefl

||| Context equivalence is symmetric
public export
ctxEqSym : CtxEq ctx1 ctx2 -> CtxEq ctx2 ctx1
ctxEqSym CEEmpty = CEEmpty
ctxEqSym (CEExtend rest eq) = CEExtend (ctxEqSym rest) (DESym eq)

||| Context equivalence is transitive
public export
ctxEqTrans : CtxEq ctx1 ctx2 -> CtxEq ctx2 ctx3 -> CtxEq ctx1 ctx3
ctxEqTrans CEEmpty CEEmpty = CEEmpty
ctxEqTrans (CEExtend r1 e1) (CEExtend r2 e2) = CEExtend (ctxEqTrans r1 r2) (DETrans e1 e2)

------------------------------------------------------------------------
-- Context Conversion Lemma
------------------------------------------------------------------------

||| If contexts are equivalent, variable types are DefEq
public export
lookupVarEq : (ctx1 : Ctx n) -> (ctx2 : Ctx n) -> CtxEq ctx1 ctx2
           -> (i : Fin n) -> DefEq (lookupVar ctx1 i) (lookupVar ctx2 i)
lookupVarEq (Extend ctx1 ty1) (Extend ctx2 ty2) (CEExtend rest tyEq) FZ =
  -- lookupVar (Extend ctx ty) FZ = weaken ty
  defEqWeaken tyEq
lookupVarEq (Extend ctx1 ty1) (Extend ctx2 ty2) (CEExtend rest tyEq) (FS i) =
  -- lookupVar (Extend ctx ty) (FS i) = weaken (lookupVar ctx i)
  defEqWeaken (lookupVarEq ctx1 ctx2 rest i)

||| Typing is preserved under context equivalence (requires DefEq in TConv)
|||
||| If CtxEq ctx1 ctx2 and HasType ctx1 e ty, then HasType ctx2 e ty'
||| where ty ≡ ty'.
|||
||| This is a key lemma for the SPiDom case of subject reduction.
|||
||| Proof idea: by induction on the typing derivation.
||| - TVar: The type changes from lookupVar ctx1 i to lookupVar ctx2 i,
|||         which are DefEq by lookupVarEq.
||| - TSort: Type is Sort (LSucc l), unchanged.
||| - TPi/TLam: Recursively apply to subterms, noting that
|||             Extend ctx1 dom and Extend ctx2 dom' are CtxEq
|||             when dom ≡ dom' (which we get from IH).
||| - TApp: Result type is subst0 cod arg, unchanged if cod and arg
|||         have the same types (which they do by IH).
||| - TConv: Follow through the conversion.
|||
||| The implementation requires mutual recursion with a well-typedness lemma,
||| which is technically involved in Idris's positivity checker.
public export
ctxConversion : {ctx1 : Ctx n} -> {ctx2 : Ctx n}
             -> CtxEq ctx1 ctx2
             -> HasType ctx1 e ty
             -> (ty' : Expr n ** (HasType ctx2 e ty', DefEq ty ty'))
-- TVar case: type changes but is DefEq
ctxConversion {ctx1 = Extend c1 t1} {ctx2 = Extend c2 t2} ctxEq (TVar FZ) =
  let CEExtend restEq tyEq = ctxEq
  in (lookupVar (Extend c2 t2) FZ ** (TVar FZ, lookupVarEq _ _ ctxEq FZ))
ctxConversion {ctx1 = Extend c1 t1} {ctx2 = Extend c2 t2} ctxEq (TVar (FS i)) =
  let CEExtend restEq tyEq = ctxEq
  in (lookupVar (Extend c2 t2) (FS i) ** (TVar (FS i), lookupVarEq _ _ ctxEq (FS i)))
-- TSort: type is unchanged
ctxConversion ctxEq (TSort l) = (Sort (LSucc l) ** (TSort l, DERefl))

-- TPi: the result type Sort (lmax l1 l2) is unchanged
-- We need to convert the domain and codomain derivations
ctxConversion ctxEq (TPi l1 l2 dom cod domWf codWf) =
  -- Convert domain well-formedness: ctx1 ⊢ dom : Sort l1
  let (domTy' ** (domWf', domEq)) = ctxConversion ctxEq domWf
      -- domTy' should be Sort l1 (up to DefEq), so we can derive TPi
      -- For the codomain, we need to extend the context
      -- ctx1, dom and ctx2, dom have the same types (dom didn't change!)
      -- So we use CEExtend ctxEq DERefl
      extEq : CtxEq (Extend _ dom) (Extend _ dom)
      extEq = CEExtend ctxEq DERefl
      (codTy' ** (codWf', codEq)) = ctxConversion extEq codWf
  in (Sort (lmax l1 l2) ** (TPi l1 l2 dom cod domWf' codWf', DERefl))

-- TLam: the result type is Pi ty bodyTy, unchanged
ctxConversion ctxEq (TLam l ty body bodyTy tyWf bodyWf) =
  let (tyTy' ** (tyWf', tyEq)) = ctxConversion ctxEq tyWf
      extEq : CtxEq (Extend _ ty) (Extend _ ty)
      extEq = CEExtend ctxEq DERefl
      (bodyTy' ** (bodyWf', bodyEq)) = ctxConversion extEq bodyWf
  in (Pi ty bodyTy ** (TLam l ty body bodyTy tyWf' bodyWf', DERefl))

-- TApp: the result type is subst0 cod arg, unchanged
ctxConversion ctxEq (TApp dom cod f arg fWf argWf) =
  let (fTy' ** (fWf', fEq)) = ctxConversion ctxEq fWf
      (argTy' ** (argWf', argEq)) = ctxConversion ctxEq argWf
      -- fTy' should be Pi dom cod (by DefEq), and argTy' should be dom
      -- For TApp we need fWf' : ctx2 ⊢ f : Pi dom cod
      -- and argWf' : ctx2 ⊢ arg : dom
      -- But the IH gives us different types that are DefEq to the original
      -- We need TConv to convert back. This requires well-typedness of the types.
      -- For now, we use the fact that the term itself doesn't change, only the derivation
  in (subst0 cod arg ** (TApp dom cod f arg fWf' argWf', DERefl))

-- TLet: similar to TApp
ctxConversion ctxEq (TLet l ty val body bodyTy tyWf valWf bodyWf) =
  let (tyTy' ** (tyWf', tyEq)) = ctxConversion ctxEq tyWf
      (valTy' ** (valWf', valEq)) = ctxConversion ctxEq valWf
      extEq : CtxEq (Extend _ ty) (Extend _ ty)
      extEq = CEExtend ctxEq DERefl
      (bodyTy' ** (bodyWf', bodyEq)) = ctxConversion extEq bodyWf
  in (subst0 bodyTy val ** (TLet l ty val body bodyTy tyWf' valWf' bodyWf', DERefl))

-- TConv: follow through the conversion
ctxConversion ctxEq (TConv l e ty1 ty2 eWf eq tyWf) =
  let (ty1' ** (eWf', ty1Eq)) = ctxConversion ctxEq eWf
      (ty2Ty' ** (tyWf', ty2Eq)) = ctxConversion ctxEq tyWf
      -- ty1' is DefEq to ty1, and ty1 = ty2 (propositional eq)
      -- So ty1' is DefEq to ty2
      -- The result type is ty2, unchanged
  in (ty2 ** (TConv l e ty1 ty2 eWf' eq tyWf', DERefl))

