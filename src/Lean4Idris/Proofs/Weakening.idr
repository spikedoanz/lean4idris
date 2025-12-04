||| Weakening Lemma
|||
||| If Γ ⊢ e : T, then Γ, A ⊢ weaken(e) : weaken(T)
|||
||| This lemma says that adding a new variable to the context
||| doesn't break existing typing derivations - we just need to
||| shift all the variable indices.
module Lean4Idris.Proofs.Weakening

import Data.Fin
import Lean4Idris.Proofs.Syntax
import Lean4Idris.Proofs.Substitution
import Lean4Idris.Proofs.Typing

%default total

------------------------------------------------------------------------
-- Weakening for Contexts
------------------------------------------------------------------------

||| Weaken a context lookup
|||
||| If variable i has type T in ctx, then variable (FS i) has type
||| weaken(T) in (Extend ctx A).
public export
weakenLookup : (ctx : Ctx n) -> (i : Fin n) -> (a : Expr n)
            -> lookupVar (Extend ctx a) (FS i) = weaken (lookupVar ctx i)
weakenLookup ctx i a = Refl

------------------------------------------------------------------------
-- Context Exchange
------------------------------------------------------------------------

||| The exchange renaming: swaps the two most recently bound variables
||| Maps: 0 -> 1, 1 -> 0, n+2 -> n+2
public export
exchangeRen : Ren (S (S n)) (S (S n))
exchangeRen FZ = FS FZ            -- 0 -> 1
exchangeRen (FS FZ) = FZ          -- 1 -> 0
exchangeRen (FS (FS i)) = FS (FS i)  -- n+2 -> n+2

||| Exchange is self-inverse
public export
exchangeInvol : (i : Fin (S (S n))) -> exchangeRen (exchangeRen i) = i
exchangeInvol FZ = Refl
exchangeInvol (FS FZ) = Refl
exchangeInvol (FS (FS i)) = Refl

||| rename exchangeRen is involutive on expressions
public export
renameExchangeInvol : (e : Expr (S (S n))) -> rename exchangeRen (rename exchangeRen e) = e
renameExchangeInvol e =
  rewrite renameComp exchangeRen exchangeRen e in
  rewrite renameExt (exchangeRen . exchangeRen) idRen exchangeInvol e in
  renameId e

------------------------------------------------------------------------
-- Core Weakening Lemma
------------------------------------------------------------------------

||| The weakening lemma: typing is preserved under context extension.
|||
||| If Γ ⊢ e : T, then Γ,x:A ⊢ weaken(e) : weaken(T)
|||
||| Note: The Pi/Lam/Let cases require context exchange, which requires
||| proving that rename exchangeRen preserves typing. This is a non-trivial
||| metatheoretic result that we leave as holes for now.
|||
||| Proof: by induction on the typing derivation.
public export
weakening : {ctx : Ctx n} -> {e : Expr n} -> {ty : Expr n}
         -> (a : Expr n)
         -> HasType ctx e ty
         -> HasType (Extend ctx a) (weaken e) (weaken ty)

-- Variable case: Var i has type lookupVar ctx i
-- After weakening: Var (FS i) has type weaken(lookupVar ctx i)
-- We need: lookupVar (Extend ctx a) (FS i) = weaken (lookupVar ctx i)
-- This holds by definition of lookupVar.
weakening a (TVar i) = rewrite sym (weakenLookup ctx i a) in TVar (FS i)

-- Sort case: Type l has type Type (l+1)
-- After weakening: weaken(Type l) = Type l (sorts don't contain variables)
--                  weaken(Type (l+1)) = Type (l+1)
weakening a TSort = TSort

-- Pi case: needs weakening of both domain and codomain derivations
-- Given: ctx ⊢ dom : Sort l1, and ctx,dom ⊢ cod : Sort l2
-- Need: ctx,a ⊢ weaken(dom) : Sort l1, and ctx,a,weaken(dom) ⊢ weaken(cod) : Sort l2
--
-- For the codomain, we use:
-- 1. weakening: ctx,dom,weaken(a) ⊢ weaken(cod) : Sort l2
-- 2. exchange: rename swap gives ctx,weaken(a),weaken(dom) ⊢ ... : Sort l2
-- 3. But weaken(a) in ctx,dom has an extra shift, so ctx,a,weaken(dom) after accounting for this
weakening a (TPi domWf codWf) =
  let domWf' = weakening a domWf
      codWf' = ?weakenPiCod  -- requires exchange lemma
  in TPi domWf' codWf'

-- Lambda case: similar to Pi, requires context exchange
weakening a (TLam tyWf bodyWf) =
  let tyWf' = weakening a tyWf
      bodyWf' = ?weakenLamBody  -- requires exchange lemma
  in TLam tyWf' bodyWf'

-- Application case: straightforward recursion
-- Plus a lemma: weaken(subst0 cod arg) = subst0 (weaken cod) (weaken arg)
weakening a (TApp fWf argWf) =
  let fWf' = weakening a fWf
      argWf' = weakening a argWf
  in rewrite weakenSubst0Comm cod arg in TApp fWf' argWf'
  where
    -- Weakening commutes with single-variable substitution
    -- weaken (subst0 cod arg) = subst0 (weaken cod) (weaken arg)
    --
    -- Proof:
    -- weaken (subst (singleSub arg) cod)
    --   = rename FS (subst (singleSub arg) cod)
    --   = subst (rename FS . singleSub arg) cod          by renameSubst
    --   = subst (liftSub (singleSub (weaken arg)) . FS) cod  (need to show these equal)
    --   = subst (liftSub (singleSub (weaken arg))) (rename FS cod)  by substRename (backwards)
    --   = subst (liftSub (singleSub (weaken arg))) (weaken cod)
    --
    -- The key is showing: rename FS . singleSub arg = liftSub (singleSub (weaken arg)) . FS
    weakenSubst0Comm : (cod : Expr (S n)) -> (arg : Expr n)
                    -> weaken (subst0 cod arg) = subst0 (weaken cod) (weaken arg)
    weakenSubst0Comm cod arg =
      rewrite renameSubst (singleSub arg) FS cod in
      rewrite sym (substRename FS (liftSub (singleSub (weaken arg))) cod) in
      rewrite substExt (rename FS . singleSub arg) (liftSub (singleSub (weaken arg)) . FS) extPf cod in
      Refl
      where
        extPf : (i : Fin (S n)) -> (rename FS . singleSub arg) i = (liftSub (singleSub (weaken arg)) . FS) i
        extPf FZ = Refl  -- rename FS arg = weaken arg = liftSub (singleSub (weaken arg)) (FS FZ)
        extPf (FS j) = Refl  -- rename FS (Var j) = Var (FS j) = liftSub ... (FS (FS j))

-- Let case: similar to Pi/Lam, requires exchange for body
-- Plus: result type involves subst0, need weakenSubst0Comm
weakening a (TLet tyWf valWf bodyWf) =
  let tyWf' = weakening a tyWf
      valWf' = weakening a valWf
      bodyWf' = ?weakenLetBody  -- requires exchange lemma
  in rewrite weakenSubst0Comm bodyTy val in TLet tyWf' valWf' bodyWf'
  where
    weakenSubst0Comm : (bodyTy : Expr (S n)) -> (val : Expr n)
                    -> weaken (subst0 bodyTy val) = subst0 (weaken bodyTy) (weaken val)
    weakenSubst0Comm bodyTy val =
      rewrite renameSubst (singleSub val) FS bodyTy in
      rewrite sym (substRename FS (liftSub (singleSub (weaken val))) bodyTy) in
      rewrite substExt (rename FS . singleSub val) (liftSub (singleSub (weaken val)) . FS) extPf bodyTy in
      Refl
      where
        extPf : (i : Fin (S n)) -> (rename FS . singleSub val) i = (liftSub (singleSub (weaken val)) . FS) i
        extPf FZ = Refl
        extPf (FS j) = Refl

-- Conversion case
weakening a (TConv eWf eq tyWf) =
  let eWf' = weakening a eWf
      tyWf' = weakening a tyWf
  in TConv eWf' (cong weaken eq) tyWf'

------------------------------------------------------------------------
-- Generalized Weakening
------------------------------------------------------------------------

||| Weaken by multiple variables
public export
weakeningN : {ctx : Ctx n}
          -> (ext : Ctx m)  -- Extension context
          -> HasType ctx e ty
          -> HasType (ctx ++ ext) (weakenN m e) (weakenN m ty)
weakeningN Empty deriv = deriv
weakeningN (Extend ext a) deriv =
  weakening (weakenN _ a) (weakeningN ext deriv)

------------------------------------------------------------------------
-- Weakening for Renamings
------------------------------------------------------------------------

||| A renaming preserves typing if it maps each variable to a
||| variable of the same type (appropriately weakened).
|||
||| This is a generalization of weakening.
public export
data RenWf : Ren n m -> Ctx n -> Ctx m -> Type where
  RenEmpty : RenWf r Empty ctx'
  RenExt : RenWf r ctx ctx'
        -> HasType ctx' (Var (r FZ)) (rename r (lookupVar (Extend ctx ty) FZ))
        -> RenWf (liftRen r) (Extend ctx ty) (Extend ctx' (rename r ty))

||| Renaming preserves typing
public export
renamingTyping : {r : Ren n m} -> {ctx : Ctx n} -> {ctx' : Ctx m}
              -> RenWf r ctx ctx'
              -> HasType ctx e ty
              -> HasType ctx' (rename r e) (rename r ty)
renamingTyping rWf (TVar i) = ?renameVar
renamingTyping rWf TSort = TSort
renamingTyping rWf (TPi domWf codWf) = ?renamePi
renamingTyping rWf (TLam tyWf bodyWf) = ?renameLam
renamingTyping rWf (TApp fWf argWf) =
  let fWf' = renamingTyping rWf fWf
      argWf' = renamingTyping rWf argWf
  in ?renameApp
renamingTyping rWf (TLet tyWf valWf bodyWf) = ?renameLet
renamingTyping rWf (TConv eWf eq tyWf) =
  TConv (renamingTyping rWf eWf) (cong (rename r) eq) (renamingTyping rWf tyWf)
