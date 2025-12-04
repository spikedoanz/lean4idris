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
-- Core Weakening Lemma
------------------------------------------------------------------------

||| The weakening lemma: typing is preserved under context extension.
|||
||| If Γ ⊢ e : T, then Γ,x:A ⊢ weaken(e) : weaken(T)
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
-- Plus a lemma about how weakening interacts with context extension
weakening a (TPi domWf codWf) =
  let domWf' = weakening a domWf
      -- For codomain, we need to weaken in the extended context
      -- ctx, dom ⊢ cod : Sort l2
      -- becomes
      -- ctx, a, weaken(dom) ⊢ weaken(cod) : Sort l2
      -- This requires a context swap lemma
      codWf' = ?weakenPiCod
  in TPi domWf' codWf'

-- Lambda case: similar to Pi
weakening a (TLam tyWf bodyWf) =
  let tyWf' = weakening a tyWf
      bodyWf' = ?weakenLamBody
  in TLam tyWf' bodyWf'

-- Application case: straightforward recursion
-- Plus a lemma: weaken(subst0 cod arg) = subst0 (weaken cod) (weaken arg)
weakening a (TApp fWf argWf) =
  let fWf' = weakening a fWf
      argWf' = weakening a argWf
  in rewrite weakenSubst0Comm cod arg a in TApp fWf' argWf'
  where
    -- Weakening commutes with substitution
    weakenSubst0Comm : (cod : Expr (S n)) -> (arg : Expr n) -> (a : Expr n)
                    -> weaken (subst0 cod arg) = subst0 (weaken cod) (weaken arg)
    weakenSubst0Comm cod arg a = ?weakenSubst0Comm_proof

-- Let case
weakening a (TLet tyWf valWf bodyWf) =
  let tyWf' = weakening a tyWf
      valWf' = weakening a valWf
      bodyWf' = ?weakenLetBody
  in rewrite ?weakenLetSubst in TLet tyWf' valWf' bodyWf'

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
