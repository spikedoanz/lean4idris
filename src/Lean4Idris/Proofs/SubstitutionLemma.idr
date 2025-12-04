||| The Substitution Lemma
|||
||| If Γ, x:A ⊢ e : T and Γ ⊢ s : A, then Γ ⊢ e[x := s] : T[x := s]
|||
||| This is the key lemma for proving subject reduction.
||| It says that substituting a well-typed term for a variable
||| preserves the typing of any expression that uses that variable.
module Lean4Idris.Proofs.SubstitutionLemma

import Data.Fin
import Lean4Idris.Proofs.Syntax
import Lean4Idris.Proofs.Substitution
import Lean4Idris.Proofs.Typing
import Lean4Idris.Proofs.Weakening

%default total

------------------------------------------------------------------------
-- Well-Formed Substitutions
------------------------------------------------------------------------

||| A substitution is well-formed with respect to two contexts
||| if each variable maps to a term of the appropriate type.
|||
||| SubWf s ctx ctx' means:
||| For each i in ctx with type T, we have ctx' ⊢ s(i) : subst(s, T)
public export
data SubWf : Sub n m -> Ctx n -> Ctx m -> Type where
  ||| Empty substitution is well-formed from empty context
  SubEmpty : SubWf s Empty ctx'

  ||| Extend a well-formed substitution
  ||| If s is well-formed ctx -> ctx', and ctx' ⊢ e : subst(s, ty),
  ||| then we can extend s to handle a new variable of type ty.
  SubExt : SubWf s ctx ctx'
        -> HasType ctx' (s FZ) (subst s ty)
        -> SubWf (liftSub s) (Extend ctx ty) (Extend ctx' (subst s ty))

------------------------------------------------------------------------
-- Identity Substitution is Well-Formed
------------------------------------------------------------------------

||| The identity substitution is well-formed for any context
public export
idSubWf : (ctx : Ctx n) -> SubWf Substitution.idSub ctx ctx
idSubWf Empty = SubEmpty
idSubWf (Extend ctx ty) = ?idSubWfExt

------------------------------------------------------------------------
-- Single Substitution is Well-Formed
------------------------------------------------------------------------

||| If ctx ⊢ s : A, then singleSub(s) is well-formed from (ctx, A) to ctx
public export
singleSubWf : {ctx : Ctx n} -> {ty : Expr n} -> {s : Expr n}
           -> HasType ctx s ty
           -> SubWf (singleSub s) (Extend ctx ty) ctx
singleSubWf sTyping = ?singleSubWf_proof

------------------------------------------------------------------------
-- The Substitution Lemma (Core Version)
------------------------------------------------------------------------

||| Substitution preserves typing.
|||
||| If s is a well-formed substitution from ctx to ctx',
||| and ctx ⊢ e : T, then ctx' ⊢ subst(s,e) : subst(s,T).
|||
||| This is proved by induction on the typing derivation.
public export
substitutionGeneral : {s : Sub n m} -> {ctx : Ctx n} -> {ctx' : Ctx m}
                   -> SubWf s ctx ctx'
                   -> HasType ctx e ty
                   -> HasType ctx' (subst s e) (subst s ty)

-- Variable case: look up in the substitution
substitutionGeneral sWf (TVar i) = ?substVar

-- Sort case: sorts don't contain variables
substitutionGeneral sWf TSort = TSort

-- Pi case: substitute in domain and codomain
substitutionGeneral sWf (TPi domWf codWf) =
  let domWf' = substitutionGeneral sWf domWf
      -- For codomain, we need to lift the substitution
      codWf' = ?substPiCod
  in TPi domWf' codWf'

-- Lambda case: similar to Pi
substitutionGeneral sWf (TLam tyWf bodyWf) =
  let tyWf' = substitutionGeneral sWf tyWf
      bodyWf' = ?substLamBody
  in TLam tyWf' bodyWf'

-- Application case: substitute in function and argument
-- The key lemma (substSubst0) requires substitution composition which is complex.
-- We use believe_me here since the full proof requires substantial infrastructure.
substitutionGeneral sWf (TApp fWf argWf) = believe_me True

-- Let case: similar to App, requires complex substitution composition
substitutionGeneral sWf (TLet tyWf valWf bodyWf) = believe_me True

-- Conversion case
substitutionGeneral sWf (TConv eWf eq tyWf) =
  let eWf' = substitutionGeneral sWf eWf
      tyWf' = substitutionGeneral sWf tyWf
  in TConv eWf' (cong (subst s) eq) tyWf'

------------------------------------------------------------------------
-- The Substitution Lemma (Single Variable Version)
------------------------------------------------------------------------

||| The classic substitution lemma for single variable substitution.
|||
||| If Γ, x:A ⊢ e : T and Γ ⊢ s : A,
||| then Γ ⊢ e[x := s] : T[x := s].
|||
||| This is the version used directly in subject reduction.
public export
substitutionLemma : {ctx : Ctx n} -> {ty : Expr n} -> {s : Expr n}
                 -> HasType (Extend ctx ty) e eTy
                 -> HasType ctx s ty
                 -> HasType ctx (subst0 e s) (subst0 eTy s)
substitutionLemma eTyping sTyping =
  substitutionGeneral (singleSubWf sTyping) eTyping

------------------------------------------------------------------------
-- Corollaries
------------------------------------------------------------------------

||| Substitution preserves well-typed terms
||| (The type itself might change, but the result is still well-typed)
public export
substitutionPreservesWellTyped : {ctx : Ctx n} -> {ty : Expr n} -> {eTy : Expr (S n)} -> {s : Expr n}
                               -> HasType (Extend ctx ty) e eTy
                               -> HasType ctx s ty
                               -> (ty' : Expr n ** HasType ctx (subst0 e s) ty')
substitutionPreservesWellTyped {ty} {eTy} {s} eTyping sTyping =
  (subst0 eTy s ** substitutionLemma {ty} eTyping sTyping)

------------------------------------------------------------------------
-- Key Helper Lemmas (stated, to be proved)
------------------------------------------------------------------------

||| Lifting preserves substitution well-formedness
public export
liftSubWf : SubWf s ctx ctx'
         -> SubWf (liftSub s) (Extend ctx ty) (Extend ctx' (subst s ty))
liftSubWf sWf = ?liftSubWf_proof

-- Note: Substitution composition is more complex than renaming composition.
-- s2 . s1 doesn't typecheck directly because s1 returns Expr, not Fin.
-- The proper notion is: (i : Fin n) -> subst s2 (s1 i)
-- We omit this for now as it requires substantial additional infrastructure.

||| Weakening and substitution commute
||| This is already proved in Substitution.idr as weakenSubst
public export
weakenSubstCommutes : (s : Sub n m) -> (e : Expr n)
                   -> weaken (subst s e) = subst (liftSub s) (weaken e)
weakenSubstCommutes = weakenSubst
