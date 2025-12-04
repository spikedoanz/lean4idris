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
import Lean4Idris.Proofs.DefEq
import Lean4Idris.Proofs.Typing
import Lean4Idris.Proofs.Weakening

%default total

------------------------------------------------------------------------
-- Well-Formed Substitutions (Functional Representation)
------------------------------------------------------------------------

||| A substitution is well-formed with respect to two contexts
||| if each variable maps to a term of the appropriate type.
|||
||| SubWf s ctx ctx' means:
||| For each i in ctx with type T, we have ctx' ⊢ s(i) : subst(s, T)
|||
||| We use a functional representation (like renaming) to enable
||| easy lifting in the inductive cases.
public export
0 SubWf : {n : Nat} -> {m : Nat} -> Sub n m -> Ctx n -> Ctx m -> Type
SubWf {n} s ctx ctx' = (i : Fin n) -> HasType ctx' (s i) (subst s (lookupVar ctx i))

------------------------------------------------------------------------
-- Lifted Substitution is Well-Formed
------------------------------------------------------------------------

||| Helper to construct the lifted substitution witness.
||| If s is well-formed from ctx to ctx', then liftSub s is well-formed
||| from (Extend ctx ty) to (Extend ctx' (subst s ty)).
|||
||| This is analogous to liftRenWfHelper in Weakening.idr.
public export
liftSubWfHelper : {n : Nat} -> {m : Nat} -> {s : Sub n m} -> {ctx : Ctx n} -> {ctx' : Ctx m}
               -> {ty : Expr n}
               -> SubWf s ctx ctx'
               -> (i : Fin (S n)) -> HasType (Extend ctx' (subst s ty)) (liftSub s i)
                                             (subst (liftSub s) (lookupVar (Extend ctx ty) i))
liftSubWfHelper {s} {ty} {ctx'} subWf FZ =
  -- Goal: HasType (Extend ctx' (subst s ty)) (Var FZ) (subst (liftSub s) (weaken ty))
  -- liftSub s FZ = Var FZ
  -- lookupVar (Extend ctx ty) FZ = weaken ty
  -- TVar FZ : HasType (Extend ctx' (subst s ty)) (Var FZ) (lookupVar (Extend ctx' (subst s ty)) FZ)
  --         = HasType (Extend ctx' (subst s ty)) (Var FZ) (weaken (subst s ty))
  -- By weakenSubst: subst (liftSub s) (weaken ty) = weaken (subst s ty)
  rewrite sym (weakenSubst s ty) in TVar FZ
liftSubWfHelper {s} {ctx} {ctx'} subWf (FS i) =
  -- Goal: HasType (Extend ctx' (subst s ty)) (liftSub s (FS i)) (subst (liftSub s) (lookupVar (Extend ctx ty) (FS i)))
  -- liftSub s (FS i) = weaken (s i)
  -- lookupVar (Extend ctx ty) (FS i) = weaken (lookupVar ctx i)
  -- By weakenSubst: subst (liftSub s) (weaken (lookupVar ctx i)) = weaken (subst s (lookupVar ctx i))
  -- So we need: HasType (Extend ctx' (subst s ty)) (weaken (s i)) (weaken (subst s (lookupVar ctx i)))
  -- This is weakening of: HasType ctx' (s i) (subst s (lookupVar ctx i))
  -- Which is exactly subWf i
  rewrite sym (weakenSubst s (lookupVar ctx i)) in
  weakening (subst s ty) (subWf i)

------------------------------------------------------------------------
-- Identity Substitution is Well-Formed
------------------------------------------------------------------------

||| The identity substitution is well-formed for any context
public export
idSubWf : (ctx : Ctx n) -> SubWf Substitution.idSub ctx ctx
idSubWf ctx i =
  -- idSub i = Var i
  -- subst idSub (lookupVar ctx i) = lookupVar ctx i   by substId
  -- So need: HasType ctx (Var i) (lookupVar ctx i)
  -- Which is exactly TVar i
  rewrite substId (lookupVar ctx i) in TVar i

------------------------------------------------------------------------
-- Single Substitution is Well-Formed
------------------------------------------------------------------------

||| If ctx ⊢ s : A, then singleSub(s) is well-formed from (ctx, A) to ctx
public export
singleSubWf : {ctx : Ctx n} -> {ty : Expr n} -> {s : Expr n}
           -> HasType ctx s ty
           -> SubWf (singleSub s) (Extend ctx ty) ctx
singleSubWf {ctx} {ty} {s} sTyping FZ =
  -- singleSub s FZ = s
  -- lookupVar (Extend ctx ty) FZ = weaken ty
  -- subst (singleSub s) (weaken ty) = ty  by weakenSubst0
  -- So need: HasType ctx s ty
  -- Which is exactly sTyping
  rewrite weakenSubst0 ty s in sTyping
singleSubWf {ctx} {ty} {s} sTyping (FS i) =
  -- singleSub s (FS i) = Var i
  -- lookupVar (Extend ctx ty) (FS i) = weaken (lookupVar ctx i)
  -- subst (singleSub s) (weaken (lookupVar ctx i)) = lookupVar ctx i  by weakenSubst0
  -- So need: HasType ctx (Var i) (lookupVar ctx i)
  -- Which is TVar i
  rewrite weakenSubst0 (lookupVar ctx i) s in TVar i

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
substitutionGeneral : {n : Nat} -> {m : Nat}
                   -> {s : Sub n m} -> {ctx : Ctx n} -> {ctx' : Ctx m}
                   -> {e : Expr n} -> {ty : Expr n}
                   -> SubWf s ctx ctx'
                   -> HasType ctx e ty
                   -> HasType ctx' (subst s e) (subst s ty)

-- Variable case: look up in the substitution
-- sWf i gives: HasType ctx' (s i) (subst s (lookupVar ctx i))
-- TVar i : HasType ctx (Var i) (lookupVar ctx i)
-- So subst s (Var i) = s i, subst s (lookupVar ctx i) already matches
substitutionGeneral sWf (TVar i) = sWf i

-- Sort case: sorts don't contain variables
substitutionGeneral sWf (TSort l) = TSort l

-- Pi case: substitute in domain and codomain
substitutionGeneral {s} sWf (TPi l1 l2 dom cod domWf codWf) =
  let domWf' = substitutionGeneral sWf domWf
      codWf' = substitutionGeneral (liftSubWfHelper sWf) codWf
  in TPi l1 l2 (subst s dom) (subst (liftSub s) cod) domWf' codWf'

-- Lambda case: similar to Pi
substitutionGeneral {s} sWf (TLam l ty body bodyTy tyWf bodyWf) =
  let tyWf' = substitutionGeneral sWf tyWf
      bodyWf' = substitutionGeneral (liftSubWfHelper sWf) bodyWf
  in TLam l (subst s ty) (subst (liftSub s) body) (subst (liftSub s) bodyTy) tyWf' bodyWf'

-- Application case: substitute in function and argument
substitutionGeneral {s} sWf (TApp l dom cod f arg fWf argWf codWf) =
  let fWf' = substitutionGeneral sWf fWf
      argWf' = substitutionGeneral sWf argWf
      codWf' = substitutionGeneral (liftSubWfHelper sWf) codWf
      -- fWf' : HasType ctx' (subst s f) (subst s (Pi dom cod)) = HasType ctx' (subst s f) (Pi (subst s dom) (subst (liftSub s) cod))
      -- argWf' : HasType ctx' (subst s arg) (subst s dom)
      -- TApp gives: HasType ctx' (App (subst s f) (subst s arg)) (subst0 (subst (liftSub s) cod) (subst s arg))
      -- Need: HasType ctx' (subst s (App f arg)) (subst s (subst0 cod arg))
      --     = HasType ctx' (App (subst s f) (subst s arg)) (subst s (subst0 cod arg))
      -- By substSubst0: subst s (subst0 cod arg) = subst0 (subst (liftSub s) cod) (subst s arg)
  in rewrite substSubst0 s cod arg in
     TApp l (subst s dom) (subst (liftSub s) cod) (subst s f) (subst s arg) fWf' argWf' codWf'

-- Let case: similar to App
substitutionGeneral {s} sWf (TLet l1 l2 ty val body bodyTy tyWf valWf bodyWf bodyTyWf) =
  let tyWf' = substitutionGeneral sWf tyWf
      valWf' = substitutionGeneral sWf valWf
      bodyWf' = substitutionGeneral (liftSubWfHelper sWf) bodyWf
      bodyTyWf' = substitutionGeneral (liftSubWfHelper sWf) bodyTyWf
  in rewrite substSubst0 s bodyTy val in
     TLet l1 l2 (subst s ty) (subst s val) (subst (liftSub s) body) (subst (liftSub s) bodyTy)
          tyWf' valWf' bodyWf' bodyTyWf'

-- Conversion case
substitutionGeneral {s} sWf (TConv l e ty1 ty2 eWf eq tyWf) =
  let eWf' = substitutionGeneral sWf eWf
      tyWf' = substitutionGeneral sWf tyWf
      eq' = defEqSubst s eq
  in TConv l (subst s e) (subst s ty1) (subst s ty2) eWf' eq' tyWf'

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
substitutionLemma : {n : Nat} -> {ctx : Ctx n} -> {ty : Expr n} -> {s : Expr n}
                 -> {e : Expr (S n)} -> {eTy : Expr (S n)}
                 -> HasType (Extend ctx ty) e eTy
                 -> HasType ctx s ty
                 -> HasType ctx (subst0 e s) (subst0 eTy s)
substitutionLemma {n} eTyping sTyping =
  substitutionGeneral {n = S n} {m = n} (singleSubWf sTyping) eTyping

------------------------------------------------------------------------
-- Corollaries
------------------------------------------------------------------------

||| Substitution preserves well-typed terms
||| (The type itself might change, but the result is still well-typed)
public export
substitutionPreservesWellTyped : {n : Nat} -> {ctx : Ctx n} -> {ty : Expr n} -> {eTy : Expr (S n)} -> {s : Expr n}
                               -> {e : Expr (S n)}
                               -> HasType (Extend ctx ty) e eTy
                               -> HasType ctx s ty
                               -> (ty' : Expr n ** HasType ctx (subst0 e s) ty')
substitutionPreservesWellTyped {n} {ty} {eTy} {s} eTyping sTyping =
  (subst0 eTy s ** substitutionLemma {n} {ty} eTyping sTyping)

------------------------------------------------------------------------
-- Key Helper Lemmas
------------------------------------------------------------------------

-- Note: Substitution composition is more complex than renaming composition.
-- s2 . s1 doesn't typecheck directly because s1 returns Expr, not Fin.
-- The proper notion is: (i : Fin n) -> subst s2 (s1 i)
-- Proving substSubst0 (for App/Let cases) requires this infrastructure.

||| Weakening and substitution commute
||| This is already proved in Substitution.idr as weakenSubst
public export
weakenSubstCommutes : (s : Sub n m) -> (e : Expr n)
                   -> weaken (subst s e) = subst (liftSub s) (weaken e)
weakenSubstCommutes = weakenSubst
