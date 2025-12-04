||| Weakening Lemma
|||
||| If Γ ⊢ e : T, then Γ, A ⊢ weaken(e) : weaken(T)
|||
||| This lemma says that adding a new variable to the context
||| doesn't break existing typing derivations - we just need to
||| shift all the variable indices.
|||
||| The proof strategy is to prove a more general "renaming preserves typing"
||| lemma and derive weakening as a special case.
module Lean4Idris.Proofs.Weakening

import Data.Fin
import Lean4Idris.Proofs.Syntax
import Lean4Idris.Proofs.Substitution
import Lean4Idris.Proofs.Environment
import Lean4Idris.Proofs.DefEq
import Lean4Idris.Proofs.Typing

%default total

------------------------------------------------------------------------
-- Weakening for Context Lookups
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
renameExchangeInvol : (e : Expr (S (S n))) -> rename Weakening.exchangeRen (rename Weakening.exchangeRen e) = e
renameExchangeInvol e =
  rewrite renameComp Weakening.exchangeRen Weakening.exchangeRen e in
  rewrite renameExt (Weakening.exchangeRen . Weakening.exchangeRen) idRen exchangeInvol e in
  renameId e

------------------------------------------------------------------------
-- Helper for Lifted Renaming Witness
------------------------------------------------------------------------

||| Helper to construct the lifted renaming witness.
||| If r is well-formed from ctx to ctx', then liftRen r is well-formed
||| from (Extend ctx ty) to (Extend ctx' (rename r ty)).
public export
liftRenWfHelper : {n : Nat} -> {m : Nat} -> {r : Ren n m} -> {ctx : Ctx n} -> {ctx' : Ctx m}
               -> {ty : Expr n}
               -> ((i : Fin n) -> lookupVar ctx' (r i) = rename r (lookupVar ctx i))
               -> (i : Fin (S n)) -> lookupVar (Extend ctx' (rename r ty)) (liftRen r i)
                                   = rename (liftRen r) (lookupVar (Extend ctx ty) i)
liftRenWfHelper {r} {ty} renWf FZ = sym (renameLiftWeaken r ty)
liftRenWfHelper {r} {ctx} renWf (FS i) = rewrite renWf i in sym (renameLiftWeaken r (lookupVar ctx i))

------------------------------------------------------------------------
-- The Core Theorem: Renaming Preserves Typing
------------------------------------------------------------------------

||| Renaming preserves typing, given a witness that variable types are preserved.
|||
||| If for each variable i in ctx, looking up (r i) in ctx' gives the
||| renamed type, and Σ; ctx ⊢ e : ty, then Σ; ctx' ⊢ rename r e : rename r ty.
|||
||| The witness function renWf provides: lookupVar ctx' (r i) = rename r (lookupVar ctx i)
public export
renamingPreservesTyping : {n : Nat} -> {m : Nat} -> {env : Env}
                       -> {r : Ren n m} -> {ctx : Ctx n} -> {ctx' : Ctx m}
                       -> {e : Expr n} -> {ty : Expr n}
                       -> (renWf : (i : Fin n) -> lookupVar ctx' (r i) = rename r (lookupVar ctx i))
                       -> HasType env ctx e ty
                       -> HasType env ctx' (rename r e) (rename r ty)

-- Variable case: use the well-formedness witness
renamingPreservesTyping {env} {r} {ctx} {ctx'} renWf (TVar i) =
  -- Goal: HasType env ctx' (Var (r i)) (rename r (lookupVar ctx i))
  -- TVar (r i) gives: HasType env ctx' (Var (r i)) (lookupVar ctx' (r i))
  -- By renWf: lookupVar ctx' (r i) = rename r (lookupVar ctx i)
  let tvarTyping : HasType env ctx' (Var (r i)) (lookupVar ctx' (r i))
      tvarTyping = TVar (r i)
  in rewrite sym (renWf i) in tvarTyping

-- Sort case: sorts don't contain variables (level is explicit now)
renamingPreservesTyping renWf (TSort l) = TSort l

-- Pi case: rename domain and codomain
renamingPreservesTyping {r} renWf (TPi l1 l2 dom cod domWf codWf) =
  let domWf' = renamingPreservesTyping renWf domWf
      codWf' = renamingPreservesTyping (liftRenWfHelper renWf) codWf
  in TPi l1 l2 (rename r dom) (rename (liftRen r) cod) domWf' codWf'

-- Lambda case: rename annotation and body
renamingPreservesTyping {r} renWf (TLam l ty body bodyTy tyWf bodyWf) =
  let tyWf' = renamingPreservesTyping renWf tyWf
      bodyWf' = renamingPreservesTyping (liftRenWfHelper renWf) bodyWf
  in TLam l (rename r ty) (rename (liftRen r) body) (rename (liftRen r) bodyTy) tyWf' bodyWf'

-- Application case: rename function and argument, use renameSubst0 for result type
renamingPreservesTyping {r} renWf (TApp l dom cod f arg fWf argWf codWf) =
  let fWf' = renamingPreservesTyping renWf fWf
      argWf' = renamingPreservesTyping renWf argWf
      -- codWf : HasType (Extend ctx dom) cod (Sort l)
      -- We need: HasType (Extend ctx' (rename r dom)) (rename (liftRen r) cod) (Sort l)
      codWf' = renamingPreservesTyping (liftRenWfHelper renWf) codWf
      -- Goal: HasType ctx' (App (rename r f) (rename r arg)) (rename r (subst0 cod arg))
      -- Have: TApp fWf' argWf' : HasType ctx' (App ...) (subst0 (rename (liftRen r) cod) (rename r arg))
      -- By renameSubst0: rename r (subst0 cod arg) = subst0 (rename (liftRen r) cod) (rename r arg)
      -- Rewrite goal: rename r (subst0 ...) --> subst0 (rename ...) ...
  in rewrite renameSubst0 r cod arg in
     TApp l (rename r dom) (rename (liftRen r) cod) (rename r f) (rename r arg) fWf' argWf' codWf'

-- Let case: similar to App
renamingPreservesTyping {r} renWf (TLet l1 l2 ty val body bodyTy tyWf valWf bodyWf bodyTyWf) =
  let tyWf' = renamingPreservesTyping renWf tyWf
      valWf' = renamingPreservesTyping renWf valWf
      bodyWf' = renamingPreservesTyping (liftRenWfHelper renWf) bodyWf
      bodyTyWf' = renamingPreservesTyping (liftRenWfHelper renWf) bodyTyWf
  in rewrite renameSubst0 r bodyTy val in
     TLet l1 l2 (rename r ty) (rename r val) (rename (liftRen r) body) (rename (liftRen r) bodyTy)
          tyWf' valWf' bodyWf' bodyTyWf'

-- Conversion case: rename both the term and type derivations
renamingPreservesTyping {r} renWf (TConv l e ty1 ty2 eWf eq tyWf) =
  let eWf' = renamingPreservesTyping renWf eWf
      tyWf' = renamingPreservesTyping renWf tyWf
      eq' = defEqRename r eq
  in TConv l (rename r e) (rename r ty1) (rename r ty2) eWf' eq' tyWf'

-- Const case: constants are closed, renaming doesn't change them
-- rename r (Const name levels) = Const name levels
-- rename r (weakenClosed ty) = weakenClosed ty (closed expressions are unchanged by renaming)
renamingPreservesTyping renWf (TConst name levels ty lookup) =
  -- Goal: HasType env ctx' (rename r (Const name levels)) (rename r (weakenClosed (instantiateLevels ty levels)))
  -- Since Const has no variables: rename r (Const name levels) = Const name levels
  -- Since instantiateLevels ty levels is closed: rename r (weakenClosed ...) = weakenClosed ...
  ?renamingPreservesTyping_TConst

------------------------------------------------------------------------
-- Shift Renaming Preserves Variable Types
------------------------------------------------------------------------

||| The shift renaming FS preserves variable types in the expected way.
|||
||| For any variable i in ctx, looking up (FS i) in (Extend ctx a)
||| gives weaken(lookupVar ctx i) = rename FS (lookupVar ctx i).
public export
shiftRenPreservesTypes : (ctx : Ctx n) -> (a : Expr n)
                      -> (i : Fin n) -> lookupVar (Extend ctx a) (FS i) = rename FS (lookupVar ctx i)
shiftRenPreservesTypes ctx a i =
  -- LHS: lookupVar (Extend ctx a) (FS i) = weaken (lookupVar ctx i)  by definition
  -- RHS: rename FS (lookupVar ctx i) = weaken (lookupVar ctx i)      since rename FS = weaken
  Refl

------------------------------------------------------------------------
-- The Weakening Lemma (Main Result)
------------------------------------------------------------------------

||| The weakening lemma: typing is preserved under context extension.
|||
||| If Σ; Γ ⊢ e : T, then Σ; Γ,x:A ⊢ weaken(e) : weaken(T)
|||
||| This is a special case of renamingPreservesTyping where the
||| renaming is the shift (FS).
public export
weakening : {n : Nat} -> {env : Env} -> {ctx : Ctx n} -> {e : Expr n} -> {ty : Expr n}
         -> (a : Expr n)
         -> HasType env ctx e ty
         -> HasType env (Extend ctx a) (weaken e) (weaken ty)
weakening {n} {ctx} a hasType = renamingPreservesTyping {n} {m = S n} (shiftRenPreservesTypes ctx a) hasType
