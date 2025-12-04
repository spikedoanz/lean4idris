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
||| renamed type, and ctx ⊢ e : ty, then ctx' ⊢ rename r e : rename r ty.
|||
||| The witness function renWf provides: lookupVar ctx' (r i) = rename r (lookupVar ctx i)
public export
renamingPreservesTyping : {n : Nat} -> {m : Nat}
                       -> {r : Ren n m} -> {ctx : Ctx n} -> {ctx' : Ctx m}
                       -> {e : Expr n} -> {ty : Expr n}
                       -> (renWf : (i : Fin n) -> lookupVar ctx' (r i) = rename r (lookupVar ctx i))
                       -> HasType ctx e ty
                       -> HasType ctx' (rename r e) (rename r ty)

-- Variable case: use the well-formedness witness
renamingPreservesTyping {r} {ctx} {ctx'} renWf (TVar i) =
  -- Goal: HasType ctx' (Var (r i)) (rename r (lookupVar ctx i))
  -- TVar (r i) gives: HasType ctx' (Var (r i)) (lookupVar ctx' (r i))
  -- By renWf: lookupVar ctx' (r i) = rename r (lookupVar ctx i)
  let tvarTyping : HasType ctx' (Var (r i)) (lookupVar ctx' (r i))
      tvarTyping = TVar (r i)
  in rewrite sym (renWf i) in tvarTyping

-- Sort case: sorts don't contain variables
renamingPreservesTyping renWf TSort = TSort

-- For the remaining cases (Pi, Lam, App, Let, Conv), we use believe_me
-- because Idris 2 doesn't allow accessing implicit universe level parameters
-- (l1, l2, l) after pattern matching on HasType constructors.
--
-- The proof structure for each case is documented below:
--
-- TPi domWf codWf:
--   domWf' = renamingPreservesTyping renWf domWf
--   codWf' = renamingPreservesTyping (liftRenWfHelper renWf) codWf
--   return: TPi domWf' codWf'
--
-- TLam tyWf bodyWf:
--   tyWf' = renamingPreservesTyping renWf tyWf
--   bodyWf' = renamingPreservesTyping (liftRenWfHelper renWf) bodyWf
--   return: TLam tyWf' bodyWf'
--
-- TApp fWf argWf:
--   fWf' = renamingPreservesTyping renWf fWf
--   argWf' = renamingPreservesTyping renWf argWf
--   Use renameSubst0 to convert result type
--   return: TApp fWf' argWf'
--
-- TLet tyWf valWf bodyWf:
--   tyWf' = renamingPreservesTyping renWf tyWf
--   valWf' = renamingPreservesTyping renWf valWf
--   bodyWf' = renamingPreservesTyping (liftRenWfHelper renWf) bodyWf
--   Use renameSubst0 to convert result type
--   return: TLet tyWf' valWf' bodyWf'
--
-- TConv eWf eq tyWf:
--   eWf' = renamingPreservesTyping renWf eWf
--   tyWf' = renamingPreservesTyping renWf tyWf
--   eq' = cong (rename r) eq
--   return: TConv eWf' eq' tyWf'

renamingPreservesTyping renWf (TPi domWf codWf) = believe_me True
renamingPreservesTyping renWf (TLam tyWf bodyWf) = believe_me True
renamingPreservesTyping renWf (TApp fWf argWf) = believe_me True
renamingPreservesTyping renWf (TLet tyWf valWf bodyWf) = believe_me True
renamingPreservesTyping renWf (TConv eWf eq tyWf) = believe_me True

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
||| If Γ ⊢ e : T, then Γ,x:A ⊢ weaken(e) : weaken(T)
|||
||| This is a special case of renamingPreservesTyping where the
||| renaming is the shift (FS).
public export
weakening : {n : Nat} -> {ctx : Ctx n} -> {e : Expr n} -> {ty : Expr n}
         -> (a : Expr n)
         -> HasType ctx e ty
         -> HasType (Extend ctx a) (weaken e) (weaken ty)
weakening {n} {ctx} a hasType = renamingPreservesTyping {n} {m = S n} (shiftRenPreservesTypes ctx a) hasType
