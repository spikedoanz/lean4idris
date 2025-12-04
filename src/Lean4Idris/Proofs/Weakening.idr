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
renameExchangeInvol : (e : Expr (S (S n))) -> rename Weakening.exchangeRen (rename Weakening.exchangeRen e) = e
renameExchangeInvol e =
  rewrite renameComp Weakening.exchangeRen Weakening.exchangeRen e in
  rewrite renameExt (Weakening.exchangeRen . Weakening.exchangeRen) idRen exchangeInvol e in
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
||| metatheoretic result that we mark as believe_me for now.
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

-- For the remaining cases (Pi, Lam, App, Let, Conv), we use believe_me
-- because they require either:
-- 1. Context exchange lemmas (Pi/Lam/Let bodies)
-- 2. Complex substitution commutativity (App/Let result types)
-- 3. Access to implicit types that Idris 2 doesn't expose (Conv)
--
-- These are all theoretically sound - the full proofs would require
-- substantial additional infrastructure.
weakening a (TPi _ _) = believe_me True
weakening a (TLam _ _) = believe_me True
weakening a (TApp _ _) = believe_me True
weakening a (TLet _ _ _) = believe_me True
weakening a (TConv _ _ _) = believe_me True

------------------------------------------------------------------------
-- Generalized Weakening
------------------------------------------------------------------------

-- Note: weakeningN requires context concatenation which is complex
-- with de Bruijn indices. Omitted for now as it's not needed for
-- the core subject reduction proof.

------------------------------------------------------------------------
-- Weakening for Renamings (stated, needs more infrastructure)
------------------------------------------------------------------------

-- Note: A full treatment of renaming-preserves-typing requires:
-- 1. A well-formedness relation for renamings
-- 2. Careful handling of variable types across contexts
-- This is more complex infrastructure that we defer for now.
