||| Context Equivalence and Conversion
|||
||| This module defines context equivalence (pointwise DefEq)
||| and the context conversion lemma (typing preserved under equivalent contexts).
|||
||| Separated from DefEq to break circular dependency with Typing.
module Lean4Idris.Proofs.CtxConversion

import Data.Fin
import Lean4Idris.Proofs.Syntax
import Lean4Idris.Proofs.Substitution
import Lean4Idris.Proofs.Reduction
import Lean4Idris.Proofs.DefEq
import Lean4Idris.Proofs.Typing

%default total

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
-- The context conversion preserves the type derivations
-- Full proof requires TConv to convert back to exact types when they're only DefEq
-- We hole this out for now as the full proof is complex
ctxConversion ctxEq (TPi l1 l2 dom cod domWf codWf) = ?ctxConversion_TPi_hole

-- TLam: the result type is Pi ty bodyTy, unchanged
ctxConversion ctxEq (TLam l ty body bodyTy tyWf bodyWf) = ?ctxConversion_TLam_hole

-- TApp: the result type is subst0 cod arg, unchanged
ctxConversion ctxEq (TApp l dom cod f arg fWf argWf codWf) = ?ctxConversion_TApp_hole

-- TLet: similar to TApp
ctxConversion ctxEq (TLet l1 l2 ty val body bodyTy tyWf valWf bodyWf bodyTyWf) = ?ctxConversion_TLet_hole

-- TConv: follow through the conversion
-- Full proof requires careful handling of the DefEq changes
ctxConversion ctxEq (TConv l e ty1 ty2 eWf eq tyWf) = ?ctxConversion_TConv_hole
