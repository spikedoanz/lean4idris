||| Typing Judgment for Dependent Type Theory
|||
||| This module defines the typing rules as an inductive type.
||| A value of type `HasType ctx e ty` is a proof that
||| expression `e` has type `ty` in context `ctx`.
module Lean4Idris.Proofs.Typing

import Data.Fin
import Data.Vect
import Lean4Idris.Proofs.Syntax
import Lean4Idris.Proofs.Substitution

%default total

------------------------------------------------------------------------
-- Typing Contexts
------------------------------------------------------------------------

||| A typing context maps each variable in scope to its type.
|||
||| For n variables in scope, we have n types.
||| The type at index i is the type of variable i (de Bruijn index).
|||
||| Note: types in the context are themselves expressions that may
||| reference earlier variables. Context entry i has type `Expr i`
||| because it can only reference variables 0..(i-1).
public export
data Ctx : Nat -> Type where
  ||| Empty context (no variables in scope)
  Empty : Ctx 0
  ||| Extend context with a new variable of given type
  ||| The type is an expression in the current context
  Extend : Ctx n -> Expr n -> Ctx (S n)

||| Look up the type of a variable in the context.
|||
||| The returned type is weakened to be valid in the full context.
||| If variable i has type A in the original position, we need to
||| weaken A by (n - i - 1) to make it valid at position n.
public export
lookupVar : (ctx : Ctx n) -> (i : Fin n) -> Expr n
lookupVar (Extend ctx ty) FZ = weaken ty
lookupVar (Extend ctx ty) (FS i) = weaken (lookupVar ctx i)

------------------------------------------------------------------------
-- Typing Judgment
------------------------------------------------------------------------

||| Typing judgment: Γ ⊢ e : T
|||
||| This is the core of the type system. Each constructor corresponds
||| to a typing rule from the literature.
|||
||| `HasType ctx e ty` is a proof that in context `ctx`,
||| expression `e` has type `ty`.
public export
data HasType : Ctx n -> Expr n -> Expr n -> Type where

  ||| Variable rule (Var)
  |||
  |||   x : A ∈ Γ
  ||| ─────────────
  |||   Γ ⊢ x : A
  |||
  ||| If variable i has type A in the context, then Var i has type A.
  TVar : (i : Fin n)
      -> HasType ctx (Var i) (lookupVar ctx i)

  ||| Sort rule (Type-in-Type, simplified)
  |||
  ||| ───────────────────────
  |||   Γ ⊢ Type l : Type (l+1)
  |||
  ||| Each universe is typed by the next universe.
  ||| (A proper treatment would track universe consistency.)
  TSort : HasType ctx (Sort l) (Sort (LSucc l))

  ||| Pi formation rule (Pi-F)
  |||
  |||   Γ ⊢ A : Type l₁    Γ, x:A ⊢ B : Type l₂
  ||| ───────────────────────────────────────────
  |||   Γ ⊢ (x : A) → B : Type (max l₁ l₂)
  |||
  ||| To form a Pi type, the domain must be a type and the codomain
  ||| must be a type in the extended context.
  TPi : HasType ctx dom (Sort l1)
     -> HasType (Extend ctx dom) cod (Sort l2)
     -> HasType ctx (Pi dom cod) (Sort (lmax l1 l2))

  ||| Lambda introduction rule (Lam-I)
  |||
  |||   Γ ⊢ A : Type l    Γ, x:A ⊢ e : B
  ||| ─────────────────────────────────────
  |||   Γ ⊢ λ(x:A). e : (x : A) → B
  |||
  ||| A lambda has a Pi type. The body is typed in the extended context.
  TLam : HasType ctx ty (Sort l)
      -> HasType (Extend ctx ty) body bodyTy
      -> HasType ctx (Lam ty body) (Pi ty bodyTy)

  ||| Application rule (App)
  |||
  |||   Γ ⊢ f : (x : A) → B    Γ ⊢ a : A
  ||| ─────────────────────────────────────
  |||   Γ ⊢ f a : B[x := a]
  |||
  ||| Applying a function to an argument substitutes the argument
  ||| into the codomain type.
  TApp : HasType ctx f (Pi dom cod)
      -> HasType ctx arg dom
      -> HasType ctx (App f arg) (subst0 cod arg)

  ||| Let rule (Let)
  |||
  |||   Γ ⊢ A : Type l    Γ ⊢ v : A    Γ, x:A ⊢ e : B
  ||| ──────────────────────────────────────────────────
  |||   Γ ⊢ let x : A = v in e : B[x := v]
  |||
  ||| Let bindings have types that account for the substitution.
  TLet : HasType ctx ty (Sort l)
      -> HasType ctx val ty
      -> HasType (Extend ctx ty) body bodyTy
      -> HasType ctx (Let ty val body) (subst0 bodyTy val)

  ||| Conversion rule (Conv)
  |||
  |||   Γ ⊢ e : A    A ≡ B    Γ ⊢ B : Type l
  ||| ─────────────────────────────────────────
  |||   Γ ⊢ e : B
  |||
  ||| If two types are definitionally equal, we can convert between them.
  ||| Note: DefEq is defined in a separate module to avoid circularity.
  TConv : HasType ctx e ty1
       -> ty1 = ty2  -- Simplified: using propositional equality
       -> HasType ctx ty2 (Sort l)
       -> HasType ctx e ty2

------------------------------------------------------------------------
-- HasType View (exposes implicit parameters)
------------------------------------------------------------------------

||| A view on HasType that makes all implicit parameters accessible.
|||
||| This is needed because Idris 2 doesn't allow accessing implicit
||| parameters after pattern matching. The view pattern exposes them
||| as explicit fields.
public export
data HasTypeView : {ctx : Ctx n} -> {e : Expr n} -> {ty : Expr n}
                -> HasType ctx e ty -> Type where
  ||| View of TVar
  VTVar : {ctx : Ctx n} -> (i : Fin n)
       -> HasTypeView {ctx} {e = Var i} {ty = lookupVar ctx i} (TVar i)

  ||| View of TSort
  VTSort : {ctx : Ctx n} -> {l : Level}
        -> HasTypeView {ctx} {e = Sort l} {ty = Sort (LSucc l)} TSort

  ||| View of TPi - exposes l1 and l2
  VTPi : {ctx : Ctx n} -> {dom : Expr n} -> {cod : Expr (S n)}
      -> {l1 : Level} -> {l2 : Level}
      -> (domWf : HasType ctx dom (Sort l1))
      -> (codWf : HasType (Extend ctx dom) cod (Sort l2))
      -> HasTypeView {ctx} {e = Pi dom cod} {ty = Sort (lmax l1 l2)} (TPi domWf codWf)

  ||| View of TLam - exposes l
  VTLam : {ctx : Ctx n} -> {ty : Expr n} -> {body : Expr (S n)} -> {bodyTy : Expr (S n)}
       -> {l : Level}
       -> (tyWf : HasType ctx ty (Sort l))
       -> (bodyWf : HasType (Extend ctx ty) body bodyTy)
       -> HasTypeView {ctx} {e = Lam ty body} {ty = Pi ty bodyTy} (TLam tyWf bodyWf)

  ||| View of TApp - exposes dom and cod
  VTApp : {ctx : Ctx n} -> {f : Expr n} -> {arg : Expr n}
       -> {dom : Expr n} -> {cod : Expr (S n)}
       -> (fWf : HasType ctx f (Pi dom cod))
       -> (argWf : HasType ctx arg dom)
       -> HasTypeView {ctx} {e = App f arg} {ty = subst0 cod arg} (TApp fWf argWf)

  ||| View of TLet - exposes l
  VTLet : {ctx : Ctx n} -> {ty : Expr n} -> {val : Expr n}
       -> {body : Expr (S n)} -> {bodyTy : Expr (S n)}
       -> {l : Level}
       -> (tyWf : HasType ctx ty (Sort l))
       -> (valWf : HasType ctx val ty)
       -> (bodyWf : HasType (Extend ctx ty) body bodyTy)
       -> HasTypeView {ctx} {e = Let ty val body} {ty = subst0 bodyTy val} (TLet tyWf valWf bodyWf)

  ||| View of TConv - exposes ty1, ty2, l
  VTConv : {ctx : Ctx n} -> {e : Expr n} -> {ty1 : Expr n} -> {ty2 : Expr n}
        -> {l : Level}
        -> (eWf : HasType ctx e ty1)
        -> (eq : ty1 = ty2)
        -> (ty2Wf : HasType ctx ty2 (Sort l))
        -> HasTypeView {ctx} {e} {ty = ty2} (TConv eWf eq ty2Wf)

-- Note: Due to Idris 2's limitation that implicit parameters are not accessible
-- after pattern matching, we cannot directly construct views or eliminators
-- that expose these parameters. The HasTypeView type above documents what
-- *should* be possible, but viewHasType cannot be implemented.
--
-- Workarounds in client code:
-- 1. Use `with` clauses to pattern match on expression structure first
-- 2. Use believe_me for cases where the proof structure is sound but
--    the universe levels can't be accessed
-- 3. Redesign HasType to make universe levels explicit indices (major refactor)

------------------------------------------------------------------------
-- Basic Properties
------------------------------------------------------------------------

||| Every well-typed term has a type that is a Sort
||| (This would require an inversion lemma on the typing judgment)
public export
typeOfType : HasType ctx e ty -> (l : Level ** HasType ctx ty (Sort l))
typeOfType hasType = ?typeOfType_hole

------------------------------------------------------------------------
-- Context Operations
------------------------------------------------------------------------

-- Note: Context concatenation (++) is tricky with de Bruijn indices
-- because types in ctx2 may reference variables in ctx1.
-- For now we leave it unimplemented as it's not needed for core proofs.

------------------------------------------------------------------------
-- Example Derivations
------------------------------------------------------------------------

||| Example: identity function at Type 0
||| id : (A : Type 0) → A → A
||| id = λA. λx. x
exampleId : HasType Empty
              (Lam (Sort (LSucc LZero))
                   (Lam (Var FZ) (Var FZ)))
              (Pi (Sort (LSucc LZero))
                  (Pi (Var FZ) (Var (FS FZ))))
exampleId = TLam TSort (TLam (TVar FZ) (TVar FZ))
