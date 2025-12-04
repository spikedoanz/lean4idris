||| Typing Judgment for Dependent Type Theory
|||
||| This module defines the typing rules as an inductive type.
||| A value of type `HasType ctx e ty` is a proof that
||| expression `e` has type `ty` in context `ctx`.
|||
||| NOTE: Universe levels are explicit parameters in constructors to allow
||| pattern matching to expose them. This works around Idris 2's limitation
||| where implicit parameters aren't accessible after pattern matching.
module Lean4Idris.Proofs.Typing

import Data.Fin
import Data.Vect
import Lean4Idris.Proofs.Name
import Lean4Idris.Proofs.Syntax
import Lean4Idris.Proofs.Substitution
import Lean4Idris.Proofs.Environment
import Lean4Idris.Proofs.DefEq

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

||| Typing judgment: Σ; Γ ⊢ e : T
|||
||| This is the core of the type system. Each constructor corresponds
||| to a typing rule from the literature.
|||
||| `HasType env ctx e ty` is a proof that in environment `env` and
||| context `ctx`, expression `e` has type `ty`.
|||
||| Universe levels that appear in the result type are EXPLICIT parameters
||| to allow pattern matching to expose them.
public export
data HasType : Env -> Ctx n -> Expr n -> Expr n -> Type where

  ||| Variable rule (Var)
  |||
  |||   x : A ∈ Γ
  ||| ─────────────
  |||   Σ; Γ ⊢ x : A
  |||
  ||| If variable i has type A in the context, then Var i has type A.
  TVar : (i : Fin n)
      -> HasType env ctx (Var i) (lookupVar ctx i)

  ||| Sort rule (Type-in-Type, simplified)
  |||
  ||| ───────────────────────
  |||   Σ; Γ ⊢ Type l : Type (l+1)
  |||
  ||| Each universe is typed by the next universe.
  ||| (A proper treatment would track universe consistency.)
  ||| Note: l is explicit to allow pattern matching access.
  TSort : (l : Level) -> HasType env ctx (Sort l) (Sort (LSucc l))

  ||| Pi formation rule (Pi-F)
  |||
  |||   Σ; Γ ⊢ A : Type l₁    Σ; Γ, x:A ⊢ B : Type l₂
  ||| ─────────────────────────────────────────────────
  |||   Σ; Γ ⊢ (x : A) → B : Type (max l₁ l₂)
  |||
  ||| To form a Pi type, the domain must be a type and the codomain
  ||| must be a type in the extended context.
  ||| All parameters are explicit to allow pattern matching access.
  TPi : (l1 : Level) -> (l2 : Level)
     -> (dom : Expr n) -> (cod : Expr (S n))
     -> HasType env ctx dom (Sort l1)
     -> HasType env (Extend ctx dom) cod (Sort l2)
     -> HasType env ctx (Pi dom cod) (Sort (lmax l1 l2))

  ||| Lambda introduction rule (Lam-I)
  |||
  |||   Σ; Γ ⊢ A : Type l    Σ; Γ, x:A ⊢ e : B
  ||| ───────────────────────────────────────────
  |||   Σ; Γ ⊢ λ(x:A). e : (x : A) → B
  |||
  ||| A lambda has a Pi type. The body is typed in the extended context.
  ||| All parameters are explicit to allow pattern matching access.
  TLam : (l : Level)
      -> (ty : Expr n) -> (body : Expr (S n)) -> (bodyTy : Expr (S n))
      -> HasType env ctx ty (Sort l)
      -> HasType env (Extend ctx ty) body bodyTy
      -> HasType env ctx (Lam ty body) (Pi ty bodyTy)

  ||| Application rule (App)
  |||
  |||   Σ; Γ ⊢ f : (x : A) → B    Σ; Γ ⊢ a : A    Σ; Γ, x:A ⊢ B : Type l
  ||| ─────────────────────────────────────────────────────────────────────
  |||   Σ; Γ ⊢ f a : B[x := a]
  |||
  ||| Applying a function to an argument substitutes the argument
  ||| into the codomain type. We require the codomain to be well-typed
  ||| to enable the substitution lemma for typeOfType.
  ||| All parameters are explicit to allow pattern matching access.
  TApp : (l : Level) -> (dom : Expr n) -> (cod : Expr (S n)) -> (f : Expr n) -> (arg : Expr n)
      -> HasType env ctx f (Pi dom cod)
      -> HasType env ctx arg dom
      -> HasType env (Extend ctx dom) cod (Sort l)
      -> HasType env ctx (App f arg) (subst0 cod arg)

  ||| Let rule (Let)
  |||
  |||   Σ; Γ ⊢ A : Type l₁    Σ; Γ ⊢ v : A    Σ; Γ, x:A ⊢ e : B    Σ; Γ, x:A ⊢ B : Type l₂
  ||| ──────────────────────────────────────────────────────────────────────────────────────
  |||   Σ; Γ ⊢ let x : A = v in e : B[x := v]
  |||
  ||| Let bindings have types that account for the substitution.
  ||| We require bodyTy to be well-typed for the substitution lemma.
  ||| All parameters are explicit to allow pattern matching access.
  TLet : (l1 : Level) -> (l2 : Level)
      -> (ty : Expr n) -> (val : Expr n) -> (body : Expr (S n)) -> (bodyTy : Expr (S n))
      -> HasType env ctx ty (Sort l1)
      -> HasType env ctx val ty
      -> HasType env (Extend ctx ty) body bodyTy
      -> HasType env (Extend ctx ty) bodyTy (Sort l2)
      -> HasType env ctx (Let ty val body) (subst0 bodyTy val)

  ||| Conversion rule (Conv)
  |||
  |||   Σ; Γ ⊢ e : A    A ≡ B    Σ; Γ ⊢ B : Type l
  ||| ───────────────────────────────────────────────
  |||   Σ; Γ ⊢ e : B
  |||
  ||| If two types are definitionally equal, we can convert between them.
  ||| All parameters are explicit to allow pattern matching access.
  TConv : (l : Level)
       -> (e : Expr n) -> (ty1 : Expr n) -> (ty2 : Expr n)
       -> HasType env ctx e ty1
       -> DefEq ty1 ty2
       -> HasType env ctx ty2 (Sort l)
       -> HasType env ctx e ty2

  ||| Constant rule (Const)
  |||
  |||   Σ(c) = (ty, _)    |levels| = |params|
  ||| ─────────────────────────────────────────────────────────────
  |||   Σ; Γ ⊢ c.{levels} : ty[params := levels]
  |||
  ||| A global constant has the type from the environment,
  ||| with universe parameters instantiated and weakened to the context.
  TConst : (name : Name) -> (levels : List Level)
        -> (ty : Expr 0)  -- The type from the environment (closed)
        -> getConstType name env = Just ty
        -> HasType env ctx (Const name levels) (weakenClosed (instantiateLevels ty levels))

------------------------------------------------------------------------
-- Basic Properties
------------------------------------------------------------------------

||| Every well-typed term has a type that is itself well-typed (as a Sort).
|||
||| This is a key lemma showing the type system is well-formed.
||| It's proved by induction on the typing derivation.
|||
||| Note: This requires knowing the types of context entries are well-typed,
||| which we'd get from a well-formed context invariant. For now, we use
||| a hole for the TVar case.
public export
typeOfType : HasType env ctx e ty -> (l : Level ** HasType env ctx ty (Sort l))
-- TVar: type is lookupVar ctx i, which should be well-typed in the context
-- This requires a well-formed context invariant
typeOfType (TVar i) = ?typeOfType_TVar
-- TSort: Sort l has type Sort (LSucc l)
typeOfType (TSort l) = (LSucc (LSucc l) ** TSort (LSucc l))
-- TPi: Pi dom cod has type Sort (lmax l1 l2), which has type Sort (LSucc (lmax l1 l2))
typeOfType (TPi l1 l2 dom cod domWf codWf) =
  (LSucc (lmax l1 l2) ** TSort (lmax l1 l2))
-- TLam: Lam ty body has type Pi ty bodyTy, need to show Pi ty bodyTy : Sort l
typeOfType (TLam l ty body bodyTy tyWf bodyWf) =
  let (l2 ** bodyTyWf) = typeOfType bodyWf
  in (lmax l l2 ** TPi l l2 ty bodyTy tyWf bodyTyWf)
-- TApp: App f arg has type subst0 cod arg
-- We have codWf : HasType env (Extend ctx dom) cod (Sort l)
-- By substitution lemma: HasType env ctx (subst0 cod arg) (subst0 (Sort l) arg) = HasType env ctx (subst0 cod arg) (Sort l)
-- Note: substitutionLemma is defined in SubstitutionLemma.idr which imports Typing.idr,
-- so we can't import it here. This case is filled in SubjectReduction where we have access.
typeOfType (TApp l dom cod f arg fWf argWf codWf) =
  -- subst0 (Sort l) arg = Sort l (Sort doesn't mention variables)
  (l ** ?typeOfType_TApp_hole)
-- TLet: Let ty val body has type subst0 bodyTy val
-- We have bodyTyWf : HasType env (Extend ctx ty) bodyTy (Sort l2)
-- By substitution lemma: HasType env ctx (subst0 bodyTy val) (Sort l2)
-- Same circular dependency as TApp.
typeOfType (TLet l1 l2 ty val body bodyTy tyWf valWf bodyWf bodyTyWf) =
  (l2 ** ?typeOfType_TLet_hole)
-- TConv: e has type ty2, which has type Sort l (given as tyWf)
typeOfType (TConv l e ty1 ty2 eWf eq tyWf) = (l ** tyWf)
-- TConst: Const name levels has type instantiateLevels ty levels
-- Need to show that the instantiated type is well-typed
typeOfType (TConst name levels ty lookup) = ?typeOfType_TConst

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
exampleId : {env : Env} -> HasType env Empty
              (Lam (Sort (LSucc LZero))
                   (Lam (Var FZ) (Var FZ)))
              (Pi (Sort (LSucc LZero))
                  (Pi (Var FZ) (Var (FS FZ))))
exampleId = TLam (LSucc (LSucc LZero))
                 (Sort (LSucc LZero))       -- ty: the annotation type (Type 1)
                 (Lam (Var FZ) (Var FZ))    -- body: λx.x
                 (Pi (Var FZ) (Var (FS FZ))) -- bodyTy: A → A (in extended context)
                 (TSort (LSucc LZero))       -- proof that ty : Sort (LSucc (LSucc LZero))
                 (TLam (LSucc LZero)
                       (Var FZ)              -- inner ty: A (variable 0)
                       (Var FZ)              -- inner body: x
                       (Var (FS FZ))         -- inner bodyTy: A (shifted)
                       (TVar FZ)             -- proof that A : Sort (LSucc LZero)
                       (TVar FZ))            -- proof that x : A
