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
|||
||| Universe levels that appear in the result type are EXPLICIT parameters
||| to allow pattern matching to expose them.
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
  ||| Note: l is explicit to allow pattern matching access.
  TSort : (l : Level) -> HasType ctx (Sort l) (Sort (LSucc l))

  ||| Pi formation rule (Pi-F)
  |||
  |||   Γ ⊢ A : Type l₁    Γ, x:A ⊢ B : Type l₂
  ||| ───────────────────────────────────────────
  |||   Γ ⊢ (x : A) → B : Type (max l₁ l₂)
  |||
  ||| To form a Pi type, the domain must be a type and the codomain
  ||| must be a type in the extended context.
  ||| All parameters are explicit to allow pattern matching access.
  TPi : (l1 : Level) -> (l2 : Level)
     -> (dom : Expr n) -> (cod : Expr (S n))
     -> HasType ctx dom (Sort l1)
     -> HasType (Extend ctx dom) cod (Sort l2)
     -> HasType ctx (Pi dom cod) (Sort (lmax l1 l2))

  ||| Lambda introduction rule (Lam-I)
  |||
  |||   Γ ⊢ A : Type l    Γ, x:A ⊢ e : B
  ||| ─────────────────────────────────────
  |||   Γ ⊢ λ(x:A). e : (x : A) → B
  |||
  ||| A lambda has a Pi type. The body is typed in the extended context.
  ||| All parameters are explicit to allow pattern matching access.
  TLam : (l : Level)
      -> (ty : Expr n) -> (body : Expr (S n)) -> (bodyTy : Expr (S n))
      -> HasType ctx ty (Sort l)
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
  ||| All parameters are explicit to allow pattern matching access.
  TApp : (dom : Expr n) -> (cod : Expr (S n)) -> (f : Expr n) -> (arg : Expr n)
      -> HasType ctx f (Pi dom cod)
      -> HasType ctx arg dom
      -> HasType ctx (App f arg) (subst0 cod arg)

  ||| Let rule (Let)
  |||
  |||   Γ ⊢ A : Type l    Γ ⊢ v : A    Γ, x:A ⊢ e : B
  ||| ──────────────────────────────────────────────────
  |||   Γ ⊢ let x : A = v in e : B[x := v]
  |||
  ||| Let bindings have types that account for the substitution.
  ||| All parameters are explicit to allow pattern matching access.
  TLet : (l : Level)
      -> (ty : Expr n) -> (val : Expr n) -> (body : Expr (S n)) -> (bodyTy : Expr (S n))
      -> HasType ctx ty (Sort l)
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
  ||| All parameters are explicit to allow pattern matching access.
  TConv : (l : Level)
       -> (e : Expr n) -> (ty1 : Expr n) -> (ty2 : Expr n)
       -> HasType ctx e ty1
       -> ty1 = ty2  -- Simplified: using propositional equality
       -> HasType ctx ty2 (Sort l)
       -> HasType ctx e ty2

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
