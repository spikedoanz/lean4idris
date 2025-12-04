||| Core Syntax for a Simplified Dependent Type Theory
|||
||| This defines the expression type, intrinsically scoped to prevent
||| free variable escape. This is a fragment of Lean's type theory
||| sufficient to demonstrate subject reduction.
module Lean4Idris.Proofs.Syntax

import Data.Fin
import public Data.Vect

%default total

------------------------------------------------------------------------
-- Universe Levels
------------------------------------------------------------------------

||| Universe levels (simplified - no level polymorphism)
public export
data Level : Type where
  LZero : Level
  LSucc : Level -> Level

public export
Eq Level where
  LZero == LZero = True
  (LSucc l1) == (LSucc l2) = l1 == l2
  _ == _ = False

||| Maximum of two levels
public export
lmax : Level -> Level -> Level
lmax LZero l = l
lmax l LZero = l
lmax (LSucc l1) (LSucc l2) = LSucc (lmax l1 l2)

------------------------------------------------------------------------
-- Expressions (Intrinsically Scoped)
------------------------------------------------------------------------

||| Expressions indexed by the number of free variables in scope.
|||
||| `Expr n` means the expression may contain variables 0..(n-1).
||| This ensures well-scopedness by construction - no runtime checks needed.
|||
||| Key insight: `Fin n` can only hold values 0..(n-1), so `Var (Fin n)`
||| can never reference an out-of-scope variable.
public export
data Expr : Nat -> Type where
  ||| Bound variable (de Bruijn index)
  ||| Var FZ is the most recently bound variable
  Var : Fin n -> Expr n

  ||| Universe/Sort: Type at some level
  ||| Sort LZero = Prop, Sort (LSucc LZero) = Type 0, etc.
  Sort : Level -> Expr n

  ||| Pi type (dependent function type): (x : A) -> B
  ||| The codomain B can reference variable 0 (which is x)
  Pi : (dom : Expr n) -> (cod : Expr (S n)) -> Expr n

  ||| Lambda abstraction: λ(x : A). body
  ||| The body can reference variable 0 (which is x)
  Lam : (ty : Expr n) -> (body : Expr (S n)) -> Expr n

  ||| Application: f x
  App : Expr n -> Expr n -> Expr n

  ||| Let binding: let x : A = v in body
  ||| The body can reference variable 0 (which is x)
  Let : (ty : Expr n) -> (val : Expr n) -> (body : Expr (S n)) -> Expr n

------------------------------------------------------------------------
-- Derived Forms and Conveniences
------------------------------------------------------------------------

||| Shift all variable indices up by 1 (simple renaming version)
||| This duplicates Substitution.weaken but avoids circular imports
shift : Expr n -> Expr (S n)
shift (Var i) = Var (FS i)
shift (Sort l) = Sort l
shift (Pi d c) = Pi (shift d) (shift c)
shift (Lam t b) = Lam (shift t) (shift b)
shift (App f x) = App (shift f) (shift x)
shift (Let t v b) = Let (shift t) (shift v) (shift b)

||| Non-dependent function type: A -> B
||| Encoded as Pi where the codomain doesn't use the variable
public export
Arrow : Expr n -> Expr n -> Expr n
Arrow a b = Pi a (shift b)

------------------------------------------------------------------------
-- Show instance for debugging
------------------------------------------------------------------------

export
Show Level where
  show LZero = "0"
  show (LSucc l) = "S(" ++ show l ++ ")"

showVar : Fin n -> String
showVar FZ = "x0"
showVar (FS i) = "x" ++ show (finToNat (FS i))

export
{n : Nat} -> Show (Expr n) where
  show (Var i) = showVar i
  show (Sort l) = "Type " ++ show l
  show (Pi d c) = "(Π _ : " ++ show d ++ ". " ++ show c ++ ")"
  show (Lam t b) = "(λ _ : " ++ show t ++ ". " ++ show b ++ ")"
  show (App f x) = "(" ++ show f ++ " " ++ show x ++ ")"
  show (Let t v b) = "(let _ : " ++ show t ++ " = " ++ show v ++ " in " ++ show b ++ ")"

------------------------------------------------------------------------
-- Decidable Equality
------------------------------------------------------------------------

||| Decidable equality for Fin
finEq : (i : Fin n) -> (j : Fin n) -> Dec (i = j)
finEq FZ FZ = Yes Refl
finEq FZ (FS j) = No (\case Refl impossible)
finEq (FS i) FZ = No (\case Refl impossible)
finEq (FS i) (FS j) = case finEq i j of
  Yes Refl => Yes Refl
  No contra => No (\case Refl => contra Refl)

||| Decidable equality for Level
public export
levelEq : (l1 : Level) -> (l2 : Level) -> Dec (l1 = l2)
levelEq LZero LZero = Yes Refl
levelEq LZero (LSucc _) = No (\case Refl impossible)
levelEq (LSucc _) LZero = No (\case Refl impossible)
levelEq (LSucc l1) (LSucc l2) = case levelEq l1 l2 of
  Yes Refl => Yes Refl
  No contra => No (\case Refl => contra Refl)
