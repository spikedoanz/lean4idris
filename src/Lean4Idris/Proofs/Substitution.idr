||| Substitution and Weakening Operations
|||
||| This module defines the fundamental operations on expressions:
||| - Weakening: shift all variable indices up
||| - Substitution: replace a variable with an expression
|||
||| These are the workhorses of type theory metatheory.
module Lean4Idris.Proofs.Substitution

import Data.Fin
import Data.Vect
import Lean4Idris.Proofs.Syntax

%default total

------------------------------------------------------------------------
-- Renaming (Variable-to-Variable Substitution)
------------------------------------------------------------------------

||| A renaming from n variables to m variables
||| Maps each variable in the source to a variable in the target
public export
Ren : Nat -> Nat -> Type
Ren n m = Fin n -> Fin m

||| Identity renaming
public export
idRen : Ren n n
idRen = id

||| Shift renaming: shift all variables up by 1
||| Used when going under a binder
public export
shiftRen : Ren n (S n)
shiftRen = FS

||| Lift a renaming under a binder
||| The new variable 0 maps to 0, others are shifted
public export
liftRen : Ren n m -> Ren (S n) (S m)
liftRen r FZ = FZ
liftRen r (FS i) = FS (r i)

||| Apply a renaming to an expression
public export
rename : Ren n m -> Expr n -> Expr m
rename r (Var i) = Var (r i)
rename r (Sort l) = Sort l
rename r (Pi d c) = Pi (rename r d) (rename (liftRen r) c)
rename r (Lam t b) = Lam (rename r t) (rename (liftRen r) b)
rename r (App f x) = App (rename r f) (rename r x)
rename r (Let t v b) = Let (rename r t) (rename r v) (rename (liftRen r) b)

------------------------------------------------------------------------
-- Weakening
------------------------------------------------------------------------

||| Weaken an expression by shifting all variables up by 1
||| This is used when extending the context with a new variable
public export
weaken : Expr n -> Expr (S n)
weaken = rename shiftRen

||| Weaken by k positions
public export
weakenN : (k : Nat) -> Expr n -> Expr (k + n)
weakenN Z e = e
weakenN (S k) e = weaken (weakenN k e)

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

||| A substitution from n variables to expressions with m free vars
||| Maps each variable in the source to an expression in the target
public export
Sub : Nat -> Nat -> Type
Sub n m = Fin n -> Expr m

||| Identity substitution: each variable maps to itself
public export
idSub : Sub n n
idSub i = Var i

||| Shift substitution: each variable maps to the next variable
public export
shiftSub : Sub n (S n)
shiftSub i = Var (FS i)

||| Lift a substitution under a binder
||| Variable 0 maps to itself (Var FZ)
||| Other variables are substituted and then weakened
public export
liftSub : Sub n m -> Sub (S n) (S m)
liftSub s FZ = Var FZ
liftSub s (FS i) = weaken (s i)

||| Apply a substitution to an expression
public export
subst : Sub n m -> Expr n -> Expr m
subst s (Var i) = s i
subst s (Sort l) = Sort l
subst s (Pi d c) = Pi (subst s d) (subst (liftSub s) c)
subst s (Lam t b) = Lam (subst s t) (subst (liftSub s) b)
subst s (App f x) = App (subst s f) (subst s x)
subst s (Let t v b) = Let (subst s t) (subst s v) (subst (liftSub s) b)

------------------------------------------------------------------------
-- Single-Variable Substitution
------------------------------------------------------------------------

||| Substitution that replaces variable 0 with e, shifts others down
||| This is the β-reduction substitution: b[x := a]
public export
singleSub : Expr n -> Sub (S n) n
singleSub e FZ = e
singleSub e (FS i) = Var i

||| Substitute variable 0 with an expression
||| subst0 body arg = body[0 := arg]
public export
subst0 : Expr (S n) -> Expr n -> Expr n
subst0 body arg = subst (singleSub arg) body

------------------------------------------------------------------------
-- Substitution Laws (stated, to be proved)
------------------------------------------------------------------------

||| Renaming by identity is identity
||| rename idRen e = e
public export
renameId : (e : Expr n) -> rename Substitution.idRen e = e
renameId (Var i) = Refl
renameId (Sort l) = Refl
renameId (Pi d c) = rewrite renameId d in rewrite liftRenId c in Refl
  where
    liftRenId : (e : Expr (S n)) -> rename (liftRen Substitution.idRen) e = e
    liftRenId e = ?liftRenId_hole
renameId (Lam t b) = ?renameLam_hole
renameId (App f x) = rewrite renameId f in rewrite renameId x in Refl
renameId (Let t v b) = ?renameLet_hole

||| Substitution by identity is identity
||| subst idSub e = e
public export
substId : (e : Expr n) -> subst Substitution.idSub e = e
substId (Var i) = Refl
substId (Sort l) = Refl
substId (Pi d c) = ?substPi_hole
substId (Lam t b) = ?substLam_hole
substId (App f x) = rewrite substId f in rewrite substId x in Refl
substId (Let t v b) = ?substLet_hole

||| Weaken then substitute at 0 is identity
||| subst0 (weaken e) x = e
public export
weakenSubst0 : (e : Expr n) -> (x : Expr n) -> subst0 (weaken e) x = e
weakenSubst0 e x = ?weakenSubst0_hole

||| Composition of renamings
||| rename r2 (rename r1 e) = rename (r2 . r1) e
public export
renameComp : (r1 : Ren n m) -> (r2 : Ren m k) -> (e : Expr n)
          -> rename r2 (rename r1 e) = rename (r2 . r1) e
renameComp r1 r2 e = ?renameComp_hole

------------------------------------------------------------------------
-- Key Lemma: Substitution Commutes with Weakening (stated)
------------------------------------------------------------------------

||| Weakening commutes with substitution
||| weaken (subst s e) = subst (weaken . s) (weaken e)
|||
||| This is crucial for the substitution lemma in type preservation.
public export
weakenSubst : (s : Sub n m) -> (e : Expr n)
           -> weaken (subst s e) = subst (liftSub s) (weaken e)
weakenSubst s e = ?weakenSubst_hole
