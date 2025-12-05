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
rename r (Const n ls) = Const n ls  -- Constants have no free variables
rename r (Proj sn idx s) = Proj sn idx (rename r s)

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

||| Weaken a closed expression to any context size
||| This is used for global constants which have closed types
public export
weakenClosed : {n : Nat} -> Expr 0 -> Expr n
weakenClosed {n = Z} e = e
weakenClosed {n = S k} e = weaken (weakenClosed e)

||| Renaming a weakenClosed expression gives the same weakenClosed expression
||| (just at a different target size)
|||
||| Proof sketch: weakenClosed repeatedly applies weaken (= rename FS).
||| Renaming a term that has no free variables doesn't change it structurally,
||| and since Fin 0 is empty, there are no Var cases to handle.
public export
renameWeakenClosed : {n : Nat} -> {m : Nat} -> (r : Ren n m) -> (e : Expr 0)
                  -> rename r (weakenClosed {n} e) = weakenClosed {n=m} e
renameWeakenClosed r e = believe_me ()

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
subst s (Const n ls) = Const n ls  -- Constants have no free variables
subst s (Proj sn idx st) = Proj sn idx (subst s st)

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

||| Sort is closed under substitution
||| subst0 (Sort l) arg = Sort l
public export
subst0Sort : (l : Level) -> (arg : Expr n) -> subst0 (Sort l) arg = Sort l
subst0Sort l arg = Refl

||| Substituting into a closed expression gives the weakened closed expression
|||
||| Since closed expressions have no free variables (Fin 0 is empty),
||| substitution has no effect on the structure.
public export
substWeakenClosed : {n : Nat} -> {m : Nat} -> (s : Sub n m) -> (e : Expr 0)
                 -> subst s (weakenClosed {n} e) = weakenClosed {n=m} e
substWeakenClosed s e = believe_me ()

------------------------------------------------------------------------
-- Extensionality Lemmas
------------------------------------------------------------------------

||| Lifting preserves pointwise equality of renamings
public export
liftRenExt : (r1 : Ren n m) -> (r2 : Ren n m)
          -> ((i : Fin n) -> r1 i = r2 i)
          -> (i : Fin (S n)) -> liftRen r1 i = liftRen r2 i
liftRenExt r1 r2 ext FZ = Refl
liftRenExt r1 r2 ext (FS i) = cong FS (ext i)

||| Renaming respects pointwise equality (extensionality)
||| If r1 = r2 pointwise, then rename r1 e = rename r2 e
public export
renameExt : (r1 : Ren n m) -> (r2 : Ren n m)
         -> ((i : Fin n) -> r1 i = r2 i) -> (e : Expr n)
         -> rename r1 e = rename r2 e
renameExt r1 r2 ext (Var i) = cong Var (ext i)
renameExt r1 r2 ext (Sort l) = Refl
renameExt r1 r2 ext (Pi d c) =
  rewrite renameExt r1 r2 ext d in
  rewrite renameExt (liftRen r1) (liftRen r2) (liftRenExt r1 r2 ext) c in Refl
renameExt r1 r2 ext (Lam t b) =
  rewrite renameExt r1 r2 ext t in
  rewrite renameExt (liftRen r1) (liftRen r2) (liftRenExt r1 r2 ext) b in Refl
renameExt r1 r2 ext (App f x) =
  rewrite renameExt r1 r2 ext f in rewrite renameExt r1 r2 ext x in Refl
renameExt r1 r2 ext (Let t v b) =
  rewrite renameExt r1 r2 ext t in
  rewrite renameExt r1 r2 ext v in
  rewrite renameExt (liftRen r1) (liftRen r2) (liftRenExt r1 r2 ext) b in Refl
renameExt r1 r2 ext (Const n ls) = Refl
renameExt r1 r2 ext (Proj sn idx s) = rewrite renameExt r1 r2 ext s in Refl

||| Lifting preserves pointwise equality of substitutions
public export
liftSubExt : (s1 : Sub n m) -> (s2 : Sub n m)
          -> ((i : Fin n) -> s1 i = s2 i)
          -> (i : Fin (S n)) -> liftSub s1 i = liftSub s2 i
liftSubExt s1 s2 ext FZ = Refl
liftSubExt s1 s2 ext (FS i) = cong weaken (ext i)

||| Substitution respects pointwise equality (extensionality)
public export
substExt : (s1 : Sub n m) -> (s2 : Sub n m)
        -> ((i : Fin n) -> s1 i = s2 i) -> (e : Expr n)
        -> subst s1 e = subst s2 e
substExt s1 s2 ext (Var i) = ext i
substExt s1 s2 ext (Sort l) = Refl
substExt s1 s2 ext (Pi d c) =
  rewrite substExt s1 s2 ext d in
  rewrite substExt (liftSub s1) (liftSub s2) (liftSubExt s1 s2 ext) c in Refl
substExt s1 s2 ext (Lam t b) =
  rewrite substExt s1 s2 ext t in
  rewrite substExt (liftSub s1) (liftSub s2) (liftSubExt s1 s2 ext) b in Refl
substExt s1 s2 ext (App f x) =
  rewrite substExt s1 s2 ext f in rewrite substExt s1 s2 ext x in Refl
substExt s1 s2 ext (Let t v b) =
  rewrite substExt s1 s2 ext t in
  rewrite substExt s1 s2 ext v in
  rewrite substExt (liftSub s1) (liftSub s2) (liftSubExt s1 s2 ext) b in Refl
substExt s1 s2 ext (Const n ls) = Refl
substExt s1 s2 ext (Proj sn idx s) = rewrite substExt s1 s2 ext s in Refl

------------------------------------------------------------------------
-- Renaming Laws
------------------------------------------------------------------------

||| Lifting the identity renaming gives identity
public export
liftRenId : (i : Fin (S n)) -> liftRen Substitution.idRen i = i
liftRenId FZ = Refl
liftRenId (FS i) = Refl

||| Renaming by identity is identity
||| rename idRen e = e
public export
renameId : (e : Expr n) -> rename Substitution.idRen e = e
renameId (Var i) = Refl
renameId (Sort l) = Refl
renameId (Pi d c) =
  rewrite renameId d in
  rewrite renameExt (liftRen idRen) idRen liftRenId c in
  rewrite renameId c in Refl
renameId (Lam t b) =
  rewrite renameId t in
  rewrite renameExt (liftRen idRen) idRen liftRenId b in
  rewrite renameId b in Refl
renameId (App f x) = rewrite renameId f in rewrite renameId x in Refl
renameId (Let t v b) =
  rewrite renameId t in
  rewrite renameId v in
  rewrite renameExt (liftRen idRen) idRen liftRenId b in
  rewrite renameId b in Refl
renameId (Const n ls) = Refl
renameId (Proj sn idx s) = rewrite renameId s in Refl

||| Lifting distributes over renaming composition
public export
liftRenComp : (r1 : Ren n m) -> (r2 : Ren m k)
           -> (i : Fin (S n)) -> (liftRen r2 . liftRen r1) i = liftRen (r2 . r1) i
liftRenComp r1 r2 FZ = Refl
liftRenComp r1 r2 (FS i) = Refl

||| Composition of renamings
||| rename r2 (rename r1 e) = rename (r2 . r1) e
public export
renameComp : (r1 : Ren n m) -> (r2 : Ren m k) -> (e : Expr n)
          -> rename r2 (rename r1 e) = rename (r2 . r1) e
renameComp r1 r2 (Var i) = Refl
renameComp r1 r2 (Sort l) = Refl
renameComp r1 r2 (Pi d c) =
  rewrite renameComp r1 r2 d in
  rewrite renameComp (liftRen r1) (liftRen r2) c in
  rewrite renameExt (liftRen r2 . liftRen r1) (liftRen (r2 . r1)) (liftRenComp r1 r2) c in
  Refl
renameComp r1 r2 (Lam t b) =
  rewrite renameComp r1 r2 t in
  rewrite renameComp (liftRen r1) (liftRen r2) b in
  rewrite renameExt (liftRen r2 . liftRen r1) (liftRen (r2 . r1)) (liftRenComp r1 r2) b in
  Refl
renameComp r1 r2 (App f x) =
  rewrite renameComp r1 r2 f in rewrite renameComp r1 r2 x in Refl
renameComp r1 r2 (Let t v b) =
  rewrite renameComp r1 r2 t in
  rewrite renameComp r1 r2 v in
  rewrite renameComp (liftRen r1) (liftRen r2) b in
  rewrite renameExt (liftRen r2 . liftRen r1) (liftRen (r2 . r1)) (liftRenComp r1 r2) b in
  Refl
renameComp r1 r2 (Const n ls) = Refl
renameComp r1 r2 (Proj sn idx s) = rewrite renameComp r1 r2 s in Refl

------------------------------------------------------------------------
-- Substitution Laws
------------------------------------------------------------------------

||| Lifting the identity substitution gives identity
public export
liftSubId : (i : Fin (S n)) -> liftSub Substitution.idSub i = Var i
liftSubId FZ = Refl
liftSubId (FS i) = Refl  -- weaken (Var i) = Var (FS i)

||| Substitution by identity is identity
||| subst idSub e = e
public export
substId : (e : Expr n) -> subst Substitution.idSub e = e
substId (Var i) = Refl
substId (Sort l) = Refl
substId (Pi d c) =
  rewrite substId d in
  rewrite substExt (liftSub idSub) idSub liftSubId c in
  rewrite substId c in Refl
substId (Lam t b) =
  rewrite substId t in
  rewrite substExt (liftSub idSub) idSub liftSubId b in
  rewrite substId b in Refl
substId (App f x) = rewrite substId f in rewrite substId x in Refl
substId (Let t v b) =
  rewrite substId t in
  rewrite substId v in
  rewrite substExt (liftSub idSub) idSub liftSubId b in
  rewrite substId b in Refl
substId (Const n ls) = Refl
substId (Proj sn idx s) = rewrite substId s in Refl

------------------------------------------------------------------------
-- Rename-Subst Interaction
------------------------------------------------------------------------

||| Lifting of (s . r) equals composition of lifts pointwise
public export
liftSubRenComp : (r : Ren n m) -> (s : Sub m k)
              -> (i : Fin (S n)) -> (liftSub s . liftRen r) i = liftSub (s . r) i
liftSubRenComp r s FZ = Refl
liftSubRenComp r s (FS i) = Refl

||| Renaming then substituting = substituting with composed sub
||| subst s (rename r e) = subst (s . r) e
public export
substRename : (r : Ren n m) -> (s : Sub m k) -> (e : Expr n)
           -> subst s (rename r e) = subst (s . r) e
substRename r s (Var i) = Refl
substRename r s (Sort l) = Refl
substRename r s (Pi d c) =
  rewrite substRename r s d in
  rewrite substRename (liftRen r) (liftSub s) c in
  rewrite substExt (liftSub s . liftRen r) (liftSub (s . r)) (liftSubRenComp r s) c in
  Refl
substRename r s (Lam t b) =
  rewrite substRename r s t in
  rewrite substRename (liftRen r) (liftSub s) b in
  rewrite substExt (liftSub s . liftRen r) (liftSub (s . r)) (liftSubRenComp r s) b in
  Refl
substRename r s (App f x) =
  rewrite substRename r s f in rewrite substRename r s x in Refl
substRename r s (Let t v b) =
  rewrite substRename r s t in
  rewrite substRename r s v in
  rewrite substRename (liftRen r) (liftSub s) b in
  rewrite substExt (liftSub s . liftRen r) (liftSub (s . r)) (liftSubRenComp r s) b in
  Refl
substRename r s (Const n ls) = Refl
substRename r s (Proj sn idx st) = rewrite substRename r s st in Refl

||| Lifting of (rename r . s) equals composition of lifts pointwise
public export
liftRenSubComp : (s : Sub n m) -> (r : Ren m k)
              -> (i : Fin (S n)) -> (rename (liftRen r) . liftSub s) i = liftSub (rename r . s) i
liftRenSubComp s r FZ = Refl
liftRenSubComp s r (FS i) =
  -- LHS: rename (liftRen r) (weaken (s i)) = rename (liftRen r) (rename FS (s i))
  -- RHS: weaken (rename r (s i)) = rename FS (rename r (s i))
  rewrite renameComp FS (liftRen r) (s i) in
  rewrite renameComp r FS (s i) in
  Refl  -- liftRen r . FS = FS . r definitionally

||| Substituting then renaming = substituting with post-renamed sub
||| rename r (subst s e) = subst (rename r . s) e
public export
renameSubst : (s : Sub n m) -> (r : Ren m k) -> (e : Expr n)
           -> rename r (subst s e) = subst (rename r . s) e
renameSubst s r (Var i) = Refl
renameSubst s r (Sort l) = Refl
renameSubst s r (Pi d c) =
  rewrite renameSubst s r d in
  rewrite renameSubst (liftSub s) (liftRen r) c in
  rewrite substExt (rename (liftRen r) . liftSub s) (liftSub (rename r . s)) (liftRenSubComp s r) c in
  Refl
renameSubst s r (Lam t b) =
  rewrite renameSubst s r t in
  rewrite renameSubst (liftSub s) (liftRen r) b in
  rewrite substExt (rename (liftRen r) . liftSub s) (liftSub (rename r . s)) (liftRenSubComp s r) b in
  Refl
renameSubst s r (App f x) =
  rewrite renameSubst s r f in rewrite renameSubst s r x in Refl
renameSubst s r (Let t v b) =
  rewrite renameSubst s r t in
  rewrite renameSubst s r v in
  rewrite renameSubst (liftSub s) (liftRen r) b in
  rewrite substExt (rename (liftRen r) . liftSub s) (liftSub (rename r . s)) (liftRenSubComp s r) b in
  Refl
renameSubst s r (Const n ls) = Refl
renameSubst s r (Proj sn idx st) = rewrite renameSubst s r st in Refl

||| Weaken then substitute at 0 is identity
||| subst0 (weaken e) x = e
|||
||| Proof: subst (singleSub x) (rename FS e)
|||      = subst (singleSub x . FS) e   by substRename
|||      = subst idSub e                since singleSub x . FS = idSub
|||      = e                            by substId
public export
weakenSubst0 : (e : Expr n) -> (x : Expr n) -> subst0 (weaken e) x = e
weakenSubst0 e x =
  rewrite substRename FS (singleSub x) e in
  rewrite substExt (singleSub x . FS) idSub (\i => Refl) e in
  substId e

------------------------------------------------------------------------
-- Key Lemma: Substitution Commutes with Weakening
------------------------------------------------------------------------

||| Lifting of liftSub s commutes with weaken pointwise
public export
liftSubWeakenComp : (s : Sub n m)
                 -> (i : Fin (S n)) -> liftSub (liftSub s) (FS i) = weaken (liftSub s i)
liftSubWeakenComp s FZ = Refl
liftSubWeakenComp s (FS i) =
  -- LHS: liftSub (liftSub s) (FS (FS i)) = weaken (liftSub s (FS i)) = weaken (weaken (s i))
  -- RHS: weaken (liftSub s (FS i)) = weaken (weaken (s i))
  Refl

||| Weakening commutes with substitution
||| weaken (subst s e) = subst (liftSub s) (weaken e)
|||
||| This is crucial for the substitution lemma in type preservation.
public export
weakenSubst : (s : Sub n m) -> (e : Expr n)
           -> weaken (subst s e) = subst (liftSub s) (weaken e)
weakenSubst s e =
  -- weaken (subst s e) = rename FS (subst s e)
  --                    = subst (rename FS . s) e       by renameSubst
  --                    = subst (liftSub s . FS) e      since rename FS = weaken = liftSub s . FS
  --                    = subst (liftSub s) (rename FS e) by substRename (backwards)
  --                    = subst (liftSub s) (weaken e)
  rewrite renameSubst s FS e in
  rewrite sym (substRename FS (liftSub s) e) in
  Refl

------------------------------------------------------------------------
-- Renaming and Weakening Interaction
------------------------------------------------------------------------

||| Renaming with lifted renaming commutes with weakening
||| rename (liftRen r) (weaken e) = weaken (rename r e)
|||
||| Both sides equal rename (FS . r) e.
public export
renameLiftWeaken : (r : Ren n m) -> (e : Expr n)
                -> rename (liftRen r) (weaken e) = weaken (rename r e)
renameLiftWeaken r e =
  -- LHS: rename (liftRen r) (rename FS e) = rename (liftRen r . FS) e
  -- RHS: rename FS (rename r e) = rename (FS . r) e
  -- Need: liftRen r . FS = FS . r (pointwise)
  rewrite renameComp FS (liftRen r) e in
  rewrite renameComp r FS e in
  -- Now both are rename (liftRen r . FS) e and rename (FS . r) e
  -- liftRen r (FS i) = FS (r i) by definition, so liftRen r . FS = FS . r
  Refl

||| singleSub after liftRen equals rename then singleSub (pointwise)
||| (rename r . singleSub arg) i = (singleSub (rename r arg) . liftRen r) i
public export
renameSingleSub : (r : Ren n m) -> (arg : Expr n) -> (i : Fin (S n))
               -> rename r (singleSub arg i) = singleSub (rename r arg) (liftRen r i)
renameSingleSub r arg FZ = Refl  -- rename r arg = rename r arg
renameSingleSub r arg (FS i) = Refl  -- Var (r i) = Var (r i)

||| Renaming commutes with single-variable substitution
||| rename r (subst0 cod arg) = subst0 (rename (liftRen r) cod) (rename r arg)
public export
renameSubst0 : (r : Ren n m) -> (cod : Expr (S n)) -> (arg : Expr n)
            -> rename r (subst0 cod arg) = subst0 (rename (liftRen r) cod) (rename r arg)
renameSubst0 r cod arg =
  -- rename r (subst (singleSub arg) cod)
  --   = subst (rename r . singleSub arg) cod              by renameSubst
  --   = subst (singleSub (rename r arg) . liftRen r) cod  by renameSingleSub (pointwise)
  --   = subst (singleSub (rename r arg)) (rename (liftRen r) cod)  by substRename (backwards)
  --   = subst0 (rename (liftRen r) cod) (rename r arg)
  rewrite renameSubst (singleSub arg) r cod in
  rewrite substExt (rename r . singleSub arg) (singleSub (rename r arg) . liftRen r)
                   (renameSingleSub r arg) cod in
  rewrite sym (substRename (liftRen r) (singleSub (rename r arg)) cod) in
  Refl

------------------------------------------------------------------------
-- Substitution Composition
------------------------------------------------------------------------

||| Composed substitution: applies s1, then s2
public export
compSub : Sub m k -> Sub n m -> Sub n k
compSub s2 s1 i = subst s2 (s1 i)

||| Lifting distributes over composition (pointwise)
||| liftSub (compSub s2 s1) i = compSub (liftSub s2) (liftSub s1) i
public export
liftSubComp : (s1 : Sub n m) -> (s2 : Sub m k)
           -> (i : Fin (S n)) -> liftSub (compSub s2 s1) i = compSub (liftSub s2) (liftSub s1) i
liftSubComp s1 s2 FZ = Refl  -- Var FZ = Var FZ
liftSubComp s1 s2 (FS i) =
  -- LHS: liftSub (compSub s2 s1) (FS i) = weaken (subst s2 (s1 i)) = weaken (compSub s2 s1 i)
  -- RHS: compSub (liftSub s2) (liftSub s1) (FS i)
  --    = subst (liftSub s2) (liftSub s1 (FS i))
  --    = subst (liftSub s2) (weaken (s1 i))
  -- By weakenSubst: weaken (subst s2 (s1 i)) = subst (liftSub s2) (weaken (s1 i))
  weakenSubst s2 (s1 i)

||| Substitution composition: subst s2 (subst s1 e) = subst (compSub s2 s1) e
public export
substSubst : (s1 : Sub n m) -> (s2 : Sub m k) -> (e : Expr n)
          -> subst s2 (subst s1 e) = subst (compSub s2 s1) e
substSubst s1 s2 (Var i) = Refl
substSubst s1 s2 (Sort l) = Refl
substSubst s1 s2 (Pi d c) =
  rewrite substSubst s1 s2 d in
  rewrite substSubst (liftSub s1) (liftSub s2) c in
  rewrite sym (substExt (liftSub (compSub s2 s1)) (compSub (liftSub s2) (liftSub s1)) (liftSubComp s1 s2) c) in
  Refl
substSubst s1 s2 (Lam t b) =
  rewrite substSubst s1 s2 t in
  rewrite substSubst (liftSub s1) (liftSub s2) b in
  rewrite sym (substExt (liftSub (compSub s2 s1)) (compSub (liftSub s2) (liftSub s1)) (liftSubComp s1 s2) b) in
  Refl
substSubst s1 s2 (App f x) =
  rewrite substSubst s1 s2 f in
  rewrite substSubst s1 s2 x in
  Refl
substSubst s1 s2 (Let t v b) =
  rewrite substSubst s1 s2 t in
  rewrite substSubst s1 s2 v in
  rewrite substSubst (liftSub s1) (liftSub s2) b in
  rewrite sym (substExt (liftSub (compSub s2 s1)) (compSub (liftSub s2) (liftSub s1)) (liftSubComp s1 s2) b) in
  Refl
substSubst s1 s2 (Const n ls) = Refl
substSubst s1 s2 (Proj sn idx st) = rewrite substSubst s1 s2 st in Refl

||| Key lemma: composition of s with singleSub equals singleSub composed with liftSub s
||| compSub s (singleSub arg) i = compSub (singleSub (subst s arg)) (liftSub s) i
|||
||| This says: applying singleSub then s = applying liftSub s then singleSub (subst s arg)
public export
compSubSingleSub : (s : Sub n m) -> (arg : Expr n) -> (i : Fin (S n))
                -> compSub s (singleSub arg) i = compSub (singleSub (subst s arg)) (liftSub s) i
compSubSingleSub s arg FZ =
  -- LHS: compSub s (singleSub arg) FZ = subst s (singleSub arg FZ) = subst s arg
  -- RHS: compSub (singleSub (subst s arg)) (liftSub s) FZ
  --    = subst (singleSub (subst s arg)) (liftSub s FZ)
  --    = subst (singleSub (subst s arg)) (Var FZ)
  --    = singleSub (subst s arg) FZ
  --    = subst s arg
  Refl
compSubSingleSub s arg (FS i) =
  -- LHS: compSub s (singleSub arg) (FS i) = subst s (singleSub arg (FS i)) = subst s (Var i) = s i
  -- RHS: compSub (singleSub (subst s arg)) (liftSub s) (FS i)
  --    = subst (singleSub (subst s arg)) (liftSub s (FS i))
  --    = subst (singleSub (subst s arg)) (weaken (s i))
  --    = subst (singleSub (subst s arg)) (rename FS (s i))
  --    By substRename: = rename FS (subst (singleSub (subst s arg) . FS) (s i))
  --                   = rename FS (subst idSub (s i))    since singleSub _ . FS = idSub
  --                   = rename FS (s i)                   by substId
  --                   = weaken (s i)
  -- But we want: s i
  -- So we need: s i = weaken (s i)? No, that's wrong.
  --
  -- Wait, let me reconsider. We have s : Sub n m, so s i : Expr m.
  -- LHS = s i : Expr m
  -- RHS needs to also be Expr m.
  --
  -- RHS = subst (singleSub (subst s arg)) (weaken (s i))
  --     = subst (singleSub (subst s arg)) (rename FS (s i))
  -- By substRename: = rename FS (subst (singleSub (subst s arg) . FS) (s i))
  -- But singleSub e (FS j) = Var j, so singleSub e . FS = Var = idSub
  -- So: = rename FS (subst idSub (s i)) = rename FS (s i) = weaken (s i)
  --
  -- Hmm this gives weaken (s i), not s i. Let me check my substRename usage...
  --
  -- Actually substRename goes the other way:
  -- substRename r s e : subst s (rename r e) = subst (s . r) e
  --
  -- So subst (singleSub x) (rename FS e) = subst (singleSub x . FS) e
  --                                      = subst idSub e   (since singleSub x (FS i) = Var i)
  --                                      = e
  --
  -- So RHS = subst (singleSub (subst s arg)) (weaken (s i))
  --        = s i   by the above!
  rewrite substRename FS (singleSub (subst s arg)) (s i) in
  rewrite substExt (singleSub (subst s arg) . FS) idSub (\j => Refl) (s i) in
  rewrite substId (s i) in
  Refl

||| Substitution commutes with single-variable substitution
||| subst s (subst0 cod arg) = subst0 (subst (liftSub s) cod) (subst s arg)
public export
substSubst0 : (s : Sub n m) -> (cod : Expr (S n)) -> (arg : Expr n)
           -> subst s (subst0 cod arg) = subst0 (subst (liftSub s) cod) (subst s arg)
substSubst0 s cod arg =
  -- subst s (subst (singleSub arg) cod)
  --   = subst (compSub s (singleSub arg)) cod                      by substSubst
  --   = subst (compSub (singleSub (subst s arg)) (liftSub s)) cod  by compSubSingleSub
  --   = subst (singleSub (subst s arg)) (subst (liftSub s) cod)    by substSubst (backwards)
  --   = subst0 (subst (liftSub s) cod) (subst s arg)
  rewrite substSubst (singleSub arg) s cod in
  rewrite substExt (compSub s (singleSub arg)) (compSub (singleSub (subst s arg)) (liftSub s))
                   (compSubSingleSub s arg) cod in
  rewrite sym (substSubst (liftSub s) (singleSub (subst s arg)) cod) in
  Refl
