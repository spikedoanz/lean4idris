||| Well-scoped expressions for Lean 4
|||
||| Expressions are indexed by a natural number representing the number of
||| bound variables in scope. This makes ill-scoped terms unrepresentable.
||| De Bruijn indices are represented as `Fin n` ensuring they're always valid.
module Lean4Idris.Expr

import Lean4Idris.Name
import Lean4Idris.Level
import Data.Fin
import Data.Vect
import Data.List

%default total

||| Binder information - how a variable binding appears in source
public export
data BinderInfo : Type where
  ||| Default: explicit `(x : A)`
  Default : BinderInfo
  ||| Implicit: `{x : A}`
  Implicit : BinderInfo
  ||| Strict implicit: `{{x : A}}`
  StrictImplicit : BinderInfo
  ||| Instance: `[x : A]`
  Instance : BinderInfo

export
Eq BinderInfo where
  Default == Default = True
  Implicit == Implicit = True
  StrictImplicit == StrictImplicit = True
  Instance == Instance = True
  _ == _ = False

export
Show BinderInfo where
  show Default = "#BD"
  show Implicit = "#BI"
  show StrictImplicit = "#BS"
  show Instance = "#BC"

||| Well-scoped expressions indexed by the number of bound variables in scope
|||
||| @n The number of bound variables currently in scope
public export
data Expr : (n : Nat) -> Type where
  ||| Bound variable - de Bruijn index guaranteed to be in scope
  BVar : Fin n -> Expr n
  ||| Free variable (local) - used during type checking to represent
  ||| variables introduced by binders. Has a unique ID and a type.
  ||| Unlike BVar which uses de Bruijn indices, Local uses unique IDs
  ||| which makes comparison trivial (same ID = same variable).
  Local : (id : Nat) -> (userName : Name) -> Expr n
  ||| Sort (type universe)
  Sort : Level -> Expr n
  ||| Constant reference with universe level instantiation
  Const : Name -> List Level -> Expr n
  ||| Function application
  App : Expr n -> Expr n -> Expr n
  ||| Lambda abstraction: λ (x : A). body
  ||| The body has one more variable in scope
  Lam : (binderName : Name) -> BinderInfo -> (binderType : Expr n) -> (body : Expr (S n)) -> Expr n
  ||| Pi type (dependent function type): (x : A) -> B
  ||| The codomain has one more variable in scope
  Pi : (binderName : Name) -> BinderInfo -> (binderType : Expr n) -> (body : Expr (S n)) -> Expr n
  ||| Let binding: let x : A := v in body
  Let : (binderName : Name) -> (binderType : Expr n) -> (val : Expr n) -> (body : Expr (S n)) -> Expr n
  ||| Primitive projection from a structure
  Proj : (structName : Name) -> (fieldIdx : Nat) -> (struct : Expr n) -> Expr n
  ||| Natural number literal
  NatLit : Nat -> Expr n
  ||| String literal
  StringLit : String -> Expr n

%name Expr e, e1, e2, f, g

||| A closed expression has no free de Bruijn variables
public export
ClosedExpr : Type
ClosedExpr = Expr 0

||| Shift a Fin by m (adding m to the index)
shiftFin : (m : Nat) -> Fin n -> Fin (n + m)
shiftFin m FZ = FZ
shiftFin m (FS i) = FS (shiftFin m i)

||| Weaken an expression to a larger scope
||| Shifts all de Bruijn indices up
public export
weaken : {m : Nat} -> Expr n -> Expr (n + m)
weaken (BVar i) = BVar (shiftFin m i)
weaken (Local id name) = Local id name
weaken (Sort l) = Sort l
weaken (Const name lvls) = Const name lvls
weaken (App f x) = App (weaken f) (weaken x)
weaken (Lam name bi ty body) = Lam name bi (weaken ty) (weaken body)
weaken (Pi name bi ty body) = Pi name bi (weaken ty) (weaken body)
weaken (Let name ty val body) = Let name (weaken ty) (weaken val) (weaken body)
weaken (Proj sname idx s) = Proj sname idx (weaken s)
weaken (NatLit k) = NatLit k
weaken (StringLit s) = StringLit s

||| Shift a Fin by 1
shiftFin1 : Fin n -> Fin (S n)
shiftFin1 FZ = FZ
shiftFin1 (FS i) = FS (shiftFin1 i)

||| Weaken by 1 - most common case
public export
weaken1 : Expr n -> Expr (S n)
weaken1 (BVar i) = BVar (shiftFin1 i)
weaken1 (Local id name) = Local id name
weaken1 (Sort l) = Sort l
weaken1 (Const name lvls) = Const name lvls
weaken1 (App f x) = App (weaken1 f) (weaken1 x)
weaken1 (Lam name bi ty body) = Lam name bi (weaken1 ty) (weaken1 body)
weaken1 (Pi name bi ty body) = Pi name bi (weaken1 ty) (weaken1 body)
weaken1 (Let name ty val body) = Let name (weaken1 ty) (weaken1 val) (weaken1 body)
weaken1 (Proj sname idx s) = Proj sname idx (weaken1 s)
weaken1 (NatLit k) = NatLit k
weaken1 (StringLit s) = StringLit s

-- For comparing expressions we need Eq on Fin
eqFin : Fin n -> Fin m -> Bool
eqFin FZ FZ = True
eqFin (FS i) (FS j) = eqFin i j
eqFin _ _ = False

||| Syntactic equality of expressions (ignoring binder names)
export
exprEq : Expr n -> Expr m -> Bool
exprEq (BVar i) (BVar j) = eqFin i j
exprEq (Local id1 _) (Local id2 _) = id1 == id2
exprEq (Sort l1) (Sort l2) = l1 == l2
exprEq (Const n1 ls1) (Const n2 ls2) = n1 == n2 && ls1 == ls2
exprEq (App f1 x1) (App f2 x2) = exprEq f1 f2 && exprEq x1 x2
exprEq (Lam _ bi1 ty1 b1) (Lam _ bi2 ty2 b2) = bi1 == bi2 && exprEq ty1 ty2 && exprEq b1 b2
exprEq (Pi _ bi1 ty1 b1) (Pi _ bi2 ty2 b2) = bi1 == bi2 && exprEq ty1 ty2 && exprEq b1 b2
exprEq (Let _ ty1 v1 b1) (Let _ ty2 v2 b2) = exprEq ty1 ty2 && exprEq v1 v2 && exprEq b1 b2
exprEq (Proj n1 i1 s1) (Proj n2 i2 s2) = n1 == n2 && i1 == i2 && exprEq s1 s2
exprEq (NatLit n1) (NatLit n2) = n1 == n2
exprEq (StringLit s1) (StringLit s2) = s1 == s2
exprEq _ _ = False

export
Eq (Expr n) where
  (==) = exprEq

-- Helper to compare Fin values
compareFin : Fin n -> Fin m -> Ordering
compareFin FZ FZ = EQ
compareFin FZ (FS _) = LT
compareFin (FS _) FZ = GT
compareFin (FS i) (FS j) = compareFin i j

-- Compare BinderInfo
compareBinderInfo : BinderInfo -> BinderInfo -> Ordering
compareBinderInfo Default Default = EQ
compareBinderInfo Default _ = LT
compareBinderInfo _ Default = GT
compareBinderInfo Implicit Implicit = EQ
compareBinderInfo Implicit _ = LT
compareBinderInfo _ Implicit = GT
compareBinderInfo StrictImplicit StrictImplicit = EQ
compareBinderInfo StrictImplicit _ = LT
compareBinderInfo _ StrictImplicit = GT
compareBinderInfo Instance Instance = EQ

||| Structural comparison of expressions
export covering
exprCompare : Expr n -> Expr m -> Ordering
exprCompare (BVar i) (BVar j) = compareFin i j
exprCompare (BVar _) _ = LT
exprCompare _ (BVar _) = GT
exprCompare (Local id1 _) (Local id2 _) = compare id1 id2
exprCompare (Local _ _) _ = LT
exprCompare _ (Local _ _) = GT
exprCompare (Sort l1) (Sort l2) = compare l1 l2
exprCompare (Sort _) _ = LT
exprCompare _ (Sort _) = GT
exprCompare (Const n1 ls1) (Const n2 ls2) =
  case compare n1 n2 of
    EQ => compare ls1 ls2
    c => c
exprCompare (Const _ _) _ = LT
exprCompare _ (Const _ _) = GT
exprCompare (App f1 x1) (App f2 x2) =
  case exprCompare f1 f2 of
    EQ => exprCompare x1 x2
    c => c
exprCompare (App _ _) _ = LT
exprCompare _ (App _ _) = GT
exprCompare (Lam _ bi1 ty1 b1) (Lam _ bi2 ty2 b2) =
  case compareBinderInfo bi1 bi2 of
    EQ => case exprCompare ty1 ty2 of
            EQ => exprCompare b1 b2
            c => c
    c => c
exprCompare (Lam _ _ _ _) _ = LT
exprCompare _ (Lam _ _ _ _) = GT
exprCompare (Pi _ bi1 ty1 b1) (Pi _ bi2 ty2 b2) =
  case compareBinderInfo bi1 bi2 of
    EQ => case exprCompare ty1 ty2 of
            EQ => exprCompare b1 b2
            c => c
    c => c
exprCompare (Pi _ _ _ _) _ = LT
exprCompare _ (Pi _ _ _ _) = GT
exprCompare (Let _ ty1 v1 b1) (Let _ ty2 v2 b2) =
  case exprCompare ty1 ty2 of
    EQ => case exprCompare v1 v2 of
            EQ => exprCompare b1 b2
            c => c
    c => c
exprCompare (Let _ _ _ _) _ = LT
exprCompare _ (Let _ _ _ _) = GT
exprCompare (Proj n1 i1 s1) (Proj n2 i2 s2) =
  case compare n1 n2 of
    EQ => case compare i1 i2 of
            EQ => exprCompare s1 s2
            c => c
    c => c
exprCompare (Proj _ _ _) _ = LT
exprCompare _ (Proj _ _ _) = GT
exprCompare (NatLit n1) (NatLit n2) = compare n1 n2
exprCompare (NatLit _) _ = LT
exprCompare _ (NatLit _) = GT
exprCompare (StringLit s1) (StringLit s2) = compare s1 s2

export covering
Ord (Expr n) where
  compare = exprCompare

||| Is this expression a sort?
public export
isSort : Expr n -> Bool
isSort (Sort _) = True
isSort _ = False

||| Is this expression a Pi type?
public export
isPi : Expr n -> Bool
isPi (Pi _ _ _ _) = True
isPi _ = False

||| Is this expression a lambda?
public export
isLam : Expr n -> Bool
isLam (Lam _ _ _ _) = True
isLam _ = False

||| Is this expression an application?
public export
isApp : Expr n -> Bool
isApp (App _ _) = True
isApp _ = False

||| Get the head of an application spine
||| e.g., for `f a b c` returns `f`
public export
getAppFn : Expr n -> Expr n
getAppFn (App f _) = getAppFn f
getAppFn e = e

||| Get arguments of an application spine
||| e.g., for `f a b c` returns `[a, b, c]`
public export
getAppArgs : Expr n -> List (Expr n)
getAppArgs = go []
  where
    go : List (Expr n) -> Expr n -> List (Expr n)
    go acc (App f x) = go (x :: acc) f
    go acc _ = acc

||| Build an application from a function and list of arguments
public export
mkApp : Expr n -> List (Expr n) -> Expr n
mkApp f [] = f
mkApp f (x :: xs) = mkApp (App f x) xs

||| Collect all free constants referenced in an expression
public export
freeConsts : Expr n -> List Name
freeConsts (BVar _) = []
freeConsts (Local _ _) = []
freeConsts (Sort _) = []
freeConsts (Const name _) = [name]
freeConsts (App f x) = freeConsts f ++ freeConsts x
freeConsts (Lam _ _ ty body) = freeConsts ty ++ freeConsts body
freeConsts (Pi _ _ ty body) = freeConsts ty ++ freeConsts body
freeConsts (Let _ ty val body) = freeConsts ty ++ freeConsts val ++ freeConsts body
freeConsts (Proj _ _ s) = freeConsts s
freeConsts (NatLit _) = []
freeConsts (StringLit _) = []

||| Collect all universe level parameters in an expression
public export
levelParams : Expr n -> List Name
levelParams (BVar _) = []
levelParams (Local _ _) = []
levelParams (Sort l) = Level.params l
levelParams (Const _ ls) = concatMap Level.params ls
levelParams (App f x) = levelParams f ++ levelParams x
levelParams (Lam _ _ ty body) = levelParams ty ++ levelParams body
levelParams (Pi _ _ ty body) = levelParams ty ++ levelParams body
levelParams (Let _ ty val body) = levelParams ty ++ levelParams val ++ levelParams body
levelParams (Proj _ _ s) = levelParams s
levelParams (NatLit _) = []
levelParams (StringLit _) = []
