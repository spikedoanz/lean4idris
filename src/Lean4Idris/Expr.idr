||| Expressions for Lean 4
|||
||| Following lean4lean's approach, expressions are not indexed by scope depth.
||| De Bruijn indices are plain Nat values. Scope correctness is ensured by
||| the type checker operations rather than the type structure itself.
module Lean4Idris.Expr

import Lean4Idris.Name
import Lean4Idris.Level
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

||| Expressions (following lean4lean's flat approach)
public export
data Expr : Type where
  ||| Bound variable - de Bruijn index (0 = most recently bound)
  BVar : Nat -> Expr
  ||| Free variable (local) - used during type checking to represent
  ||| variables introduced by binders. Has a unique ID and a type.
  ||| Unlike BVar which uses de Bruijn indices, Local uses unique IDs
  ||| which makes comparison trivial (same ID = same variable).
  Local : (id : Nat) -> (userName : Name) -> Expr
  ||| Sort (type universe)
  Sort : Level -> Expr
  ||| Constant reference with universe level instantiation
  Const : Name -> List Level -> Expr
  ||| Function application
  App : Expr -> Expr -> Expr
  ||| Lambda abstraction: λ (x : A). body
  Lam : (binderName : Name) -> BinderInfo -> (binderType : Expr) -> (body : Expr) -> Expr
  ||| Pi type (dependent function type): (x : A) -> B
  Pi : (binderName : Name) -> BinderInfo -> (binderType : Expr) -> (body : Expr) -> Expr
  ||| Let binding: let x : A := v in body
  Let : (binderName : Name) -> (binderType : Expr) -> (val : Expr) -> (body : Expr) -> Expr
  ||| Primitive projection from a structure
  Proj : (structName : Name) -> (fieldIdx : Nat) -> (struct : Expr) -> Expr
  ||| Natural number literal
  NatLit : Nat -> Expr
  ||| String literal
  StringLit : String -> Expr

%name Expr e, e1, e2, f, g

||| Alias for documentation purposes - a "closed" expression
||| (no free BVars) is just a regular Expr. Scope correctness
||| is enforced by type checker operations.
public export
ClosedExpr : Type
ClosedExpr = Expr

||| Syntactic equality of expressions (ignoring binder names)
export
exprEq : Expr -> Expr -> Bool
exprEq (BVar i) (BVar j) = i == j
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
Eq Expr where
  (==) = exprEq

||| Is this expression a sort?
public export
isSort : Expr -> Bool
isSort (Sort _) = True
isSort _ = False

||| Is this expression a Pi type?
public export
isPi : Expr -> Bool
isPi (Pi _ _ _ _) = True
isPi _ = False

||| Is this expression a lambda?
public export
isLam : Expr -> Bool
isLam (Lam _ _ _ _) = True
isLam _ = False

||| Is this expression an application?
public export
isApp : Expr -> Bool
isApp (App _ _) = True
isApp _ = False

||| Get the head of an application spine
||| e.g., for `f a b c` returns `f`
public export
getAppFn : Expr -> Expr
getAppFn (App f _) = getAppFn f
getAppFn e = e

||| Get arguments of an application spine
||| e.g., for `f a b c` returns `[a, b, c]`
public export
getAppArgs : Expr -> List Expr
getAppArgs = go []
  where
    go : List Expr -> Expr -> List Expr
    go acc (App f x) = go (x :: acc) f
    go acc _ = acc

||| Build an application from a function and list of arguments
public export
mkApp : Expr -> List Expr -> Expr
mkApp f [] = f
mkApp f (x :: xs) = mkApp (App f x) xs

||| Collect all free constants referenced in an expression
public export
freeConsts : Expr -> List Name
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
levelParams : Expr -> List Name
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
