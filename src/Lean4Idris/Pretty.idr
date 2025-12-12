||| Pretty printing for Lean 4 AST
|||
||| Provides human-readable representations of expressions, levels, etc.
module Lean4Idris.Pretty

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Data.String
import Data.List

-- Pretty printing functions are not necessarily total due to recursive expressions

||| Pretty print a binder info
export
ppBinderInfo : BinderInfo -> String
ppBinderInfo Default = ""
ppBinderInfo Implicit = "implicit "
ppBinderInfo StrictImplicit = "strict implicit "
ppBinderInfo Instance = "instance "

||| Pretty print a level
export
ppLevel : Level -> String
ppLevel Zero = "0"
ppLevel (Succ l) = ppSucc 1 l
  where
    ppSucc : Nat -> Level -> String
    ppSucc n Zero = show n
    ppSucc n (Succ l') = ppSucc (S n) l'
    ppSucc n l' = ppLevel l' ++ "+" ++ show n
ppLevel (Max l1 l2) = "max " ++ ppLevel l1 ++ " " ++ ppLevel l2
ppLevel (IMax l1 l2) = "imax " ++ ppLevel l1 ++ " " ++ ppLevel l2
ppLevel (Param n) = show n

||| Pretty print universe level arguments
export
ppLevelArgs : List Level -> String
ppLevelArgs [] = ""
ppLevelArgs ls = ".{" ++ joinBy ", " (map ppLevel ls) ++ "}"

||| Context for pretty printing with named binders
public export
record PPContext where
  constructor MkPPContext
  binderNames : List Name
  indent : Nat

||| Initial context
export
initPPContext : PPContext
initPPContext = MkPPContext [] 0

||| Add a binder to context
export
addBinder : Name -> PPContext -> PPContext
addBinder n ctx = { binderNames $= (n ::) } ctx

||| Increase indent
export
indented : PPContext -> PPContext
indented ctx = { indent $= (+ 2) } ctx

||| Get indent string
indentStr : PPContext -> String
indentStr ctx = replicate ctx.indent ' '

||| Look up binder name by de Bruijn index
lookupBinder : PPContext -> Nat -> String
lookupBinder ctx i =
  case getAt i ctx.binderNames of
    Nothing => "#" ++ show i
    Just n => show n
  where
    getAt : Nat -> List a -> Maybe a
    getAt _ [] = Nothing
    getAt Z (x :: _) = Just x
    getAt (S k) (_ :: xs) = getAt k xs

||| Pretty print an expression
export
ppExpr : PPContext -> Expr -> String
ppExpr ctx (BVar i) = lookupBinder ctx i
ppExpr ctx (Local id name) = "?" ++ show name ++ "." ++ show id
ppExpr ctx (Sort l) = "Sort " ++ ppLevel l
ppExpr ctx (Const n ls) = show n ++ ppLevelArgs ls
ppExpr ctx (App f x) = ppApp ctx f [x]
  where
    ppApp : PPContext -> Expr -> List Expr -> String
    ppApp ctx' (App f' x') args = ppApp ctx' f' (x' :: args)
    ppApp ctx' f' args = "(" ++ ppExpr ctx' f' ++ " " ++
                         joinBy " " (map (ppExpr ctx') args) ++ ")"
ppExpr ctx (Lam name bi ty body) =
  let ctx' = addBinder name ctx
  in "(fun (" ++ show name ++ " : " ++ ppExpr ctx ty ++ ") => " ++
     ppExpr ctx' body ++ ")"
ppExpr ctx (Pi name bi ty body) =
  let ctx' = addBinder name ctx
  in case name of
       Anonymous => "(" ++ ppExpr ctx ty ++ " -> " ++ ppExpr ctx' body ++ ")"
       _ => "((" ++ show name ++ " : " ++ ppExpr ctx ty ++ ") -> " ++
            ppExpr ctx' body ++ ")"
ppExpr ctx (Let name ty val body) =
  let ctx' = addBinder name ctx
  in "(let " ++ show name ++ " : " ++ ppExpr ctx ty ++
     " := " ++ ppExpr ctx val ++ " in " ++ ppExpr ctx' body ++ ")"
ppExpr ctx (Proj sname idx s) =
  ppExpr ctx s ++ "." ++ show idx
ppExpr ctx (NatLit n) = show n
ppExpr ctx (StringLit s) = show s

||| Pretty print a closed expression
export
ppClosedExpr : ClosedExpr -> String
ppClosedExpr = ppExpr initPPContext

||| Pretty print a declaration
export
ppDecl : Declaration -> String
ppDecl (AxiomDecl n ty params) =
  "axiom " ++ show n ++ ppLevelArgs (map Param params) ++ " : " ++ ppClosedExpr ty
ppDecl (DefDecl n ty val hint safety params) =
  show safety ++ " def " ++ show n ++ ppLevelArgs (map Param params) ++
  " : " ++ ppClosedExpr ty ++ " := " ++ ppClosedExpr val
ppDecl (ThmDecl n ty val params) =
  "theorem " ++ show n ++ ppLevelArgs (map Param params) ++
  " : " ++ ppClosedExpr ty ++ " := " ++ ppClosedExpr val
ppDecl (OpaqueDecl n ty val params) =
  "opaque " ++ show n ++ ppLevelArgs (map Param params) ++
  " : " ++ ppClosedExpr ty ++ " := " ++ ppClosedExpr val
ppDecl QuotDecl = "quot"
ppDecl (IndDecl info params) =
  "inductive " ++ show info.name ++ ppLevelArgs (map Param params) ++
  " : " ++ ppClosedExpr info.type ++ " where\n" ++
  joinBy "\n" (map (\c => "  | " ++ show c.name ++ " : " ++ ppClosedExpr c.type) info.constructors)
ppDecl (CtorDecl n ty ind _ _ _ params) =
  "constructor " ++ show n ++ " of " ++ show ind
ppDecl (RecDecl info params) =
  "recursor " ++ show info.name

||| Simplified expression printer (no context)
export
covering
Show Expr where
  show = ppExpr initPPContext
