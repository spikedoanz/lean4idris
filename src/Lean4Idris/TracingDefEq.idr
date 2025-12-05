||| Tracing version of definitional equality checking
|||
||| Provides isDefEq with tree-structured recording of all comparisons.
module Lean4Idris.TracingDefEq

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Subst
import Lean4Idris.Pretty
import Lean4Idris.Trace
import Lean4Idris.TypeChecker
import Data.SortedMap
import Data.List
import Data.String

%default covering

------------------------------------------------------------------------
-- Helper: Pretty print expression for trace
------------------------------------------------------------------------

ppExpr' : ClosedExpr -> String
ppExpr' e = ppExpr initPPContext e

------------------------------------------------------------------------
-- Traced DefEq Result
------------------------------------------------------------------------

||| Result of traced isDefEq: (result, trace node)
public export
DefEqResult : Type
DefEqResult = Either TCError (Bool, DefEqNode)

------------------------------------------------------------------------
-- Tracing isDefEq
------------------------------------------------------------------------

||| Definitional equality with tracing
||| Returns the comparison result and a tree of all sub-comparisons
export
isDefEqTraced : TCEnv -> ClosedExpr -> ClosedExpr -> DefEqResult
isDefEqTraced env e1 e2 = do
  -- First reduce both to WHNF
  e1' <- whnf env e1
  e2' <- whnf env e2
  -- Record the WHNF step if anything changed
  let lhsWhnf = if ppExpr' e1 == ppExpr' e1' then Nothing else Just (ppExpr' e1')
  let rhsWhnf = if ppExpr' e2 == ppExpr' e2' then Nothing else Just (ppExpr' e2')
  -- Compare in WHNF
  (result, children) <- isDefEqWhnf e1' e2'
  -- Determine the kind based on expression structure
  let kind = getKind e1' e2'
  let node = MkDefEqNode kind (ppExpr' e1) (ppExpr' e2) lhsWhnf rhsWhnf result children ""
  Right (result, node)
  where
    getKind : ClosedExpr -> ClosedExpr -> DefEqKind
    getKind (Sort _) (Sort _) = EqSort
    getKind (Const _ _) (Const _ _) = EqConst
    getKind (App _ _) (App _ _) = EqApp
    getKind (Lam _ _ _ _) (Lam _ _ _ _) = EqLam
    getKind (Pi _ _ _ _) (Pi _ _ _ _) = EqPi
    getKind (Let _ _ _ _) (Let _ _ _ _) = EqLet
    getKind (Proj _ _ _) (Proj _ _ _) = EqProj
    getKind (NatLit _) (NatLit _) = EqLit
    getKind (StringLit _) (StringLit _) = EqLit
    getKind _ _ = EqConst  -- fallback for mismatched structures

    -- Helper to run isDefEq and extract result/children
    isDefEqWhnf : ClosedExpr -> ClosedExpr -> Either TCError (Bool, List DefEqNode)

    -- Sort comparison
    isDefEqWhnf (Sort l1) (Sort l2) =
      let result = levelEq l1 l2
      in Right (result, [])

    -- Const comparison
    isDefEqWhnf (Const n1 ls1) (Const n2 ls2) =
      if n1 == n2 && levelListEq ls1 ls2
        then Right (True, [])
        else Right (False, [])

    -- App: compare function and argument
    isDefEqWhnf (App f1 a1) (App f2 a2) = do
      (fRes, fNode) <- isDefEqTraced env f1 f2
      if fRes
        then do
          (aRes, aNode) <- isDefEqTraced env a1 a2
          Right (aRes, [fNode, aNode])
        else Right (False, [fNode])

    -- Lam: compare type and body
    isDefEqWhnf (Lam name1 _ ty1 body1) (Lam _ _ ty2 body2) = do
      (tyRes, tyNode) <- isDefEqTraced env ty1 ty2
      if tyRes
        then do
          -- Use real isDefEq for body comparison (placeholder substitution happens there)
          bodyResult <- isDefEqBodyWithNameAndType name1 ty1 isDefEq env body1 body2
          Right (bodyResult, [tyNode])
        else Right (False, [tyNode])

    -- Pi: compare domain and codomain
    isDefEqWhnf (Pi name1 _ dom1 cod1) (Pi _ _ dom2 cod2) = do
      (domRes, domNode) <- isDefEqTraced env dom1 dom2
      if domRes
        then do
          -- Use real isDefEq for codomain comparison
          codResult <- isDefEqBodyWithNameAndType name1 dom1 isDefEq env cod1 cod2
          Right (codResult, [domNode])
        else Right (False, [domNode])

    -- Let: compare type, value, and body
    isDefEqWhnf (Let name1 ty1 v1 b1) (Let _ ty2 v2 b2) = do
      (tyRes, tyNode) <- isDefEqTraced env ty1 ty2
      (vRes, vNode) <- isDefEqTraced env v1 v2
      if tyRes && vRes
        then do
          -- Use real isDefEq for body comparison
          bodyResult <- isDefEqBodyWithNameAndType name1 ty1 isDefEq env b1 b2
          Right (bodyResult, [tyNode, vNode])
        else Right (False, [tyNode, vNode])

    -- Proj: compare struct and index
    isDefEqWhnf (Proj sn1 i1 s1) (Proj sn2 i2 s2) =
      if sn1 == sn2 && i1 == i2
        then do
          (sRes, sNode) <- isDefEqTraced env s1 s2
          Right (sRes, [sNode])
        else Right (False, [])

    -- Literals
    isDefEqWhnf (NatLit n1) (NatLit n2) = Right (n1 == n2, [])
    isDefEqWhnf (StringLit s1) (StringLit s2) = Right (s1 == s2, [])

    -- Mismatched constructors
    isDefEqWhnf _ _ = Right (False, [])

------------------------------------------------------------------------
-- Convenience Functions
------------------------------------------------------------------------

||| Run isDefEq and format trace as text
export
isDefEqTraceText : TCEnv -> ClosedExpr -> ClosedExpr -> Either TCError String
isDefEqTraceText env e1 e2 = do
  (_, node) <- isDefEqTraced env e1 e2
  Right (ppDefEqNode 0 node)

||| Run isDefEq and format trace as JSON
export
isDefEqTraceJSON : TCEnv -> ClosedExpr -> ClosedExpr -> Either TCError String
isDefEqTraceJSON env e1 e2 = do
  (_, node) <- isDefEqTraced env e1 e2
  Right (defEqNodeToJSON node)

||| Run isDefEq and format trace as HTML
export
isDefEqTraceHTML : TCEnv -> ClosedExpr -> ClosedExpr -> Either TCError String
isDefEqTraceHTML env e1 e2 = do
  (_, node) <- isDefEqTraced env e1 e2
  Right (defEqToFullHTML node)
