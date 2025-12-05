||| Tracing version of WHNF reduction
|||
||| Provides whnf with step-by-step recording of all reductions.
module Lean4Idris.TracingWhnf

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
-- Tracing State
------------------------------------------------------------------------

||| Result of a traced reduction: either error or (result, trace)
public export
TracedResult : Type -> Type
TracedResult a = Either TCError (a, Trace)

||| Run a traced computation
runTraced : Trace -> (Trace -> TracedResult a) -> TracedResult a
runTraced t f = f t

------------------------------------------------------------------------
-- Helper: Pretty print expression for trace
------------------------------------------------------------------------

ppExprForTrace : ClosedExpr -> String
ppExprForTrace e = ppExpr initPPContext e

------------------------------------------------------------------------
-- Tracing WHNF
------------------------------------------------------------------------

||| Record a reduction step and return the result
recordStep : ReductionRule -> String -> ClosedExpr -> ClosedExpr -> Trace -> (ClosedExpr, Trace)
recordStep rule loc before after trace =
  let step = MkStep rule (ppExprForTrace before) (ppExprForTrace after) loc
  in (after, addStep step trace)

||| Weak head normal form with tracing
|||
||| Returns the reduced expression and a trace of all reduction steps.
export
whnfTraced : TCEnv -> ClosedExpr -> TracedResult ClosedExpr
whnfTraced env e = whnfFuel 20 e emptyTrace
  where
    ||| Try beta reduction: (λx.body) arg → body[x := arg]
    tryBeta : ClosedExpr -> Maybe ClosedExpr
    tryBeta (App (Lam _ _ _ body) arg) = Just (instantiate1 (believe_me body) arg)
    tryBeta _ = Nothing

    ||| Try let substitution: let x = v in body → body[x := v]
    tryLet : ClosedExpr -> Maybe ClosedExpr
    tryLet (Let _ _ val body) = Just (instantiate1 (believe_me body) val)
    tryLet _ = Nothing

    ||| Try delta reduction: unfold constant head
    tryDelta : ClosedExpr -> Maybe (Name, ClosedExpr)
    tryDelta e' =
      case unfoldHead env e' of
        Just e'' =>
          -- Extract the constant name that was unfolded
          let name = case e' of
                       Const n _ => n
                       App f _ => case getHead f of
                                    Just n => n
                                    Nothing => Anonymous
                       _ => Anonymous
          in Just (name, e'')
        Nothing => Nothing
      where
        getHead : ClosedExpr -> Maybe Name
        getHead (Const n _) = Just n
        getHead (App f _) = getHead f
        getHead _ = Nothing

    ||| Single step with tracing
    whnfStepTraced : ClosedExpr -> String -> Trace -> Maybe (ClosedExpr, Trace)
    whnfStepTraced expr loc trace =
      -- Try beta
      case tryBeta expr of
        Just e' => Just (recordStep Beta loc expr e' trace)
        Nothing =>
          -- Try let
          case tryLet expr of
            Just e' => Just (recordStep LetSubst loc expr e' trace)
            Nothing =>
              -- Try delta
              case tryDelta expr of
                Just (name, e') => Just (recordStep (Delta name) loc expr e' trace)
                Nothing => Nothing

    ||| Reduce nested application head
    reduceAppHeadTraced : ClosedExpr -> Trace -> Maybe (ClosedExpr, Trace)
    reduceAppHeadTraced (App f arg) trace =
      case reduceAppHeadTraced f trace of
        Just (f', trace') => Just (App f' arg, trace')
        Nothing =>
          case whnfStepTraced f "app-head" trace of
            Just (f', trace') => Just (App f' arg, trace')
            Nothing => Nothing
    reduceAppHeadTraced _ _ = Nothing

    ||| Main fuel-limited loop
    whnfFuel : Nat -> ClosedExpr -> Trace -> TracedResult ClosedExpr
    whnfFuel 0 e trace = Right (e, trace)  -- out of fuel
    whnfFuel (S k) e trace =
      -- Try beta/let at top level
      case whnfStepTraced e "top" trace of
        Just (e', trace') => whnfFuel k e' trace'
        Nothing =>
          -- Try reducing application head
          case reduceAppHeadTraced e trace of
            Just (e', trace') => whnfFuel k e' trace'
            Nothing => Right (e, trace)  -- no more reductions

------------------------------------------------------------------------
-- Convenience Functions
------------------------------------------------------------------------

||| Run whnf and get just the trace
export
getWhnfTrace : TCEnv -> ClosedExpr -> Either TCError Trace
getWhnfTrace env e = map snd (whnfTraced env e)

||| Run whnf and format trace as text
export
whnfTraceText : TCEnv -> ClosedExpr -> Either TCError String
whnfTraceText env e = map (ppTrace . snd) (whnfTraced env e)

||| Run whnf and format trace as JSON
export
whnfTraceJSON : TCEnv -> ClosedExpr -> Either TCError String
whnfTraceJSON env e = map (traceToJSON . snd) (whnfTraced env e)

||| Run whnf and format trace as HTML
export
whnfTraceHTML : TCEnv -> ClosedExpr -> Either TCError String
whnfTraceHTML env e = map (traceToHTML . snd) (whnfTraced env e)
