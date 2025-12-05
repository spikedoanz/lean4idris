||| Reduction tracing for type checker visualization
|||
||| This module provides data structures and functions for recording
||| reduction steps during type checking, enabling visualization of
||| the reduction process.
module Lean4Idris.Trace

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Pretty
import Data.List
import Data.String

%default total

------------------------------------------------------------------------
-- Reduction Step Types
------------------------------------------------------------------------

||| The type of reduction rule applied
public export
data ReductionRule
  = Beta           -- (λx.body) arg → body[x := arg]
  | LetSubst       -- let x = v in body → body[x := v]
  | Delta Name     -- unfold constant definition
  | Iota Name      -- recursor reduction (with recursor name)
  | Proj Nat       -- projection reduction (with field index)
  | Quot Name      -- quotient reduction (Quot.lift or Quot.ind)

export
Show ReductionRule where
  show Beta = "β"
  show LetSubst = "let"
  show (Delta n) = "δ(" ++ show n ++ ")"
  show (Iota n) = "ι(" ++ show n ++ ")"
  show (Proj i) = "π(" ++ show i ++ ")"
  show (Quot n) = "quot(" ++ show n ++ ")"

||| A single reduction step
public export
record ReductionStep where
  constructor MkStep
  rule : ReductionRule
  before : String   -- Pretty-printed expression before
  after : String    -- Pretty-printed expression after
  location : String -- Where in the expression (e.g., "head", "arg", "body")

export
Show ReductionStep where
  show s = show s.rule ++ " @ " ++ s.location ++ ":\n  " ++ s.before ++ "\n  → " ++ s.after

------------------------------------------------------------------------
-- Trace Accumulator
------------------------------------------------------------------------

||| Accumulated trace of reduction steps
public export
record Trace where
  constructor MkTrace
  steps : List ReductionStep
  depth : Nat  -- Current nesting depth for indentation

||| Empty trace
export
emptyTrace : Trace
emptyTrace = MkTrace [] 0

||| Add a step to the trace
export
addStep : ReductionStep -> Trace -> Trace
addStep s t = { steps $= (s ::) } t

||| Increase depth
export
enterScope : Trace -> Trace
enterScope t = { depth $= S } t

||| Decrease depth
predNat : Nat -> Nat
predNat Z = Z
predNat (S n) = n

export
exitScope : Trace -> Trace
exitScope t = { depth $= predNat } t

||| Get all steps in order (most recent last)
export
getSteps : Trace -> List ReductionStep
getSteps t = reverse t.steps

------------------------------------------------------------------------
-- Pretty Printing Traces
------------------------------------------------------------------------

||| Format a trace as plain text
export
ppTrace : Trace -> String
ppTrace t =
  let steps = getSteps t
      numbered = zip [1..length steps] steps
  in unlines (map ppNumberedStep numbered)
  where
    ppNumberedStep : (Nat, ReductionStep) -> String
    ppNumberedStep (n, s) =
      "[" ++ show n ++ "] " ++ show s.rule ++ " @ " ++ s.location ++ "\n" ++
      "    " ++ s.before ++ "\n" ++
      "  → " ++ s.after

------------------------------------------------------------------------
-- JSON Output for Visualization
------------------------------------------------------------------------

||| Escape a string for JSON
escapeJSON : String -> String
escapeJSON s = pack (concatMap escapeChar (unpack s))
  where
    escapeChar : Char -> List Char
    escapeChar '"' = ['\\', '"']
    escapeChar '\\' = ['\\', '\\']
    escapeChar '\n' = ['\\', 'n']
    escapeChar '\t' = ['\\', 't']
    escapeChar c = [c]

||| Convert a reduction rule to JSON
ruleToJSON : ReductionRule -> String
ruleToJSON Beta = "\"beta\""
ruleToJSON LetSubst = "\"let\""
ruleToJSON (Delta n) = "{\"delta\": \"" ++ escapeJSON (show n) ++ "\"}"
ruleToJSON (Iota n) = "{\"iota\": \"" ++ escapeJSON (show n) ++ "\"}"
ruleToJSON (Proj i) = "{\"proj\": " ++ show i ++ "}"
ruleToJSON (Quot n) = "{\"quot\": \"" ++ escapeJSON (show n) ++ "\"}"

||| Convert a step to JSON
stepToJSON : ReductionStep -> String
stepToJSON s =
  "{\"rule\": " ++ ruleToJSON s.rule ++
  ", \"before\": \"" ++ escapeJSON s.before ++
  "\", \"after\": \"" ++ escapeJSON s.after ++
  "\", \"location\": \"" ++ escapeJSON s.location ++ "\"}"

||| Convert a trace to JSON
export
traceToJSON : Trace -> String
traceToJSON t =
  let steps = getSteps t
  in "{\"steps\": [" ++ joinBy ", " (map stepToJSON steps) ++ "]}"

------------------------------------------------------------------------
-- HTML Output for Visualization
------------------------------------------------------------------------

||| Convert a trace to HTML for visualization
export
traceToHTML : Trace -> String
traceToHTML t =
  let steps = getSteps t
      numbered = zip [1..length steps] steps
  in htmlHeader ++ unlines (map stepToHTML numbered) ++ htmlFooter
  where
    htmlHeader : String
    htmlHeader = """
<!DOCTYPE html>
<html>
<head>
  <title>Reduction Trace</title>
  <style>
    body { font-family: 'Fira Code', monospace; margin: 20px; background: #1e1e1e; color: #d4d4d4; }
    .step { margin: 10px 0; padding: 10px; border-left: 3px solid #569cd6; background: #252526; }
    .step-number { color: #569cd6; font-weight: bold; }
    .rule { color: #4ec9b0; }
    .location { color: #9cdcfe; }
    .expr { font-family: 'Fira Code', monospace; white-space: pre-wrap; }
    .before { color: #ce9178; }
    .after { color: #b5cea8; }
    .arrow { color: #569cd6; font-size: 1.2em; }
    h1 { color: #569cd6; }
  </style>
</head>
<body>
  <h1>Reduction Trace</h1>
  <div class="trace">
"""

    htmlFooter : String
    htmlFooter = """
  </div>
</body>
</html>
"""

    escapeHTML : String -> String
    escapeHTML s = pack (concatMap escapeChar (unpack s))
      where
        escapeChar : Char -> List Char
        escapeChar '<' = unpack "&lt;"
        escapeChar '>' = unpack "&gt;"
        escapeChar '&' = unpack "&amp;"
        escapeChar '"' = unpack "&quot;"
        escapeChar c = [c]

    stepToHTML : (Nat, ReductionStep) -> String
    stepToHTML (n, s) =
      "    <div class=\"step\">\n" ++
      "      <span class=\"step-number\">[" ++ show n ++ "]</span> " ++
      "<span class=\"rule\">" ++ show s.rule ++ "</span> " ++
      "@ <span class=\"location\">" ++ escapeHTML s.location ++ "</span>\n" ++
      "      <div class=\"expr before\">" ++ escapeHTML s.before ++ "</div>\n" ++
      "      <div class=\"arrow\">→</div>\n" ++
      "      <div class=\"expr after\">" ++ escapeHTML s.after ++ "</div>\n" ++
      "    </div>"
