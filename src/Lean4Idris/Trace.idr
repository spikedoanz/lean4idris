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

------------------------------------------------------------------------
-- DefEq Comparison Events
------------------------------------------------------------------------

||| Type of definitional equality comparison
public export
data DefEqKind
  = EqSort              -- Sort vs Sort
  | EqConst             -- Const vs Const
  | EqApp               -- App vs App
  | EqLam               -- Lam vs Lam
  | EqPi                -- Pi vs Pi
  | EqLet               -- Let vs Let
  | EqProj              -- Proj vs Proj
  | EqLit               -- Literal comparison
  | EqPlaceholder       -- Placeholder equivalence
  | EqProofIrrel        -- Proof irrelevance
  | EqEta               -- Eta expansion

export
Show DefEqKind where
  show EqSort = "Sort"
  show EqConst = "Const"
  show EqApp = "App"
  show EqLam = "Lam"
  show EqPi = "Pi"
  show EqLet = "Let"
  show EqProj = "Proj"
  show EqLit = "Lit"
  show EqPlaceholder = "Placeholder"
  show EqProofIrrel = "ProofIrrel"
  show EqEta = "Eta"

||| A node in the DefEq comparison tree
||| Recursive structure captures nested comparisons
public export
data DefEqNode : Type where
  ||| A comparison between two expressions
  MkDefEqNode : (kind : DefEqKind)        -- What kind of comparison
             -> (lhs : String)             -- Left-hand side (pretty-printed)
             -> (rhs : String)             -- Right-hand side (pretty-printed)
             -> (lhsWhnf : Maybe String)   -- LHS after WHNF (if different)
             -> (rhsWhnf : Maybe String)   -- RHS after WHNF (if different)
             -> (result : Bool)            -- Comparison result
             -> (children : List DefEqNode) -- Sub-comparisons
             -> (note : String)            -- Additional info (e.g., binder name)
             -> DefEqNode

||| Smart constructor for DefEqNode
export
mkDefEqNode : DefEqKind -> String -> String -> Bool -> DefEqNode
mkDefEqNode k l r res = MkDefEqNode k l r Nothing Nothing res [] ""

||| Add WHNF results to a node
export
withWhnf : Maybe String -> Maybe String -> DefEqNode -> DefEqNode
withWhnf lw rw (MkDefEqNode k l r _ _ res ch n) = MkDefEqNode k l r lw rw res ch n

||| Add children to a node
export
withChildren : List DefEqNode -> DefEqNode -> DefEqNode
withChildren cs (MkDefEqNode k l r lw rw res _ n) = MkDefEqNode k l r lw rw res cs n

||| Add a note to a node
export
withNote : String -> DefEqNode -> DefEqNode
withNote note (MkDefEqNode k l r lw rw res ch _) = MkDefEqNode k l r lw rw res ch note

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

------------------------------------------------------------------------
-- DefEq Tree Output
------------------------------------------------------------------------

||| Make indentation string
indent : Nat -> String
indent n = pack (replicate (n * 2) ' ')

||| Pretty print a DefEqNode as text (tree format)
export
covering
ppDefEqNode : Nat -> DefEqNode -> String
ppDefEqNode depth (MkDefEqNode kind lhs rhs lhsWhnf rhsWhnf result children note) =
  let ind = indent depth
      resultStr = if result then "✓" else "✗"
      noteStr = if note == "" then "" else " [" ++ note ++ "]"
      whnfStr = case (lhsWhnf, rhsWhnf) of
                  (Just lw, Just rw) =>
                    if lw /= lhs || rw /= rhs
                      then "\n" ++ ind ++ "  ⇓ " ++ lw ++ "\n" ++ ind ++ "  ⇓ " ++ rw
                      else ""
                  (Just lw, Nothing) =>
                    if lw /= lhs then "\n" ++ ind ++ "  ⇓ " ++ lw else ""
                  (Nothing, Just rw) =>
                    if rw /= rhs then "\n" ++ ind ++ "  ⇓ " ++ rw else ""
                  _ => ""
      childStr = if null children then ""
                 else "\n" ++ unlines (map (ppDefEqNode (S depth)) children)
  in ind ++ resultStr ++ " " ++ show kind ++ noteStr ++ ": " ++ lhs ++ " =?= " ++ rhs ++ whnfStr ++ childStr

||| Convert DefEqNode to JSON
export
covering
defEqNodeToJSON : DefEqNode -> String
defEqNodeToJSON (MkDefEqNode kind lhs rhs lhsWhnf rhsWhnf result children note) =
  "{\"kind\": \"" ++ show kind ++ "\"" ++
  ", \"lhs\": \"" ++ escapeJSON lhs ++ "\"" ++
  ", \"rhs\": \"" ++ escapeJSON rhs ++ "\"" ++
  (case lhsWhnf of Just w => ", \"lhsWhnf\": \"" ++ escapeJSON w ++ "\""; Nothing => "") ++
  (case rhsWhnf of Just w => ", \"rhsWhnf\": \"" ++ escapeJSON w ++ "\""; Nothing => "") ++
  ", \"result\": " ++ (if result then "true" else "false") ++
  (if note == "" then "" else ", \"note\": \"" ++ escapeJSON note ++ "\"") ++
  ", \"children\": [" ++ joinBy ", " (map defEqNodeToJSON children) ++ "]}"

||| Convert DefEqNode to HTML
export
covering
defEqNodeToHTML : Nat -> DefEqNode -> String
defEqNodeToHTML depth (MkDefEqNode kind lhs rhs lhsWhnf rhsWhnf result children note) =
  let resultClass = if result then "success" else "failure"
      resultIcon = if result then "✓" else "✗"
      noteStr = if note == "" then "" else " <span class=\"note\">[" ++ escapeHTML note ++ "]</span>"
      marginLeft = show (depth * 20)
  in "<div class=\"defeq-node " ++ resultClass ++ "\" style=\"margin-left: " ++ marginLeft ++ "px;\">\n" ++
     "  <span class=\"result-icon\">" ++ resultIcon ++ "</span>\n" ++
     "  <span class=\"kind\">" ++ show kind ++ "</span>" ++ noteStr ++ "\n" ++
     "  <div class=\"comparison\">\n" ++
     "    <span class=\"lhs\">" ++ escapeHTML lhs ++ "</span>\n" ++
     "    <span class=\"eq-symbol\">=?=</span>\n" ++
     "    <span class=\"rhs\">" ++ escapeHTML rhs ++ "</span>\n" ++
     (case (lhsWhnf, rhsWhnf) of
        (Just lw, Just rw) =>
          if lw /= lhs || rw /= rhs
            then "    <div class=\"whnf\">⇓ " ++ escapeHTML lw ++ " =?= " ++ escapeHTML rw ++ "</div>\n"
            else ""
        _ => "") ++
     "  </div>\n" ++
     (if null children then ""
      else "  <div class=\"children\">\n" ++
           unlines (map (defEqNodeToHTML (S depth)) children) ++
           "  </div>\n") ++
     "</div>"
  where
    escapeHTML : String -> String
    escapeHTML s = pack (concatMap escapeChar (unpack s))
      where
        escapeChar : Char -> List Char
        escapeChar '<' = unpack "&lt;"
        escapeChar '>' = unpack "&gt;"
        escapeChar '&' = unpack "&amp;"
        escapeChar '"' = unpack "&quot;"
        escapeChar c = [c]

||| Full HTML page for DefEq trace
export
covering
defEqToFullHTML : DefEqNode -> String
defEqToFullHTML node = htmlHeader ++ defEqNodeToHTML 0 node ++ htmlFooter
  where
    htmlHeader : String
    htmlHeader = """
<!DOCTYPE html>
<html>
<head>
  <title>DefEq Trace</title>
  <style>
    body { font-family: 'Fira Code', monospace; margin: 20px; background: #1e1e1e; color: #d4d4d4; }
    .defeq-node { padding: 8px; margin: 4px 0; border-left: 3px solid #569cd6; background: #252526; }
    .defeq-node.success { border-left-color: #4ec9b0; }
    .defeq-node.failure { border-left-color: #f14c4c; }
    .result-icon { font-weight: bold; margin-right: 8px; }
    .success .result-icon { color: #4ec9b0; }
    .failure .result-icon { color: #f14c4c; }
    .kind { color: #569cd6; font-weight: bold; }
    .note { color: #9cdcfe; font-style: italic; }
    .comparison { margin: 4px 0 4px 20px; }
    .lhs { color: #ce9178; }
    .rhs { color: #b5cea8; }
    .eq-symbol { color: #569cd6; margin: 0 8px; }
    .whnf { color: #808080; font-style: italic; margin-top: 4px; }
    .children { margin-left: 10px; border-left: 1px dashed #444; padding-left: 10px; }
    h1 { color: #569cd6; }
  </style>
</head>
<body>
  <h1>DefEq Trace</h1>
"""

    htmlFooter : String
    htmlFooter = """
</body>
</html>
"""
