||| Parser for the lean4export format
|||
||| Parses export files into AST types. The export format uses indices
||| to refer to previously defined names, levels, and expressions.
module Lean4Idris.Export.Parser

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Export.Token
import Lean4Idris.Export.Lexer
import Data.Fin
import Data.List
import Data.Maybe
import Data.SortedMap

%default total

||| Parser state: maps from indices to parsed entities
public export
record ParseState where
  constructor MkParseState
  names : SortedMap Nat Name
  levels : SortedMap Nat Level
  exprs : SortedMap Nat ClosedExpr

||| Initial parse state with index 0 pre-populated
export
initState : ParseState
initState = MkParseState
  (singleton 0 Anonymous)
  (singleton 0 Zero)
  empty

||| Parser result
public export
Result : Type -> Type
Result a = Either String (a, List Token)

||| Expect a natural number token
expectNat : List Token -> Result Nat
expectNat [] = Left "Unexpected EOF, expecting nat"
expectNat (TNat n :: rest) = Right (n, rest)
expectNat (t :: _) = Left $ "Expected nat, got " ++ show t

||| Expect an identifier token
expectIdent : List Token -> Result String
expectIdent [] = Left "Unexpected EOF, expecting ident"
expectIdent (TIdent s :: rest) = Right (s, rest)
expectIdent (TNat n :: rest) = Right (show n, rest)
expectIdent (t :: _) = Left $ "Expected ident, got " ++ show t

||| Expect a specific command
expectCommand : Command -> List Token -> Result ()
expectCommand cmd [] = Left $ "Unexpected EOF, expecting " ++ show cmd
expectCommand cmd (TCommand c :: rest) =
  if c == cmd then Right ((), rest)
  else Left $ "Expected " ++ show cmd ++ ", got " ++ show c
expectCommand cmd (t :: _) = Left $ "Expected " ++ show cmd ++ ", got " ++ show t

||| Skip newline tokens
skipNewlines : List Token -> List Token
skipNewlines [] = []
skipNewlines (TNewline :: rest) = skipNewlines rest
skipNewlines toks = toks

||| Look up a name by index
lookupName : ParseState -> Nat -> Either String Name
lookupName st idx =
  case lookup idx st.names of
    Just n => Right n
    Nothing => Left $ "Invalid name index: " ++ show idx

||| Look up a level by index
lookupLevel : ParseState -> Nat -> Either String Level
lookupLevel st idx =
  case lookup idx st.levels of
    Just l => Right l
    Nothing => Left $ "Invalid level index: " ++ show idx

||| Look up an expression by index
lookupExpr : ParseState -> Nat -> Either String ClosedExpr
lookupExpr st idx =
  case lookup idx st.exprs of
    Just e => Right e
    Nothing => Left $ "Invalid expr index: " ++ show idx

||| Parse a name command: idx #NS parent_idx string | idx #NI parent_idx nat
parseNameCmd : ParseState -> Nat -> List Token -> Result ParseState
parseNameCmd st idx (TCommand NS :: rest) = do
  (parentIdx, rest1) <- expectNat rest
  (seg, rest2) <- expectIdent rest1
  parent <- lookupName st parentIdx
  Right ({ names $= insert idx (Str seg parent) } st, rest2)
parseNameCmd st idx (TCommand NI :: rest) = do
  (parentIdx, rest1) <- expectNat rest
  (num, rest2) <- expectNat rest1
  parent <- lookupName st parentIdx
  Right ({ names $= insert idx (Num num parent) } st, rest2)
parseNameCmd _ _ toks = Left $ "Expected name command, got " ++ show (take 3 toks)

||| Parse a level command
parseLevelCmd : ParseState -> Nat -> List Token -> Result ParseState
parseLevelCmd st idx (TCommand US :: rest) = do
  (argIdx, rest1) <- expectNat rest
  l <- lookupLevel st argIdx
  Right ({ levels $= insert idx (Succ l) } st, rest1)
parseLevelCmd st idx (TCommand UM :: rest) = do
  (idx1, rest1) <- expectNat rest
  (idx2, rest2) <- expectNat rest1
  l1 <- lookupLevel st idx1
  l2 <- lookupLevel st idx2
  Right ({ levels $= insert idx (Max l1 l2) } st, rest2)
parseLevelCmd st idx (TCommand UIM :: rest) = do
  (idx1, rest1) <- expectNat rest
  (idx2, rest2) <- expectNat rest1
  l1 <- lookupLevel st idx1
  l2 <- lookupLevel st idx2
  Right ({ levels $= insert idx (IMax l1 l2) } st, rest2)
parseLevelCmd st idx (TCommand UP :: rest) = do
  (nameIdx, rest1) <- expectNat rest
  n <- lookupName st nameIdx
  Right ({ levels $= insert idx (Param n) } st, rest1)
parseLevelCmd _ _ toks = Left $ "Expected level command, got " ++ show (take 3 toks)

||| Parse universe level indices until non-nat token
parseLevelIndices : ParseState -> List Token -> (List Level, List Token)
parseLevelIndices st toks = go [] toks
  where
    go : List Level -> List Token -> (List Level, List Token)
    go acc [] = (reverse acc, [])
    go acc (TNat n :: rest) =
      case lookupLevel st n of
        Left _ => (reverse acc, TNat n :: rest)
        Right l => go (l :: acc) rest
    go acc toks' = (reverse acc, toks')

||| Parse an expression command
parseExprCmd : ParseState -> Nat -> List Token -> Result ParseState
parseExprCmd st idx (TCommand ES :: rest) = do
  (levelIdx, rest1) <- expectNat rest
  l <- lookupLevel st levelIdx
  Right ({ exprs $= insert idx (Sort l) } st, rest1)
parseExprCmd st idx (TCommand EC :: rest) = do
  (nameIdx, rest1) <- expectNat rest
  n <- lookupName st nameIdx
  let (lvls, rest2) = parseLevelIndices st rest1
  Right ({ exprs $= insert idx (Const n lvls) } st, rest2)
parseExprCmd st idx (TCommand EA :: rest) = do
  (fnIdx, rest1) <- expectNat rest
  (argIdx, rest2) <- expectNat rest1
  fn <- lookupExpr st fnIdx
  arg <- lookupExpr st argIdx
  Right ({ exprs $= insert idx (App fn arg) } st, rest2)
parseExprCmd st idx (TCommand ELN :: rest) = do
  (n, rest1) <- expectNat rest
  Right ({ exprs $= insert idx (NatLit n) } st, rest1)
parseExprCmd _ _ toks = Left $ "Expected expr command, got " ++ show (take 3 toks)

||| Parse a single indexed line (name, level, or expr definition)
parseIndexedLine : ParseState -> List Token -> Result ParseState
parseIndexedLine st toks = do
  (idx, rest1) <- expectNat toks
  case rest1 of
    TCommand NS :: _ => parseNameCmd st idx rest1
    TCommand NI :: _ => parseNameCmd st idx rest1
    TCommand US :: _ => parseLevelCmd st idx rest1
    TCommand UM :: _ => parseLevelCmd st idx rest1
    TCommand UIM :: _ => parseLevelCmd st idx rest1
    TCommand UP :: _ => parseLevelCmd st idx rest1
    TCommand ES :: _ => parseExprCmd st idx rest1
    TCommand EC :: _ => parseExprCmd st idx rest1
    TCommand EA :: _ => parseExprCmd st idx rest1
    TCommand ELN :: _ => parseExprCmd st idx rest1
    -- Skip other commands for now
    _ => Right (st, skipToNewline rest1)
  where
    skipToNewline : List Token -> List Token
    skipToNewline [] = []
    skipToNewline (TNewline :: rest) = rest
    skipToNewline (_ :: rest) = skipToNewline rest

||| Parse the version line: major.minor.patch
parseVersion : List Token -> Result (Nat, Nat, Nat)
parseVersion toks = do
  let toks' = skipNewlines toks
  (major, rest1) <- expectNat toks'
  (_, rest2) <- expectIdent rest1  -- '.'
  (minor, rest3) <- expectNat rest2
  (_, rest4) <- expectIdent rest3  -- '.'
  (patch, rest5) <- expectNat rest4
  Right ((major, minor, patch), skipNewlines rest5)

||| Parse all lines
partial
parseAllLines : ParseState -> List Token -> Either String ParseState
parseAllLines st [] = Right st
parseAllLines st (TNewline :: rest) = parseAllLines st rest
parseAllLines st (TCommand _ :: rest) =
  -- Skip declaration lines for now
  parseAllLines st (skipToNewline rest)
  where
    skipToNewline : List Token -> List Token
    skipToNewline [] = []
    skipToNewline (TNewline :: r) = r
    skipToNewline (_ :: r) = skipToNewline r
parseAllLines st toks@(TNat _ :: _) = do
  (st', rest) <- parseIndexedLine st toks
  parseAllLines st' (skipNewlines rest)
parseAllLines st (t :: _) = Left $ "Unexpected token: " ++ show t

||| Main parsing function
partial export
parseExport : String -> Either String ParseState
parseExport input = do
  tokens <- lexToTokens input
  ((major, minor, patch), rest) <- parseVersion tokens
  parseAllLines initState rest

||| Get all parsed names
export
getNames : ParseState -> List (Nat, Name)
getNames st = toList st.names

||| Get all parsed levels
export
getLevels : ParseState -> List (Nat, Level)
getLevels st = toList st.levels

||| Get all parsed expressions
export
getExprs : ParseState -> List (Nat, ClosedExpr)
getExprs st = toList st.exprs
