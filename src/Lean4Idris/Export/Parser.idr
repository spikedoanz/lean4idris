||| Parser for the lean4export format
|||
||| Parses export files into AST types. The export format uses indices
||| to refer to previously defined names, levels, and expressions.
module Lean4Idris.Export.Parser

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Decl
import Lean4Idris.Export.Token
import Lean4Idris.Export.Lexer
import Data.Fin
import Data.List
import Data.Maybe
import Data.SortedMap
import Decidable.Equality

%default total

------------------------------------------------------------------------
-- Scoped expression parsing
------------------------------------------------------------------------

||| An expression with unknown scope depth, stored as a function from depth
||| to an expression at that depth. This lets us delay the scope resolution.
public export
ScopedExpr : Type
ScopedExpr = (n : Nat) -> Maybe (Expr n)

||| A closed scoped expression (at depth 0)
export
closeScopedExpr : ScopedExpr -> Maybe ClosedExpr
closeScopedExpr f = f 0

------------------------------------------------------------------------
-- Recursor rule (intermediate representation)
------------------------------------------------------------------------

||| Recursor rule parsed from export
public export
record ParsedRecRule where
  constructor MkParsedRecRule
  ctorName : Name
  numFields : Nat
  rhs : ClosedExpr

------------------------------------------------------------------------
-- Parser state
------------------------------------------------------------------------

||| Parser state: maps from indices to parsed entities
public export
record ParseState where
  constructor MkParseState
  names : SortedMap Nat Name
  levels : SortedMap Nat Level
  exprs : SortedMap Nat ScopedExpr
  recRules : SortedMap Nat ParsedRecRule
  decls : List Declaration

||| Initial parse state with index 0 pre-populated
export
initState : ParseState
initState = MkParseState
  (singleton 0 Anonymous)
  (singleton 0 Zero)
  empty
  empty
  []

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

||| Look up a scoped expression by index
lookupScopedExpr : ParseState -> Nat -> Either String ScopedExpr
lookupScopedExpr st idx =
  case lookup idx st.exprs of
    Just e => Right e
    Nothing => Left $ "Invalid expr index: " ++ show idx

||| Look up an expression by index at a given scope depth
lookupExprAt : ParseState -> Nat -> (depth : Nat) -> Either String (Expr depth)
lookupExprAt st idx depth = do
  se <- lookupScopedExpr st idx
  case se depth of
    Just e => Right e
    Nothing => Left $ "Expression " ++ show idx ++ " invalid at depth " ++ show depth

||| Look up a closed expression by index
lookupExpr : ParseState -> Nat -> Either String ClosedExpr
lookupExpr st idx = lookupExprAt st idx 0

||| Look up a recursor rule by index
lookupRecRule : ParseState -> Nat -> Either String ParsedRecRule
lookupRecRule st idx =
  case lookup idx st.recRules of
    Just r => Right r
    Nothing => Left $ "Invalid rec rule index: " ++ show idx

||| Parse binder info token
parseBinderInfo : List Token -> Either String (BinderInfo, List Token)
parseBinderInfo (TCommand BD :: rest) = Right (Default, rest)
parseBinderInfo (TCommand BI :: rest) = Right (Implicit, rest)
parseBinderInfo (TCommand BS :: rest) = Right (StrictImplicit, rest)
parseBinderInfo (TCommand BC :: rest) = Right (Instance, rest)
parseBinderInfo toks = Left $ "Expected binder info, got " ++ show (take 1 toks)

||| Convert a natural number to Fin n, if possible
natToFinMaybe : (i : Nat) -> (n : Nat) -> Maybe (Fin n)
natToFinMaybe i n = case isLT i n of
  Yes prf => Just (natToFinLT i)
  No _ => Nothing

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

||| Weaken a closed expression to any depth
weakenToN : (n : Nat) -> ClosedExpr -> Expr n
weakenToN Z e = e
weakenToN (S k) e = weaken1 (weakenToN k e)

||| Make a scoped expression from a closed one (can be used at any depth)
liftClosed : ClosedExpr -> ScopedExpr
liftClosed e = \n => Just (weakenToN n e)

||| Parse an expression command
||| Expressions are stored as ScopedExpr to handle bound variables properly
parseExprCmd : ParseState -> Nat -> List Token -> Result ParseState

-- #EV i : bound variable with de Bruijn index i
parseExprCmd st idx (TCommand EV :: rest) = do
  (i, rest1) <- expectNat rest
  -- Create a scoped expr: at depth n, if i < n then BVar (natToFinLT i) else Nothing
  let scopedE : ScopedExpr = \n => do
        fin <- natToFinMaybe i n
        Just (BVar fin)
  Right ({ exprs $= insert idx scopedE } st, rest1)

-- #ES level : Sort level
parseExprCmd st idx (TCommand ES :: rest) = do
  (levelIdx, rest1) <- expectNat rest
  l <- lookupLevel st levelIdx
  Right ({ exprs $= insert idx (liftClosed (Sort l)) } st, rest1)

-- #EC name levels* : Const name [levels]
parseExprCmd st idx (TCommand EC :: rest) = do
  (nameIdx, rest1) <- expectNat rest
  n <- lookupName st nameIdx
  let (lvls, rest2) = parseLevelIndices st rest1
  Right ({ exprs $= insert idx (liftClosed (Const n lvls)) } st, rest2)

-- #EA fn arg : App fn arg
parseExprCmd st idx (TCommand EA :: rest) = do
  (fnIdx, rest1) <- expectNat rest
  (argIdx, rest2) <- expectNat rest1
  fnScoped <- lookupScopedExpr st fnIdx
  argScoped <- lookupScopedExpr st argIdx
  let scopedE : ScopedExpr = \n => do
        fn <- fnScoped n
        arg <- argScoped n
        Just (App fn arg)
  Right ({ exprs $= insert idx scopedE } st, rest2)

-- #EL binderInfo name domType body : Lam name binderInfo domType body
parseExprCmd st idx (TCommand EL :: rest) = do
  (bi, rest1) <- parseBinderInfo rest
  (nameIdx, rest2) <- expectNat rest1
  (domIdx, rest3) <- expectNat rest2
  (bodyIdx, rest4) <- expectNat rest3
  n <- lookupName st nameIdx
  domScoped <- lookupScopedExpr st domIdx
  bodyScoped <- lookupScopedExpr st bodyIdx
  let scopedE : ScopedExpr = \depth => do
        dom <- domScoped depth
        body <- bodyScoped (S depth)  -- body is at depth+1
        Just (Lam n bi dom body)
  Right ({ exprs $= insert idx scopedE } st, rest4)

-- #EP binderInfo name domType body : Pi name binderInfo domType body
parseExprCmd st idx (TCommand EP :: rest) = do
  (bi, rest1) <- parseBinderInfo rest
  (nameIdx, rest2) <- expectNat rest1
  (domIdx, rest3) <- expectNat rest2
  (bodyIdx, rest4) <- expectNat rest3
  n <- lookupName st nameIdx
  domScoped <- lookupScopedExpr st domIdx
  bodyScoped <- lookupScopedExpr st bodyIdx
  let scopedE : ScopedExpr = \depth => do
        dom <- domScoped depth
        body <- bodyScoped (S depth)  -- body is at depth+1
        Just (Pi n bi dom body)
  Right ({ exprs $= insert idx scopedE } st, rest4)

-- #EZ name type value body : Let name type value body
parseExprCmd st idx (TCommand EZ :: rest) = do
  (nameIdx, rest1) <- expectNat rest
  (tyIdx, rest2) <- expectNat rest1
  (valIdx, rest3) <- expectNat rest2
  (bodyIdx, rest4) <- expectNat rest3
  n <- lookupName st nameIdx
  tyScoped <- lookupScopedExpr st tyIdx
  valScoped <- lookupScopedExpr st valIdx
  bodyScoped <- lookupScopedExpr st bodyIdx
  let scopedE : ScopedExpr = \depth => do
        ty <- tyScoped depth
        val <- valScoped depth
        body <- bodyScoped (S depth)  -- body is at depth+1
        Just (Let n ty val body)
  Right ({ exprs $= insert idx scopedE } st, rest4)

-- #EJ structName fieldIdx expr : Proj structName fieldIdx expr
parseExprCmd st idx (TCommand EJ :: rest) = do
  (structNameIdx, rest1) <- expectNat rest
  (fieldIdx, rest2) <- expectNat rest1
  (exprIdx, rest3) <- expectNat rest2
  sn <- lookupName st structNameIdx
  exprScoped <- lookupScopedExpr st exprIdx
  let scopedE : ScopedExpr = \depth => do
        e <- exprScoped depth
        Just (Proj sn fieldIdx e)
  Right ({ exprs $= insert idx scopedE } st, rest3)

-- #ELN n : NatLit n
parseExprCmd st idx (TCommand ELN :: rest) = do
  (n, rest1) <- expectNat rest
  Right ({ exprs $= insert idx (liftClosed (NatLit n)) } st, rest1)

-- #ELS hexbytes : StringLit (decoded)
parseExprCmd st idx (TCommand ELS :: rest) = do
  -- For now, just collect hex tokens until newline and decode
  let (hexParts, rest1) = collectHex rest
  let s = decodeHexString hexParts
  Right ({ exprs $= insert idx (liftClosed (StringLit s)) } st, rest1)
  where
    collectHex : List Token -> (List String, List Token)
    collectHex (THex h :: rest') =
      let (more, rest'') = collectHex rest' in (h :: more, rest'')
    collectHex (TIdent h :: rest') =
      -- Sometimes hex is parsed as ident
      let (more, rest'') = collectHex rest' in (h :: more, rest'')
    collectHex rest' = ([], rest')

    hexCharToNat : Char -> Nat
    hexCharToNat c =
      if c >= '0' && c <= '9' then cast (ord c - ord '0')
      else if c >= 'A' && c <= 'F' then cast (ord c - ord 'A' + 10)
      else if c >= 'a' && c <= 'f' then cast (ord c - ord 'a' + 10)
      else 0

    decodeHexPair : String -> Maybe Char
    decodeHexPair s =
      case unpack s of
        [h1, h2] => Just (chr (cast (hexCharToNat h1 * 16 + hexCharToNat h2)))
        _ => Nothing

    decodeHexString : List String -> String
    decodeHexString parts = pack (mapMaybe decodeHexPair parts)

parseExprCmd _ _ toks = Left $ "Expected expr command, got " ++ show (take 3 toks)

||| Skip to end of line
skipToNewline : List Token -> List Token
skipToNewline [] = []
skipToNewline (TNewline :: rest) = rest
skipToNewline (_ :: rest) = skipToNewline rest

||| Parse N natural numbers
parseNNats : (n : Nat) -> List Token -> Either String (List Nat, List Token)
parseNNats Z toks = Right ([], toks)
parseNNats (S n) toks = do
  (x, rest1) <- expectNat toks
  (xs, rest2) <- parseNNats n rest1
  Right (x :: xs, rest2)

||| Parse a recursor rule: idx #RR ctorName numFields rhs
parseRecRuleCmd : ParseState -> Nat -> List Token -> Result ParseState
parseRecRuleCmd st idx (TCommand RR :: rest) = do
  (ctorNameIdx, rest1) <- expectNat rest
  (numFields, rest2) <- expectNat rest1
  (rhsIdx, rest3) <- expectNat rest2
  ctorName <- lookupName st ctorNameIdx
  rhs <- lookupExpr st rhsIdx
  let rule = MkParsedRecRule ctorName numFields rhs
  Right ({ recRules $= insert idx rule } st, rest3)
parseRecRuleCmd _ _ toks = Left $ "Expected #RR, got " ++ show (take 3 toks)

||| Parse a single indexed line (name, level, expr, or rec rule)
parseIndexedLine : ParseState -> List Token -> Result ParseState
parseIndexedLine st toks = do
  (idx, rest1) <- expectNat toks
  case rest1 of
    -- Names
    TCommand NS :: _ => parseNameCmd st idx rest1
    TCommand NI :: _ => parseNameCmd st idx rest1
    -- Levels
    TCommand US :: _ => parseLevelCmd st idx rest1
    TCommand UM :: _ => parseLevelCmd st idx rest1
    TCommand UIM :: _ => parseLevelCmd st idx rest1
    TCommand UP :: _ => parseLevelCmd st idx rest1
    -- Expressions
    TCommand EV :: _ => parseExprCmd st idx rest1
    TCommand ES :: _ => parseExprCmd st idx rest1
    TCommand EC :: _ => parseExprCmd st idx rest1
    TCommand EA :: _ => parseExprCmd st idx rest1
    TCommand EL :: _ => parseExprCmd st idx rest1
    TCommand EP :: _ => parseExprCmd st idx rest1
    TCommand EZ :: _ => parseExprCmd st idx rest1
    TCommand EJ :: _ => parseExprCmd st idx rest1
    TCommand ELN :: _ => parseExprCmd st idx rest1
    TCommand ELS :: _ => parseExprCmd st idx rest1
    -- Recursor rules
    TCommand RR :: _ => parseRecRuleCmd st idx rest1
    -- Skip unknown indexed commands
    _ => Right (st, skipToNewline rest1)

------------------------------------------------------------------------
-- Declaration parsing
------------------------------------------------------------------------

||| Parse reducibility hint: A, O, or R n
parseHint : List Token -> Either String (ReducibilityHint, List Token)
parseHint (TIdent "A" :: rest) = Right (Abbrev, rest)
parseHint (TIdent "O" :: rest) = Right (Opaq, rest)
parseHint (TIdent "R" :: rest) = do
  (n, rest1) <- expectNat rest
  Right (Regular n, rest1)
parseHint toks = Left $ "Expected hint (A/O/R), got " ++ show (take 1 toks)

||| Parse level param names from nat indices
parseLevelParamNames : ParseState -> List Nat -> Either String (List Name)
parseLevelParamNames st [] = Right []
parseLevelParamNames st (idx :: idxs) = do
  n <- lookupName st idx
  ns <- parseLevelParamNames st idxs
  Right (n :: ns)

||| Parse #AX name type levelParams*
parseAxiom : ParseState -> List Token -> Result ParseState
parseAxiom st (TCommand AX :: rest) = do
  (nameIdx, rest1) <- expectNat rest
  (typeIdx, rest2) <- expectNat rest1
  let (paramIdxs, rest3) = parseNatList rest2
  name <- lookupName st nameIdx
  ty <- lookupExpr st typeIdx
  params <- parseLevelParamNames st paramIdxs
  let decl = AxiomDecl name ty params
  Right ({ decls $= (decl ::) } st, rest3)
  where
    parseNatList : List Token -> (List Nat, List Token)
    parseNatList (TNat n :: rest') =
      let (more, rest'') = parseNatList rest' in (n :: more, rest'')
    parseNatList rest' = ([], rest')
parseAxiom _ toks = Left $ "Expected #AX, got " ++ show (take 1 toks)

||| Parse #DEF name type value hint levelParams*
parseDef : ParseState -> List Token -> Result ParseState
parseDef st (TCommand DEF :: rest) = do
  (nameIdx, rest1) <- expectNat rest
  (typeIdx, rest2) <- expectNat rest1
  (valueIdx, rest3) <- expectNat rest2
  (hint, rest4) <- parseHint rest3
  let (paramIdxs, rest5) = parseNatList rest4
  name <- lookupName st nameIdx
  ty <- lookupExpr st typeIdx
  val <- lookupExpr st valueIdx
  params <- parseLevelParamNames st paramIdxs
  let decl : Declaration = DefDecl name ty val hint Safe params
  Right ({ decls $= (decl ::) } st, rest5)
  where
    parseNatList : List Token -> (List Nat, List Token)
    parseNatList (TNat n :: rest') =
      let (more, rest'') = parseNatList rest' in (n :: more, rest'')
    parseNatList rest' = ([], rest')
parseDef _ toks = Left $ "Expected #DEF, got " ++ show (take 1 toks)

||| Parse #THM name type value levelParams*
parseThm : ParseState -> List Token -> Result ParseState
parseThm st (TCommand THM :: rest) = do
  (nameIdx, rest1) <- expectNat rest
  (typeIdx, rest2) <- expectNat rest1
  (valueIdx, rest3) <- expectNat rest2
  let (paramIdxs, rest4) = parseNatList rest3
  name <- lookupName st nameIdx
  ty <- lookupExpr st typeIdx
  val <- lookupExpr st valueIdx
  params <- parseLevelParamNames st paramIdxs
  let decl = ThmDecl name ty val params
  Right ({ decls $= (decl ::) } st, rest4)
  where
    parseNatList : List Token -> (List Nat, List Token)
    parseNatList (TNat n :: rest') =
      let (more, rest'') = parseNatList rest' in (n :: more, rest'')
    parseNatList rest' = ([], rest')
parseThm _ toks = Left $ "Expected #THM, got " ++ show (take 1 toks)

||| Parse #CTOR name type inductName ctorIdx numParams numFields levelParams*
parseCtor : ParseState -> List Token -> Result ParseState
parseCtor st (TCommand CTOR :: rest) = do
  (nameIdx, rest1) <- expectNat rest
  (typeIdx, rest2) <- expectNat rest1
  (inductIdx, rest3) <- expectNat rest2
  (ctorIdx, rest4) <- expectNat rest3
  (numParams, rest5) <- expectNat rest4
  (numFields, rest6) <- expectNat rest5
  let (paramIdxs, rest7) = parseNatList rest6
  name <- lookupName st nameIdx
  ty <- lookupExpr st typeIdx
  inductName <- lookupName st inductIdx
  params <- parseLevelParamNames st paramIdxs
  let decl = CtorDecl name ty inductName ctorIdx numParams numFields params
  Right ({ decls $= (decl ::) } st, rest7)
  where
    parseNatList : List Token -> (List Nat, List Token)
    parseNatList (TNat n :: rest') =
      let (more, rest'') = parseNatList rest' in (n :: more, rest'')
    parseNatList rest' = ([], rest')
parseCtor _ toks = Left $ "Expected #CTOR, got " ++ show (take 1 toks)

||| Parse #IND name type isReflexive isRec numNested numParams numIndices numInds indNames numCtors ctorNames levelParams*
parseInd : ParseState -> List Token -> Result ParseState
parseInd st (TCommand IND :: rest) = do
  (nameIdx, rest1) <- expectNat rest
  (typeIdx, rest2) <- expectNat rest1
  (isReflexive, rest3) <- expectNat rest2
  (isRec, rest4) <- expectNat rest3
  (numNested, rest5) <- expectNat rest4
  (numParams, rest6) <- expectNat rest5
  (numIndices, rest7) <- expectNat rest6
  (numInds, rest8) <- expectNat rest7
  result1 <- parseNNats numInds rest8
  let (indNameIdxs, rest9) = result1
  (numCtors, rest10) <- expectNat rest9
  result2 <- parseNNats numCtors rest10
  let (ctorNameIdxs, rest11) = result2
  let (paramIdxs, rest12) = parseNatList rest11
  name <- lookupName st nameIdx
  ty <- lookupExpr st typeIdx
  ctorNames <- traverse (\idx => lookupName st idx) ctorNameIdxs
  params <- parseLevelParamNames st paramIdxs
  -- Create constructor infos (types will be filled in when we see #CTOR)
  let ctorInfos = map (\cn => MkConstructorInfo cn (Sort Zero)) ctorNames  -- placeholder type
  let indInfo = MkInductiveInfo name ty numParams numIndices ctorInfos (isRec /= 0) (isReflexive /= 0)
  let decl = IndDecl indInfo params
  Right ({ decls $= (decl ::) } st, rest12)
  where
    parseNatList : List Token -> (List Nat, List Token)
    parseNatList (TNat n :: rest') =
      let (more, rest'') = parseNatList rest' in (n :: more, rest'')
    parseNatList rest' = ([], rest')
parseInd _ toks = Left $ "Expected #IND, got " ++ show (take 1 toks)

||| Parse #REC name type numInds indNames numParams numIndices numMotives numMinors numRules ruleIdxs k levelParams*
parseRec : ParseState -> List Token -> Result ParseState
parseRec st (TCommand REC :: rest) = do
  (nameIdx, rest1) <- expectNat rest
  (typeIdx, rest2) <- expectNat rest1
  (numInds, rest3) <- expectNat rest2
  result1 <- parseNNats numInds rest3
  let (indNameIdxs, rest4) = result1
  (numParams, rest5) <- expectNat rest4
  (numIndices, rest6) <- expectNat rest5
  (numMotives, rest7) <- expectNat rest6
  (numMinors, rest8) <- expectNat rest7
  (numRules, rest9) <- expectNat rest8
  result2 <- parseNNats numRules rest9
  let (ruleIdxs, rest10) = result2
  (k, rest11) <- expectNat rest10
  let (paramIdxs, rest12) = parseNatList rest11
  name <- lookupName st nameIdx
  ty <- lookupExpr st typeIdx
  params <- parseLevelParamNames st paramIdxs
  -- Look up recursor rules
  parsedRules <- traverse (\idx => lookupRecRule st idx) ruleIdxs
  let rules = map (\pr => MkRecursorRule pr.ctorName pr.numFields pr.rhs) parsedRules
  let recInfo = MkRecursorInfo name ty numParams numIndices numMotives numMinors rules (k /= 0)
  let decl = RecDecl recInfo params
  Right ({ decls $= (decl ::) } st, rest12)
  where
    parseNatList : List Token -> (List Nat, List Token)
    parseNatList (TNat n :: rest') =
      let (more, rest'') = parseNatList rest' in (n :: more, rest'')
    parseNatList rest' = ([], rest')
parseRec _ toks = Left $ "Expected #REC, got " ++ show (take 1 toks)

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
-- Declarations (non-indexed commands)
parseAllLines st toks@(TCommand AX :: _) = do
  (st', rest) <- parseAxiom st toks
  parseAllLines st' (skipNewlines rest)
parseAllLines st toks@(TCommand DEF :: _) = do
  (st', rest) <- parseDef st toks
  parseAllLines st' (skipNewlines rest)
parseAllLines st toks@(TCommand THM :: _) = do
  (st', rest) <- parseThm st toks
  parseAllLines st' (skipNewlines rest)
parseAllLines st toks@(TCommand IND :: _) = do
  (st', rest) <- parseInd st toks
  parseAllLines st' (skipNewlines rest)
parseAllLines st toks@(TCommand CTOR :: _) = do
  (st', rest) <- parseCtor st toks
  parseAllLines st' (skipNewlines rest)
parseAllLines st toks@(TCommand REC :: _) = do
  (st', rest) <- parseRec st toks
  parseAllLines st' (skipNewlines rest)
parseAllLines st toks@(TCommand QUOT :: _) = do
  -- #QUOT nameIdx typeIdx numArgs [rules...]
  -- This enables quotient types - just add QuotDecl to state
  let decl = QuotDecl
  parseAllLines ({ decls $= (decl ::) } st) (skipToNewline (drop 1 toks))
parseAllLines st (TCommand _ :: rest) =
  -- Skip other declaration lines (OPAQ, ABBREV, etc.)
  parseAllLines st (skipToNewline rest)
-- Indexed lines (names, levels, exprs, rec rules)
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

||| Get all parsed expressions (only those that are valid at depth 0)
export
getExprs : ParseState -> List (Nat, ClosedExpr)
getExprs st = mapMaybe extractClosed (toList st.exprs)
  where
    extractClosed : (Nat, ScopedExpr) -> Maybe (Nat, ClosedExpr)
    extractClosed (idx, se) = map (\e => (idx, e)) (se 0)

||| Get all parsed declarations
export
getDecls : ParseState -> List Declaration
getDecls st = reverse st.decls  -- reverse to get original order
