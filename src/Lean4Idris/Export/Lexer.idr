||| Lexer for the lean4export format
|||
||| Uses Text.Lexer from contrib to tokenize export files.
module Lean4Idris.Export.Lexer

import Lean4Idris.Export.Token
import Text.Lexer
import Text.Token
import Data.String
import Data.List
import Data.Maybe

%default total

||| Token kind for use with Text.Lexer
public export
data ExportTokenKind : Type where
  KCommand : ExportTokenKind
  KNat : ExportTokenKind
  KIdent : ExportTokenKind
  KHex : ExportTokenKind
  KNewline : ExportTokenKind
  KIgnore : ExportTokenKind

export
Eq ExportTokenKind where
  KCommand == KCommand = True
  KNat == KNat = True
  KIdent == KIdent = True
  KHex == KHex = True
  KNewline == KNewline = True
  KIgnore == KIgnore = True
  _ == _ = False

||| Token type with bounds information
public export
ExportToken : Type
ExportToken = Text.Token.Token ExportTokenKind

export
Show ExportTokenKind where
  show KCommand = "command"
  show KNat = "nat"
  show KIdent = "ident"
  show KHex = "hex"
  show KNewline = "newline"
  show KIgnore = "ignore"

export
TokenKind ExportTokenKind where
  TokType KCommand = Command
  TokType KNat = Nat
  TokType KIdent = String
  TokType KHex = String
  TokType KNewline = ()
  TokType KIgnore = ()

  tokValue KCommand str = fromMaybe NS (parseCommand str)
  tokValue KNat str = fromMaybe 0 (parsePositive str)
  tokValue KIdent str = str
  tokValue KHex str = str
  tokValue KNewline _ = ()
  tokValue KIgnore _ = ()

||| Lexer for commands starting with #
command : Lexer
command = is '#' <+> some alphaNum

||| Lexer for natural numbers
nat : Lexer
nat = digits

||| Lexer for a single dot (used in version numbers like 0.0.0)
dot : Lexer
dot = is '.'

||| Lexer for identifiers (non-space, non-# at start, non-dot at start)
||| In the export format, identifiers are name segments that may contain:
||| - Regular alphanumeric characters
||| - Special characters like # mid-identifier (e.g., term#[_,])
||| - Middle dots · (U+00B7) and other Unicode
|||
||| The key constraints are:
||| - Must not start with # (reserved for commands)
||| - Must not start with . (reserved for version number separator)
||| - Must not start with digit (reserved for numbers)
||| - Can contain # and . after the first character
|||
||| Note: Identifiers like `grind·._` work because:
||| - Starts with 'g' (not #, not ., not digit)
||| - Contains · (middle-dot, U+00B7) which is allowed anywhere
||| - Contains . (period) which is allowed after first char
ident : Lexer
ident = pred isIdentStart <+> many (pred isIdentCont)
  where
    isIdentStart : Char -> Bool
    isIdentStart c = not (isSpace c) && c /= '#' && c /= '.' && not (isDigit c)

    isIdentCont : Char -> Bool
    isIdentCont c = not (isSpace c)

||| Lexer for hex-encoded strings (after #ELS)
hex : Lexer
hex = some hexDigit

||| Whitespace (spaces and tabs, but not newlines)
ws : Lexer
ws = some (is ' ' <|> is '\t')

||| Newline
eol : Lexer
eol = is '\n' <|> exact "\r\n"

||| The complete token map
||| Order matters:
||| - ws first to skip whitespace
||| - eol for line breaks
||| - command for #NS, #DEF etc.
||| - nat for numbers
||| - dot for version number separators (before ident!)
||| - ident for everything else
exportTokenMap : TokenMap ExportToken
exportTokenMap =
  [ (ws, const $ Tok KIgnore "")
  , (eol, const $ Tok KNewline "\n")
  , (command, \s => Tok KCommand s)
  , (nat, \s => Tok KNat s)
  , (dot, \s => Tok KIdent s)
  , (ident, \s => Tok KIdent s)
  ]

||| Lex an export file into tokens
||| Returns Either an error message or a list of tokens with bounds
export
lexExport : String -> Either String (List (WithBounds ExportToken))
lexExport str =
  case lex exportTokenMap str of
    (tokens, (_, _, "")) => Right tokens
    (_, (line, col, rest)) =>
      Left $ "Lexer error at line " ++ show line ++ ", col " ++ show col ++
             ": unexpected '" ++ substr 0 20 rest ++ "...'"

||| Filter out ignored tokens and extract just the meaningful ones
export
filterTokens : List (WithBounds ExportToken) -> List (WithBounds ExportToken)
filterTokens = filter (\t => t.val.kind /= KIgnore)

||| Convert lexed tokens to our Token type
export
toToken : ExportToken -> Token
toToken (Tok KCommand str) = TCommand (fromMaybe NS (parseCommand str))
toToken (Tok KNat str) = TNat (fromMaybe 0 (parsePositive str))
toToken (Tok KIdent str) = TIdent str
toToken (Tok KHex str) = THex str
toToken (Tok KNewline _) = TNewline
toToken (Tok KIgnore _) = TNewline  -- shouldn't happen after filtering

||| Convenience function to lex and convert to Token list
export
lexToTokens : String -> Either String (List Token)
lexToTokens str = do
  withBounds <- lexExport str
  pure $ map (toToken . val) (filterTokens withBounds)
