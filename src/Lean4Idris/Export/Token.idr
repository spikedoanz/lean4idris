||| Token types for the lean4export format
|||
||| The export format is line-based with commands like #NS, #US, #EV, etc.
||| Each line typically has an index followed by a command and arguments.
module Lean4Idris.Export.Token

%default total

||| Commands in the export format
public export
data Command : Type where
  -- Name commands
  NS : Command    -- #NS: append string to name
  NI : Command    -- #NI: append integer to name

  -- Universe level commands
  US : Command    -- #US: successor universe
  UM : Command    -- #UM: max universe
  UIM : Command   -- #UIM: imax universe
  UP : Command    -- #UP: universe parameter

  -- Expression commands
  EV : Command    -- #EV: bound variable (de Bruijn index)
  ES : Command    -- #ES: sort
  EC : Command    -- #EC: constant
  EA : Command    -- #EA: application
  EL : Command    -- #EL: lambda
  EP : Command    -- #EP: pi (forall)
  EZ : Command    -- #EZ: let binding
  EJ : Command    -- #EJ: projection
  ELN : Command   -- #ELN: nat literal
  ELS : Command   -- #ELS: string literal

  -- Binder info
  BD : Command    -- #BD: default binder
  BI : Command    -- #BI: implicit binder
  BS : Command    -- #BS: strict implicit binder
  BC : Command    -- #BC: instance binder

  -- Declaration commands
  AX : Command    -- #AX: axiom
  DEF : Command   -- #DEF: definition
  THM : Command   -- #THM: theorem
  OPAQ : Command  -- #OPAQ: opaque definition
  QUOT : Command  -- #QUOT: quotient type primitives
  IND : Command   -- #IND: inductive type
  CTOR : Command  -- #CTOR: constructor
  REC : Command   -- #REC: recursor

  -- Reduction hints
  ABBREV : Command   -- abbreviation hint
  OPAQUE : Command   -- opaque hint
  REGULAR : Command  -- regular hint
  UNSAFE : Command   -- unsafe marker
  PARTIAL : Command  -- partial marker
  SAFE : Command     -- safe marker

  -- Recursor rules
  RR : Command    -- #RR: recursor rule

  -- Mutual definitions
  MUT : Command   -- #MUT: mutual block

export
Eq Command where
  NS == NS = True
  NI == NI = True
  US == US = True
  UM == UM = True
  UIM == UIM = True
  UP == UP = True
  EV == EV = True
  ES == ES = True
  EC == EC = True
  EA == EA = True
  EL == EL = True
  EP == EP = True
  EZ == EZ = True
  EJ == EJ = True
  ELN == ELN = True
  ELS == ELS = True
  BD == BD = True
  BI == BI = True
  BS == BS = True
  BC == BC = True
  AX == AX = True
  DEF == DEF = True
  THM == THM = True
  OPAQ == OPAQ = True
  QUOT == QUOT = True
  IND == IND = True
  CTOR == CTOR = True
  REC == REC = True
  RR == RR = True
  ABBREV == ABBREV = True
  OPAQUE == OPAQUE = True
  REGULAR == REGULAR = True
  UNSAFE == UNSAFE = True
  PARTIAL == PARTIAL = True
  SAFE == SAFE = True
  MUT == MUT = True
  _ == _ = False

export
Show Command where
  show NS = "#NS"
  show NI = "#NI"
  show US = "#US"
  show UM = "#UM"
  show UIM = "#UIM"
  show UP = "#UP"
  show EV = "#EV"
  show ES = "#ES"
  show EC = "#EC"
  show EA = "#EA"
  show EL = "#EL"
  show EP = "#EP"
  show EZ = "#EZ"
  show EJ = "#EJ"
  show ELN = "#ELN"
  show ELS = "#ELS"
  show BD = "#BD"
  show BI = "#BI"
  show BS = "#BS"
  show BC = "#BC"
  show AX = "#AX"
  show DEF = "#DEF"
  show THM = "#THM"
  show OPAQ = "#OPAQ"
  show QUOT = "#QUOT"
  show IND = "#IND"
  show CTOR = "#CTOR"
  show REC = "#REC"
  show RR = "#RR"
  show ABBREV = "#ABBREV"
  show OPAQUE = "#OPAQUE"
  show REGULAR = "#REGULAR"
  show UNSAFE = "#UNSAFE"
  show PARTIAL = "#PARTIAL"
  show SAFE = "#SAFE"
  show MUT = "#MUT"

||| Tokens in the export format
public export
data Token : Type where
  ||| A command like #NS, #EV, etc.
  TCommand : Command -> Token
  ||| A natural number (used for indices and literals)
  TNat : Nat -> Token
  ||| An identifier/string (for name segments)
  TIdent : String -> Token
  ||| Hex-encoded bytes (for string literals)
  THex : String -> Token
  ||| End of line
  TNewline : Token

export
Eq Token where
  (TCommand c1) == (TCommand c2) = c1 == c2
  (TNat n1) == (TNat n2) = n1 == n2
  (TIdent s1) == (TIdent s2) = s1 == s2
  (THex s1) == (THex s2) = s1 == s2
  TNewline == TNewline = True
  _ == _ = False

public export
Show Token where
  show (TCommand c) = show c
  show (TNat n) = show n
  show (TIdent s) = s
  show (THex s) = "0x" ++ s
  show TNewline = "\\n"

||| Parse a command string to a Command
public export
parseCommand : String -> Maybe Command
parseCommand "#NS" = Just NS
parseCommand "#NI" = Just NI
parseCommand "#US" = Just US
parseCommand "#UM" = Just UM
parseCommand "#UIM" = Just UIM
parseCommand "#UP" = Just UP
parseCommand "#EV" = Just EV
parseCommand "#ES" = Just ES
parseCommand "#EC" = Just EC
parseCommand "#EA" = Just EA
parseCommand "#EL" = Just EL
parseCommand "#EP" = Just EP
parseCommand "#EZ" = Just EZ
parseCommand "#EJ" = Just EJ
parseCommand "#ELN" = Just ELN
parseCommand "#ELS" = Just ELS
parseCommand "#BD" = Just BD
parseCommand "#BI" = Just BI
parseCommand "#BS" = Just BS
parseCommand "#BC" = Just BC
parseCommand "#AX" = Just AX
parseCommand "#DEF" = Just DEF
parseCommand "#THM" = Just THM
parseCommand "#OPAQ" = Just OPAQ
parseCommand "#QUOT" = Just QUOT
parseCommand "#IND" = Just IND
parseCommand "#CTOR" = Just CTOR
parseCommand "#REC" = Just REC
parseCommand "#RR" = Just RR
parseCommand "#ABBREV" = Just ABBREV
parseCommand "#OPAQUE" = Just OPAQUE
parseCommand "#REGULAR" = Just REGULAR
parseCommand "#UNSAFE" = Just UNSAFE
parseCommand "#PARTIAL" = Just PARTIAL
parseCommand "#SAFE" = Just SAFE
parseCommand "#MUT" = Just MUT
parseCommand _ = Nothing
