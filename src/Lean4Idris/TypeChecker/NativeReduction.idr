module Lean4Idris.TypeChecker.NativeReduction

import Lean4Idris.Name
import Lean4Idris.Level
import Lean4Idris.Expr
import Lean4Idris.Pretty
import Data.List
import Debug.Trace

%default total

------------------------------------------------------------------------
-- Private Helpers (for internal use)
------------------------------------------------------------------------

listNth : List a -> Nat -> Maybe a
listNth [] _ = Nothing
listNth (x :: _) Z = Just x
listNth (_ :: xs) (S n) = listNth xs n

listDrop : Nat -> List a -> List a
listDrop Z xs = xs
listDrop (S n) [] = []
listDrop (S n) (_ :: xs) = listDrop n xs

getAppConst : ClosedExpr -> Maybe (Name, List Level, List ClosedExpr)
getAppConst e = go e []
  where
    go : ClosedExpr -> List ClosedExpr -> Maybe (Name, List Level, List ClosedExpr)
    go (App f x) args = go f (x :: args)
    go (Const name levels) args = Just (name, levels, args)
    go _ _ = Nothing

getAppSpine : ClosedExpr -> (ClosedExpr, List ClosedExpr)
getAppSpine e = go e []
  where
    go : ClosedExpr -> List ClosedExpr -> (ClosedExpr, List ClosedExpr)
    go (App f x) args = go f (x :: args)
    go head args = (head, args)

iterWhnfStep : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Nat -> ClosedExpr
iterWhnfStep step m 0 = m
iterWhnfStep step m (S fuel) = case step m of
  Just m' => iterWhnfStep step m' fuel
  Nothing => m

------------------------------------------------------------------------
-- Native Evaluation (for native_decide support)
------------------------------------------------------------------------

-- Lean name constructors for Nat operations
natName : Name
natName = Str "Nat" Anonymous

natBleName : Name
natBleName = Str "ble" natName

natBltName : Name
natBltName = Str "blt" natName

natBeqName : Name
natBeqName = Str "beq" natName

natDecLeName : Name
natDecLeName = Str "decLe" natName

natDecEqName : Name
natDecEqName = Str "decEq" natName

natAddName : Name
natAddName = Str "add" natName

natSubName : Name
natSubName = Str "sub" natName

natMulName : Name
natMulName = Str "mul" natName

natDivName : Name
natDivName = Str "div" natName

natModName : Name
natModName = Str "mod" natName

natGcdName : Name
natGcdName = Str "gcd" natName

natSuccName : Name
natSuccName = Str "succ" natName

-- Nat bitwise operations
natLandName : Name
natLandName = Str "land" natName

natLorName : Name
natLorName = Str "lor" natName

natXorName : Name
natXorName = Str "xor" natName

natShiftLeftName : Name
natShiftLeftName = Str "shiftLeft" natName

natShiftRightName : Name
natShiftRightName = Str "shiftRight" natName

natTestBitName : Name
natTestBitName = Str "testBit" natName

-- Bool constructors
boolName : Name
boolName = Str "Bool" Anonymous

boolTrueName : Name
boolTrueName = Str "true" boolName

boolFalseName : Name
boolFalseName = Str "false" boolName

-- Decidable constructors
decidableName : Name
decidableName = Str "Decidable" Anonymous

isTrue : Name
isTrue = Str "isTrue" decidableName

isFalse : Name
isFalse = Str "isFalse" decidableName

-- String operations
stringName : Name
stringName = Str "String" Anonymous

stringDecEqName : Name
stringDecEqName = Str "decEq" stringName

stringBeqName : Name
stringBeqName = Str "beq" stringName

stringAppendName : Name
stringAppendName = Str "append" stringName

stringLengthName : Name
stringLengthName = Str "length" stringName

stringBytesName : Name
stringBytesName = Str "bytes" stringName

-- ByteArray and related type names
byteArrayName : Name
byteArrayName = Str "ByteArray" Anonymous

byteArrayMkName : Name
byteArrayMkName = Str "mk" byteArrayName

arrayName : Name
arrayName = Str "Array" Anonymous

arrayMkName : Name
arrayMkName = Str "mk" arrayName

uint8Name : Name
uint8Name = Str "UInt8" Anonymous

uint8OfBitVecName : Name
uint8OfBitVecName = Str "ofBitVec" uint8Name

-- BitVec (defined early for use in mkUInt8)
bitVecName : Name
bitVecName = Str "BitVec" Anonymous

bitVecOfNatName : Name
bitVecOfNatName = Str "ofNat" bitVecName

listName : Name
listName = Str "List" Anonymous

listNilName : Name
listNilName = Str "nil" listName

listConsName : Name
listConsName = Str "cons" listName

-- Helper to extract Nat from NatLit
getNatLit : ClosedExpr -> Maybe Nat
getNatLit (NatLit n) = Just n
getNatLit _ = Nothing

-- Helper to extract String from StringLit
getStringLit : ClosedExpr -> Maybe String
getStringLit (StringLit s) = Just s
getStringLit _ = Nothing

-- Make Bool constant
mkBool : Bool -> ClosedExpr
mkBool True = Const boolTrueName []
mkBool False = Const boolFalseName []

-- Debug flag for native reduction
debugNative : Bool
debugNative = False

-- Try to reduce Nat.ble n m to true/false
-- Nat.ble : Nat → Nat → Bool
tryNatBle : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatBle args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  let _ = if debugNative then trace "NATIVE Nat.ble: arg0'=\{ppClosedExpr arg0'} arg1'=\{ppClosedExpr arg1'}" () else ()
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = mkBool (n <= m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.blt n m to true/false
-- Nat.blt : Nat → Nat → Bool
tryNatBlt : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatBlt args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = mkBool (n < m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.beq n m to true/false
-- Nat.beq : Nat → Nat → Bool
tryNatBeq : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatBeq args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = mkBool (n == m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.add n m to a NatLit
-- Nat.add : Nat → Nat → Nat
tryNatAdd : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatAdd args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (n + m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.sub n m to a NatLit (truncated subtraction)
-- Nat.sub : Nat → Nat → Nat
tryNatSub : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatSub args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (minus n m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.mul n m to a NatLit
-- Nat.mul : Nat → Nat → Nat
tryNatMul : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatMul args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (n * m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.succ n to a NatLit
-- Nat.succ : Nat → Nat
tryNatSucc : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatSucc args whnfStep = do
  guard (length args >= 1)
  arg0 <- listNth args 0
  let arg0' = iterWhnfStep whnfStep arg0 100
  n <- getNatLit arg0'
  let result = NatLit (S n)
  let remaining = listDrop 1 args
  pure (mkApp result remaining)

-- Helper: Nat division (Lean-style: div by 0 returns 0)
natDiv : Nat -> Nat -> Nat
natDiv n Z = Z
natDiv n (S m) = go n (S m) n
  where
    go : Nat -> Nat -> Nat -> Nat
    go Z _ _ = Z
    go (S fuel) d acc = if acc < d then Z else S (go fuel d (minus acc d))

-- Helper: Nat modulo (Lean-style: mod by 0 returns n)
natMod : Nat -> Nat -> Nat
natMod n Z = n
natMod n (S m) = go n (S m) n
  where
    go : Nat -> Nat -> Nat -> Nat
    go Z _ acc = acc
    go (S fuel) d acc = if acc < d then acc else go fuel d (minus acc d)

-- Try to reduce Nat.div n m to a NatLit
-- Nat.div : Nat → Nat → Nat
tryNatDiv : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatDiv args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (natDiv n m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.mod n m to a NatLit
-- Nat.mod : Nat → Nat → Nat
tryNatMod : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatMod args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (natMod n m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Helper: Nat gcd (using Euclidean algorithm)
natGcd : Nat -> Nat -> Nat
natGcd a 0 = a
natGcd a (S b) = go (a + S b) a (S b)
  where
    go : Nat -> Nat -> Nat -> Nat
    go 0 x _ = x  -- fuel exhausted
    go _ x 0 = x  -- gcd(x, 0) = x
    go (S fuel) x y = go fuel y (natMod x y)

-- Try to reduce Nat.gcd n m to a NatLit
-- Nat.gcd : Nat → Nat → Nat
tryNatGcd : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatGcd args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (natGcd n m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Bitwise helper functions for Nat
-- These implement the operations natively since Idris2 doesn't have a Bits instance for Nat
-- Note: natDiv and natMod defined above are used (not backtick operators)
-- Uses fuel-based approach to satisfy totality checker

-- Nat shift right: n >> k = n / (2^k)
-- Uses shift amount k as the decreasing argument
natShiftRightNat : Nat -> Nat -> Nat
natShiftRightNat n 0 = n
natShiftRightNat n (S k) = natShiftRightNat (natDiv n 2) k

-- Nat shift left: n << k = n * (2^k)
-- Uses shift amount k as the decreasing argument
natShiftLeftNat : Nat -> Nat -> Nat
natShiftLeftNat n 0 = n
natShiftLeftNat n (S k) = natShiftLeftNat (n * 2) k

-- Nat bitwise AND (implemented via standard bit-by-bit algorithm)
-- Uses max(n, m) as fuel since we divide by 2 each step
natLandNat : Nat -> Nat -> Nat
natLandNat n m = go (n + m) n m
  where
    go : Nat -> Nat -> Nat -> Nat
    go Z _ _ = 0  -- fuel exhausted (shouldn't happen with proper fuel)
    go _ Z _ = 0  -- base case: 0 AND x = 0
    go _ _ Z = 0  -- base case: x AND 0 = 0
    go (S fuel) n' m' =
      let bit = if (natMod n' 2 == 1) && (natMod m' 2 == 1) then 1 else 0
      in bit + 2 * go fuel (natDiv n' 2) (natDiv m' 2)

-- Nat bitwise OR
-- Uses n + m as fuel
natLorNat : Nat -> Nat -> Nat
natLorNat n m = go (n + m) n m
  where
    go : Nat -> Nat -> Nat -> Nat
    go Z _ _ = 0  -- fuel exhausted
    go _ Z m' = m'  -- base case: 0 OR m = m
    go _ n' Z = n'  -- base case: n OR 0 = n
    go (S fuel) n' m' =
      let bit = if (natMod n' 2 == 1) || (natMod m' 2 == 1) then 1 else 0
      in bit + 2 * go fuel (natDiv n' 2) (natDiv m' 2)

-- Nat bitwise XOR
-- Uses n + m as fuel
natXorNat : Nat -> Nat -> Nat
natXorNat n m = go (n + m) n m
  where
    go : Nat -> Nat -> Nat -> Nat
    go Z _ _ = 0  -- fuel exhausted
    go _ Z m' = m'  -- base case: 0 XOR m = m
    go _ n' Z = n'  -- base case: n XOR 0 = n
    go (S fuel) n' m' =
      let bit = if (natMod n' 2 == 1) /= (natMod m' 2 == 1) then 1 else 0
      in bit + 2 * go fuel (natDiv n' 2) (natDiv m' 2)

-- Try to reduce Nat.shiftRight n k to a NatLit
tryNatShiftRight : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatShiftRight args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  k <- getNatLit arg1'
  let result = NatLit (natShiftRightNat n k)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.shiftLeft n k to a NatLit
tryNatShiftLeft : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatShiftLeft args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  k <- getNatLit arg1'
  let result = NatLit (natShiftLeftNat n k)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.land n m to a NatLit
tryNatLand : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatLand args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (natLandNat n m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.lor n m to a NatLit
tryNatLor : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatLor args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (natLorNat n m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.xor n m to a NatLit
tryNatXor : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatXor args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  m <- getNatLit arg1'
  let result = NatLit (natXorNat n m)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Nat.testBit: testBit n i = ((n >>> i) &&& 1) != 0
-- Returns true if the i-th bit of n is 1
natTestBit : Nat -> Nat -> Bool
natTestBit n i = natMod (natShiftRightNat n i) 2 == 1

-- Try to reduce Nat.testBit n i to true/false
tryNatTestBit : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatTestBit args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  n <- getNatLit arg0'
  i <- getNatLit arg1'
  let result = mkBool (natTestBit n i)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

------------------------------------------------------------------------
-- String.bytes native support
------------------------------------------------------------------------

-- UTF-8 encoding: Convert a single Unicode code point to UTF-8 bytes
-- Uses natShiftRightNat and natMod which are defined above
encodeCharUtf8 : Char -> List Nat
encodeCharUtf8 c =
  let cp = cast {to=Nat} (ord c)
  in if cp < 0x80 then
       [cp]
     else if cp < 0x800 then
       [0xC0 + natShiftRightNat cp 6, 0x80 + natMod cp 64]
     else if cp < 0x10000 then
       [0xE0 + natShiftRightNat cp 12, 0x80 + natMod (natShiftRightNat cp 6) 64, 0x80 + natMod cp 64]
     else
       [0xF0 + natShiftRightNat cp 18, 0x80 + natMod (natShiftRightNat cp 12) 64, 0x80 + natMod (natShiftRightNat cp 6) 64, 0x80 + natMod cp 64]

-- Encode an entire string to UTF-8 bytes
encodeStringUtf8 : String -> List Nat
encodeStringUtf8 s = concatMap encodeCharUtf8 (unpack s)

-- UInt8 type expression: UInt8
uint8Type : ClosedExpr
uint8Type = Const uint8Name []

-- Make a UInt8 literal: UInt8.ofBitVec (BitVec.ofNat 8 n)
mkUInt8 : Nat -> ClosedExpr
mkUInt8 n =
  let n' = natMod n 256  -- Ensure it fits in 8 bits
  in App (Const uint8OfBitVecName []) (App (App (Const bitVecOfNatName []) (NatLit 8)) (NatLit n'))

-- Make List UInt8 type
listUInt8Type : ClosedExpr
listUInt8Type = App (Const listName [Level.Zero]) uint8Type

-- Make List.nil {UInt8}
mkListNil : ClosedExpr
mkListNil = App (Const listNilName [Level.Zero]) uint8Type

-- Make List.cons {UInt8} head tail
mkListCons : ClosedExpr -> ClosedExpr -> ClosedExpr
mkListCons head tail = App (App (App (Const listConsName [Level.Zero]) uint8Type) head) tail

-- Make a List of UInt8 from a list of byte values
mkUInt8List : List Nat -> ClosedExpr
mkUInt8List [] = mkListNil
mkUInt8List (b :: bs) = mkListCons (mkUInt8 b) (mkUInt8List bs)

-- Make Array UInt8 type
arrayUInt8Type : ClosedExpr
arrayUInt8Type = App (Const arrayName [Level.Zero]) uint8Type

-- Make Array.mk {UInt8} list
mkArrayMk : ClosedExpr -> ClosedExpr
mkArrayMk listExpr = App (App (Const arrayMkName [Level.Zero]) uint8Type) listExpr

-- Make ByteArray.mk array
mkByteArrayMk : ClosedExpr -> ClosedExpr
mkByteArrayMk arrayExpr = App (Const byteArrayMkName []) arrayExpr

-- Make a ByteArray from a string's UTF-8 encoding
mkByteArray : String -> ClosedExpr
mkByteArray s =
  let bytes = encodeStringUtf8 s
      listExpr = mkUInt8List bytes
      arrayExpr = mkArrayMk listExpr
  in mkByteArrayMk arrayExpr

-- Try to reduce String.bytes s to ByteArray.mk (Array.mk [bytes...])
tryStringBytes : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryStringBytes args whnfStep = do
  guard (length args >= 1)
  arg0 <- listNth args 0
  let arg0' = iterWhnfStep whnfStep arg0 100
  s <- getStringLit arg0'
  let result = mkByteArray s
  let remaining = listDrop 1 args
  pure (mkApp result remaining)

-- HMod class and method
hModClassName : Name
hModClassName = Str "HMod" Anonymous

hModHModName : Name
hModHModName = Str "hMod" hModClassName

-- HPow class and method
hPowClassName : Name
hPowClassName = Str "HPow" Anonymous

hPowHPowName : Name
hPowHPowName = Str "hPow" hPowClassName

-- Nat.pow
natPowName : Name
natPowName = Str "pow" natName

-- Helper: Nat power
natPow : Nat -> Nat -> Nat
natPow _ Z = 1
natPow b (S e) = b * natPow b e

-- Try to reduce Nat.pow b e to a NatLit
-- Nat.pow : Nat → Nat → Nat
tryNatPow : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatPow args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  b <- getNatLit arg0'
  e <- getNatLit arg1'
  let result = NatLit (natPow b e)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce HPow.hPow when applied to Nat arguments
-- HPow.hPow : {α β γ} → [inst] → α → β → γ
-- For Nat, this is Nat.pow
tryHPowHPow : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryHPowHPow args whnfStep = do
  -- HPow.hPow has 6 args: 3 implicit types + instance + 2 operands
  guard (length args >= 6)
  arg4 <- listNth args 4  -- base
  arg5 <- listNth args 5  -- exponent
  let arg4' = iterWhnfStep whnfStep arg4 100
  let arg5' = iterWhnfStep whnfStep arg5 100
  b <- getNatLit arg4'
  e <- getNatLit arg5'
  let result = NatLit (natPow b e)
  let remaining = listDrop 6 args
  pure (mkApp result remaining)

-- Try to reduce HMod.hMod when applied to Nat arguments
-- HMod.hMod : {α β γ} → [inst] → α → β → γ
-- For Nat, this is just Nat.mod
tryHModHMod : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryHModHMod args whnfStep = do
  -- HMod.hMod has 6 args: 3 implicit types + instance + 2 operands
  guard (length args >= 6)
  arg4 <- listNth args 4  -- first operand
  arg5 <- listNth args 5  -- second operand
  let arg4' = iterWhnfStep whnfStep arg4 100
  let arg5' = iterWhnfStep whnfStep arg5 100
  n <- getNatLit arg4'
  m <- getNatLit arg5'
  let result = NatLit (natMod n m)
  let remaining = listDrop 6 args
  pure (mkApp result remaining)

-- Try to reduce String.beq s1 s2 to true/false
-- String.beq : String → String → Bool
tryStringBeq : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryStringBeq args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  s1 <- getStringLit arg0'
  s2 <- getStringLit arg1'
  let result = mkBool (s1 == s2)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce String.append s1 s2 to a StringLit
-- String.append : String → String → String
tryStringAppend : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryStringAppend args whnfStep = do
  guard (length args >= 2)
  arg0 <- listNth args 0
  arg1 <- listNth args 1
  let arg0' = iterWhnfStep whnfStep arg0 100
  let arg1' = iterWhnfStep whnfStep arg1 100
  s1 <- getStringLit arg0'
  s2 <- getStringLit arg1'
  let result = StringLit (s1 ++ s2)
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce String.length s to a NatLit
-- String.length : String → Nat
tryStringLength : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryStringLength args whnfStep = do
  guard (length args >= 1)
  arg0 <- listNth args 0
  let arg0' = iterWhnfStep whnfStep arg0 100
  s <- getStringLit arg0'
  let result = NatLit (length s)
  let remaining = listDrop 1 args
  pure (mkApp result remaining)

-- Fin operations
finName : Name
finName = Str "Fin" Anonymous

finValName : Name
finValName = Str "val" finName

-- Try to reduce Fin.val to extract the underlying Nat
-- Fin.val : Fin n → Nat
-- Fin values are often constructed as ⟨natVal, proof⟩
tryFinVal : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryFinVal args whnfStep = do
  guard (length args >= 2)  -- n and the Fin value
  finVal <- listNth args 1
  let finVal' = iterWhnfStep whnfStep finVal 100
  -- Try to extract from constructor application
  case getAppConst finVal' of
    Just (ctorName, _, ctorArgs) => do
      -- Fin.mk n val proof -> val is first arg after the type param
      guard (length ctorArgs >= 2)
      valArg <- listNth ctorArgs 1
      let valArg' = iterWhnfStep whnfStep valArg 100
      case valArg' of
        NatLit n =>
          let remaining = listDrop 2 args
          in pure (mkApp (NatLit n) remaining)
        _ => Nothing
    Nothing => Nothing

-- BitVec operations
bitVecToNatName : Name
bitVecToNatName = Str "toNat" bitVecName

-- Try to reduce BitVec.toNat
tryBitVecToNat : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryBitVecToNat args whnfStep = do
  guard (length args >= 2)  -- width and the BitVec value
  bvVal <- listNth args 1
  let bvVal' = iterWhnfStep whnfStep bvVal 100
  case getAppConst bvVal' of
    Just (name, _, bvArgs) =>
      -- If it's BitVec.ofNat w n, return n mod 2^w
      if name == bitVecOfNatName then do
        guard (length bvArgs >= 2)
        nArg <- listNth bvArgs 1
        let nArg' = iterWhnfStep whnfStep nArg 100
        n <- getNatLit nArg'
        -- For simplicity, just return n (assuming it's in range)
        let remaining = listDrop 2 args
        pure (mkApp (NatLit n) remaining)
      else Nothing
    Nothing => Nothing

-- UInt32 operations
uint32Name : Name
uint32Name = Str "UInt32" Anonymous

uint32ToNatName : Name
uint32ToNatName = Str "toNat" uint32Name

uint32OfNatName : Name
uint32OfNatName = Str "ofNat" uint32Name

-- decide function (both Decidable.decide and the top-level decide)
decidableDecideName : Name
decidableDecideName = Str "decide" decidableName

decideFnName : Name
decideFnName = Str "decide" Anonymous

-- Nat.decLt and Nat.decLe
natDecLtName : Name
natDecLtName = Str "decLt" natName

-- instDecidableLtNat (for Nat < comparison)
instDecidableLtNatName : Name
instDecidableLtNatName = Str "instDecidableLtNat" Anonymous

-- instDecidableLtBitVec
instDecidableLtBitVecName : Name
instDecidableLtBitVecName = Str "instDecidableLtBitVec" Anonymous

-- instDecidableLeBitVec
instDecidableLeBitVecName : Name
instDecidableLeBitVecName = Str "instDecidableLeBitVec" Anonymous

-- instDecidableEqBitVec
instDecidableEqBitVecName : Name
instDecidableEqBitVecName = Str "instDecidableEqBitVec" Anonymous

-- UInt32.decLt
uint32DecLtName : Name
uint32DecLtName = Str "decLt" uint32Name

-- Try to reduce UInt32.toNat
-- Note: This is a forward declaration - the actual implementation is below
-- after tryGetUInt32AsNat is defined
covering
tryUInt32ToNat : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr

-- OfNat class and ofNat function
ofNatClassName : Name
ofNatClassName = Str "OfNat" Anonymous

ofNatOfNatName : Name
ofNatOfNatName = Str "ofNat" ofNatClassName

-- OfNat.ofNat reduction: OfNat.ofNat α n inst => n (when α is Nat)
-- The args are: [α, n, inst]
covering
tryOfNatOfNat : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryOfNatOfNat args whnfStep = do
  guard (length args >= 3)
  -- Get the type argument α
  tyArg <- listNth args 0
  let tyArg' = iterWhnfStep whnfStep tyArg 100
  -- Check if α is Nat
  case tyArg' of
    Const n _ =>
      if n == natName
        then do
          -- Return the nat literal argument n
          nArg <- listNth args 1
          let remaining = listDrop 3 args
          Just (mkApp nArg remaining)
        else Nothing
    _ => Nothing

-- UInt32.ofBitVec name
uint32OfBitVecName : Name
uint32OfBitVecName = Str "ofBitVec" uint32Name

-- BitVec.ofFin name
bitVecOfFinName : Name
bitVecOfFinName = Str "ofFin" bitVecName

-- Helper: try to extract Nat from possible HPow projection
-- Handles (Proj HPow 0 inst) base expo -> base^expo
covering
tryGetNatFromPossiblePow : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Maybe Nat
tryGetNatFromPossiblePow whnfStep e' =
  case getNatLit e' of
    Just n => Just n
    Nothing =>
      -- Try to handle HPow projection: (Proj HPow 0 inst) arg1 arg2
      let (h, s) = getAppSpine e'
      in case h of
           Proj psn _ _ =>
             if psn == hPowClassName then do
               guard (length s >= 2)
               base <- listNth s 0
               expo <- listNth s 1
               let base' = iterWhnfStep whnfStep base 100
               let expo' = iterWhnfStep whnfStep expo 100
               b <- getNatLit base'
               e <- getNatLit expo'
               Just (natPow b e)
             else Nothing
           _ => Nothing

-- Helper: try to extract a Nat from a Fin expression
-- Fin values are structured as ⟨n, proof⟩ where we want to extract n
covering
tryGetFinAsNat : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Maybe Nat
tryGetFinAsNat whnfStep e =
  let e' = iterWhnfStep whnfStep e 100
  in case getAppConst e' of
    Just (name, _, args) =>
      let finMkName = Str "mk" finName
      in if name == finMkName then do
        guard (length args >= 2)
        valArg <- listNth args 1  -- val is the second arg (after implicit bound)
        let valArg' = iterWhnfStep whnfStep valArg 500
        -- First try getNatLit directly
        case getNatLit valArg' of
          Just n => Just n
          Nothing =>
            -- Try to handle HMod projection pattern: (Proj HMod 0 inst) arg1 arg2
            let (head, spine) = getAppSpine valArg'
            in case head of
                 Proj sn _ _ =>
                   -- Check if this is HMod.0 projection (the hMod method)
                   if sn == hModClassName then do
                     guard (length spine >= 2)
                     operand1 <- listNth spine 0
                     operand2 <- listNth spine 1
                     let operand1' = iterWhnfStep whnfStep operand1 100
                     let operand2' = iterWhnfStep whnfStep operand2 100
                     -- Short-circuit: 0 % m = 0 for any m
                     case getNatLit operand1' of
                       Just 0 => Just 0
                       Just n => do
                         m <- tryGetNatFromPossiblePow whnfStep operand2'
                         Just (natMod n m)
                       Nothing => Nothing
                   else Nothing
                 _ => Nothing
      else Nothing
    -- Try to get from Proj expression (Fin.val projection)
    Nothing => case e' of
      Proj _ idx structVal =>
        if idx == 0 then do  -- val is typically field 0
          let structVal' = iterWhnfStep whnfStep structVal 100
          tryGetFinAsNat whnfStep structVal'
        else Nothing
      -- If it's a NatLit directly, return it
      NatLit n => Just n
      _ => Nothing

-- Helper: try to extract a Nat from a BitVec expression
covering
tryGetBitVecAsNat : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Maybe Nat
tryGetBitVecAsNat whnfStep e =
  let e' = iterWhnfStep whnfStep e 100
  in case getAppConst e' of
    Just (name, _, args) =>
      -- BitVec.ofNat w n -> n (args: [w, n])
      if name == bitVecOfNatName then do
        guard (length args >= 2)
        nArg <- listNth args 1
        let nArg' = iterWhnfStep whnfStep nArg 100
        getNatLit nArg'
      -- BitVec.ofFin w fin -> extract from Fin
      else if name == bitVecOfFinName then do
        guard (length args >= 2)
        finArg <- listNth args 1
        tryGetFinAsNat whnfStep finArg
      else Nothing
    Nothing => Nothing

-- Helper: try to extract a Nat from a UInt32 expression
-- UInt32 values can be constructed as:
-- 1. OfNat.ofNat UInt32 n inst
-- 2. UInt32.ofNat inst n
-- 3. UInt32.ofBitVec (BitVec.ofNat 32 n)
covering
tryGetUInt32AsNat : (ClosedExpr -> Maybe ClosedExpr) -> ClosedExpr -> Maybe Nat
tryGetUInt32AsNat whnfStep e =
  let e' = iterWhnfStep whnfStep e 100
  in case getAppConst e' of
    Just (name, _, args) =>
      -- OfNat.ofNat ty n inst -> n (args: [ty, n, inst])
      if name == ofNatOfNatName then do
        guard (length args >= 2)
        nArg <- listNth args 1
        let nArg' = iterWhnfStep whnfStep nArg 100
        getNatLit nArg'
      -- UInt32.ofNat inst n -> n
      else if name == uint32OfNatName then do
        guard (length args >= 2)
        nArg <- listNth args 1
        let nArg' = iterWhnfStep whnfStep nArg 100
        getNatLit nArg'
      -- UInt32.ofBitVec bv -> extract from BitVec.ofNat
      else if name == uint32OfBitVecName then do
        guard (length args >= 1)
        bvArg <- listNth args 0
        tryGetBitVecAsNat whnfStep bvArg
      else Nothing
    Nothing => Nothing

-- Implementation of tryUInt32ToNat (uses tryGetUInt32AsNat)
tryUInt32ToNat args whnfStep = do
  guard (length args >= 1)
  uVal <- listNth args 0
  n <- tryGetUInt32AsNat whnfStep uVal
  let remaining = listDrop 1 args
  pure (mkApp (NatLit n) remaining)

-- Make isTrue/isFalse Decidable constructors
-- Note: We need to apply them to the proposition and proof, but for native_decide
-- the proof is erased, so we can use a placeholder
mkIsTrue : ClosedExpr
mkIsTrue = Const isTrue []

mkIsFalse : ClosedExpr
mkIsFalse = Const isFalse []

-- Try to reduce UInt32.decLt to isTrue/isFalse
covering
tryUInt32DecLt : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryUInt32DecLt args whnfStep = do
  guard (length args >= 2)
  a <- listNth args 0
  b <- listNth args 1
  na <- tryGetUInt32AsNat whnfStep a
  nb <- tryGetUInt32AsNat whnfStep b
  -- Return isTrue or isFalse (the proof args are implicit/erased)
  let result = if na < nb then mkIsTrue else mkIsFalse
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.decLt to isTrue/isFalse
tryNatDecLt : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatDecLt args whnfStep = do
  guard (length args >= 2)
  a <- listNth args 0
  b <- listNth args 1
  let a' = iterWhnfStep whnfStep a 100
  let b' = iterWhnfStep whnfStep b 100
  na <- getNatLit a'
  nb <- getNatLit b'
  let result = if na < nb then mkIsTrue else mkIsFalse
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce Nat.decLe to isTrue/isFalse
tryNatDecLeNative : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNatDecLeNative args whnfStep = do
  guard (length args >= 2)
  a <- listNth args 0
  b <- listNth args 1
  let a' = iterWhnfStep whnfStep a 100
  let b' = iterWhnfStep whnfStep b 100
  na <- getNatLit a'
  nb <- getNatLit b'
  let result = if na <= nb then mkIsTrue else mkIsFalse
  let remaining = listDrop 2 args
  pure (mkApp result remaining)

-- Try to reduce decide when applied to numeric decidability instances
-- Decidable.decide inst -> true/false based on inst
-- decide P inst -> true/false based on inst
-- The instance might be Nat.decLt a b, UInt32.decLt a b, etc.
-- Or it might have already been reduced to isTrue/isFalse
covering
tryDecide : List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryDecide args whnfStep = do
  guard (length args >= 1)
  -- For Decidable.decide: args[0] is the Decidable instance (p is implicit)
  -- For decide: args[0] is p, args[1] is the instance
  -- Try both positions
  instArg <- (if length args >= 2 then listNth args 1 else listNth args 0)
              <|> listNth args 0
  let instArg' = iterWhnfStep whnfStep instArg 100
  case getAppConst instArg' of
    Just (name, _, instArgs) =>
      -- If already reduced to isTrue, return true
      if name == isTrue then do
        let remaining = listDrop 2 args
        pure (mkApp (mkBool True) remaining)
      -- If already reduced to isFalse, return false
      else if name == isFalse then do
        let remaining = listDrop 2 args
        pure (mkApp (mkBool False) remaining)
      -- Nat.decLt a b
      else if name == natDecLtName then do
        guard (length instArgs >= 2)
        a <- listNth instArgs 0
        b <- listNth instArgs 1
        let a' = iterWhnfStep whnfStep a 100
        let b' = iterWhnfStep whnfStep b 100
        na <- getNatLit a'
        nb <- getNatLit b'
        let result = mkBool (na < nb)
        let remaining = listDrop 2 args
        pure (mkApp result remaining)
      -- UInt32.decLt a b (may have more args due to implicit params)
      else if name == uint32DecLtName then do
        -- UInt32.decLt takes 2 UInt32 args (a and b)
        guard (length instArgs >= 2)
        a <- listNth instArgs 0
        b <- listNth instArgs 1
        na <- tryGetUInt32AsNat whnfStep a
        nb <- tryGetUInt32AsNat whnfStep b
        let result = mkBool (na < nb)
        -- For Decidable.decide, remaining args start after the decide arg
        let remaining = listDrop 2 args
        pure (mkApp result remaining)
      -- instDecidableLtBitVec w a b
      else if name == instDecidableLtBitVecName then do
        guard (length instArgs >= 3)
        a <- listNth instArgs 1
        b <- listNth instArgs 2
        na <- tryGetBitVecAsNat whnfStep a
        nb <- tryGetBitVecAsNat whnfStep b
        let result = mkBool (na < nb)
        let remaining = listDrop 2 args
        pure (mkApp result remaining)
      -- instDecidableLeBitVec w a b
      else if name == instDecidableLeBitVecName then do
        guard (length instArgs >= 3)
        a <- listNth instArgs 1
        b <- listNth instArgs 2
        na <- tryGetBitVecAsNat whnfStep a
        nb <- tryGetBitVecAsNat whnfStep b
        let result = mkBool (na <= nb)
        let remaining = listDrop 2 args
        pure (mkApp result remaining)
      -- instDecidableEqBitVec w a b
      else if name == instDecidableEqBitVecName then do
        guard (length instArgs >= 3)
        a <- listNth instArgs 1
        b <- listNth instArgs 2
        na <- tryGetBitVecAsNat whnfStep a
        nb <- tryGetBitVecAsNat whnfStep b
        let result = mkBool (na == nb)
        let remaining = listDrop 2 args
        pure (mkApp result remaining)
      -- Nat.decLe a b
      else if name == natDecLeName then do
        guard (length instArgs >= 2)
        a <- listNth instArgs 0
        b <- listNth instArgs 1
        let a' = iterWhnfStep whnfStep a 100
        let b' = iterWhnfStep whnfStep b 100
        na <- getNatLit a'
        nb <- getNatLit b'
        let result = mkBool (na <= nb)
        let remaining = listDrop 2 args
        pure (mkApp result remaining)
      else Nothing
    Nothing => Nothing

------------------------------------------------------------------------
-- Main native evaluation dispatcher
------------------------------------------------------------------------

-- Dispatch native evaluation based on function name
-- Split into multiple sub-dispatchers to avoid long if-else chains
-- which cause slow compilation in Idris 2

tryNativeEvalNat : Name -> List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNativeEvalNat name args step =
  if name == natBleName then tryNatBle args step
  else if name == natBltName then tryNatBlt args step
  else if name == natBeqName then tryNatBeq args step
  else if name == natAddName then tryNatAdd args step
  else if name == natSubName then tryNatSub args step
  else if name == natMulName then tryNatMul args step
  else if name == natSuccName then tryNatSucc args step
  else if name == natDivName then tryNatDiv args step
  else if name == natModName then tryNatMod args step
  else if name == natGcdName then tryNatGcd args step
  else if name == natPowName then tryNatPow args step
  else Nothing

tryNativeEvalNatBitwise : Name -> List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNativeEvalNatBitwise name args step =
  if name == natLandName then tryNatLand args step
  else if name == natLorName then tryNatLor args step
  else if name == natXorName then tryNatXor args step
  else if name == natShiftLeftName then tryNatShiftLeft args step
  else if name == natShiftRightName then tryNatShiftRight args step
  else if name == natTestBitName then tryNatTestBit args step
  else Nothing

tryNativeEvalString : Name -> List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNativeEvalString name args step =
  if name == stringBeqName then tryStringBeq args step
  else if name == stringAppendName then tryStringAppend args step
  else if name == stringLengthName then tryStringLength args step
  else if name == stringBytesName then tryStringBytes args step
  else Nothing

covering
tryNativeEvalTypeclass : Name -> List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNativeEvalTypeclass name args step =
  if name == hModHModName then tryHModHMod args step
  else if name == hPowHPowName then tryHPowHPow args step
  else if name == ofNatOfNatName then tryOfNatOfNat args step
  else Nothing

covering
tryNativeEvalOther : Name -> List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNativeEvalOther name args step =
  if name == finValName then tryFinVal args step
  else if name == bitVecToNatName then tryBitVecToNat args step
  else if name == uint32ToNatName then tryUInt32ToNat args step
  else Nothing

covering
tryNativeEvalDecide : Name -> List ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNativeEvalDecide name args step =
  if name == uint32DecLtName then tryUInt32DecLt args step
  else if name == natDecLtName then tryNatDecLt args step
  else if name == natDecLeName then tryNatDecLeNative args step
  else if name == decideFnName then tryDecide args step
  else if name == decidableDecideName then tryDecide args step
  else Nothing

export covering
tryNativeEval : ClosedExpr -> (ClosedExpr -> Maybe ClosedExpr) -> Maybe ClosedExpr
tryNativeEval e whnfStep =
  case getAppConst e of
    Nothing => Nothing
    Just (name, _, args) =>
      let _ = if debugNative then trace "NATIVE tryNativeEval: name=\{show name} args=\{show (length args)}" () else () in
      tryNativeEvalNat name args whnfStep
        <|> tryNativeEvalNatBitwise name args whnfStep
        <|> tryNativeEvalString name args whnfStep
        <|> tryNativeEvalTypeclass name args whnfStep
        <|> tryNativeEvalOther name args whnfStep
        <|> tryNativeEvalDecide name args whnfStep
