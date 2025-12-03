||| Hierarchical names as used in Lean 4
|||
||| Names in Lean are structured hierarchically, built from segments that are
||| either strings or natural numbers. For example, `Nat.add` is represented
||| as `Str "add" (Str "Nat" Anonymous)`.
module Lean4Idris.Name

import Data.List
import Decidable.Equality

%default total

||| A hierarchical name, built from segments
public export
data Name : Type where
  ||| The empty/anonymous name (index 0 in export format)
  Anonymous : Name
  ||| Append a string segment: `#NS parent string`
  Str : String -> Name -> Name
  ||| Append a numeric segment: `#NI parent nat`
  Num : Nat -> Name -> Name

%name Name n, m

||| Show a name in dot-notation (e.g., "Nat.add")
export
Show Name where
  show Anonymous = "[anonymous]"
  show n = showName n
    where
      showName : Name -> String
      showName Anonymous = ""
      showName (Str s Anonymous) = s
      showName (Num k Anonymous) = show k
      showName (Str s parent) = showName parent ++ "." ++ s
      showName (Num k parent) = showName parent ++ "." ++ show k

||| Equality for names is decidable
export
Eq Name where
  Anonymous == Anonymous = True
  (Str s1 p1) == (Str s2 p2) = s1 == s2 && p1 == p2
  (Num n1 p1) == (Num n2 p2) = n1 == n2 && p1 == p2
  _ == _ = False

||| Compare names lexicographically
export
Ord Name where
  compare Anonymous Anonymous = EQ
  compare Anonymous _ = LT
  compare _ Anonymous = GT
  compare (Str s1 p1) (Str s2 p2) =
    case compare p1 p2 of
      EQ => compare s1 s2
      c => c
  compare (Str _ _) (Num _ _) = LT
  compare (Num _ _) (Str _ _) = GT
  compare (Num n1 p1) (Num n2 p2) =
    case compare p1 p2 of
      EQ => compare n1 n2
      c => c

||| Check if a name is anonymous
public export
isAnonymous : Name -> Bool
isAnonymous Anonymous = True
isAnonymous _ = False

||| Get the root (first) segment of a name
public export
root : Name -> Name
root Anonymous = Anonymous
root (Str s Anonymous) = Str s Anonymous
root (Num n Anonymous) = Num n Anonymous
root (Str _ parent) = root parent
root (Num _ parent) = root parent

||| Get all segments as a list (outermost first)
public export
components : Name -> List (Either String Nat)
components = reverse . go
  where
    go : Name -> List (Either String Nat)
    go Anonymous = []
    go (Str s parent) = Left s :: go parent
    go (Num n parent) = Right n :: go parent

||| Build a name from a list of string segments
public export
mkName : List String -> Name
mkName = foldr Str Anonymous

||| Append two names (second becomes prefix of first)
public export
append : Name -> Name -> Name
append Anonymous suffix = suffix
append (Str s parent) suffix = Str s (append parent suffix)
append (Num n parent) suffix = Num n (append parent suffix)

||| Check if one name is a prefix of another
public export
isPrefixOf : (pre, full : Name) -> Bool
isPrefixOf pre full = go (components pre) (components full)
  where
    go : List (Either String Nat) -> List (Either String Nat) -> Bool
    go [] _ = True
    go _ [] = False
    go (x :: xs) (y :: ys) = x == y && go xs ys
