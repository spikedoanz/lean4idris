||| Universe levels for Lean 4
|||
||| Lean uses a hierarchy of type universes to avoid paradoxes like Russell's.
||| Universe levels can be:
||| - Zero: the base level
||| - Succ: successor of another level
||| - Max: maximum of two levels
||| - IMax: "impredicative max" (returns 0 if second arg is 0, else max)
||| - Param: universe parameter (referenced by index during parsing)
module Lean4Idris.Level

import Lean4Idris.Name
import Data.Nat
import Data.List

%default total

||| Universe levels
public export
data Level : Type where
  ||| Universe 0 (Prop in Lean)
  Zero : Level
  ||| Successor universe
  Succ : Level -> Level
  ||| Maximum of two levels
  Max  : Level -> Level -> Level
  ||| Impredicative maximum: returns 0 if second is 0, else behaves like Max
  ||| This makes Prop impredicative: (P : Prop) -> Prop is in Prop
  IMax : Level -> Level -> Level
  ||| Universe parameter (by name in final representation)
  Param : Name -> Level

%name Level l, l1, l2

export
Eq Level where
  Zero == Zero = True
  (Succ l1) == (Succ l2) = l1 == l2
  (Max a1 b1) == (Max a2 b2) = a1 == a2 && b1 == b2
  (IMax a1 b1) == (IMax a2 b2) = a1 == a2 && b1 == b2
  (Param n1) == (Param n2) = n1 == n2
  _ == _ = False

export
Show Level where
  show Zero = "0"
  show (Succ l) = showSucc 1 l
    where
      showSucc : Nat -> Level -> String
      showSucc n Zero = show n
      showSucc n (Succ l') = showSucc (S n) l'
      showSucc n l' = show l' ++ " + " ++ show n
  show (Max l1 l2) = "max(" ++ show l1 ++ ", " ++ show l2 ++ ")"
  show (IMax l1 l2) = "imax(" ++ show l1 ++ ", " ++ show l2 ++ ")"
  show (Param n) = show n

||| Evaluate a level given concrete assignments to parameters
||| Returns Nothing if a parameter is not found
public export
eval : (params : List (Name, Nat)) -> Level -> Maybe Nat
eval _ Zero = Just 0
eval ps (Succ l) = map S (eval ps l)
eval ps (Max l1 l2) = [| max (eval ps l1) (eval ps l2) |]
eval ps (IMax l1 l2) = do
  v2 <- eval ps l2
  if v2 == 0
    then Just 0
    else [| max (eval ps l1) (pure v2) |]
eval ps (Param n) = lookup n ps

||| Check if a level is definitely zero (syntactically)
public export
isZero : Level -> Bool
isZero Zero = True
isZero _ = False

||| Check if a level is definitely non-zero (syntactically)
public export
isNonZero : Level -> Bool
isNonZero (Succ _) = True
isNonZero (Max l1 l2) = isNonZero l1 || isNonZero l2
isNonZero _ = False

||| Get the offset (number of Succ wrappers) and base of a level
||| e.g., Succ (Succ (Param u)) returns (2, Param u)
||| e.g., Succ (Succ Zero) returns (2, Zero)
getOffsetBase : Level -> (Nat, Level)
getOffsetBase (Succ l) = let (n, base) = getOffsetBase l in (S n, base)
getOffsetBase l = (0, l)

||| Check if level a dominates level b (i.e., max a b = a for all parameter assignments)
||| Conservative check - returns True only if we can definitely prove dominance
||| Key rule: Succ^n (Param u) dominates Succ^m Zero when m <= n (since u >= 0)
covering
dominates : Level -> Level -> Bool
dominates a b =
  let (na, basea) = getOffsetBase a
      (nb, baseb) = getOffsetBase b
  in case (basea, baseb) of
       -- Concrete levels: just compare
       (Zero, Zero) => na >= nb
       -- u+n dominates m when m <= n (since u >= 0, u+n >= n >= m)
       (Param _, Zero) => na >= nb
       -- Same param: compare offsets
       (Param u1, Param u2) => u1 == u2 && na >= nb
       -- Max: a dominates b if a dominates all parts of b
       (_, Max b1 b2) => dominates a b1 && dominates a b2
       -- a dominates b if any part of a dominates b
       (Max a1 a2, _) => dominates a1 b || dominates a2 b
       _ => False

||| Simplify a level expression
||| Applies basic normalization rules
-- Compare levels for canonical ordering (atoms only, not nested Max)
-- Uses a lexicographic ordering to ensure deterministic canonicalization
public export
levelLt : Level -> Level -> Bool
levelLt Zero Zero = False
levelLt Zero _ = True
levelLt _ Zero = False
levelLt (Succ a) (Succ b) = levelLt a b
levelLt (Succ _) _ = True
levelLt _ (Succ _) = False
levelLt (Max a1 b1) (Max a2 b2) = if a1 == a2 then levelLt b1 b2 else levelLt a1 a2
levelLt (Max _ _) _ = True
levelLt _ (Max _ _) = False
levelLt (IMax a1 b1) (IMax a2 b2) = if a1 == a2 then levelLt b1 b2 else levelLt a1 a2
levelLt (IMax _ _) _ = True
levelLt _ (IMax _ _) = False
levelLt (Param n1) (Param n2) = show n1 < show n2

||| Flatten nested Max into a list of non-Max terms (atoms)
||| e.g., Max a (Max b c) => [a, b, c]
covering
flattenMax : Level -> List Level
flattenMax (Max l1 l2) = flattenMax l1 ++ flattenMax l2
flattenMax l = [l]

||| Insert a level into a sorted list, maintaining sorted order
||| and removing duplicates and dominated terms
covering
insertSorted : Level -> List Level -> List Level
insertSorted l [] = [l]
insertSorted l (x :: xs) =
  if l == x then x :: xs  -- duplicate
  else if dominates l x then insertSorted l xs  -- l dominates x, drop x
  else if dominates x l then x :: xs  -- x dominates l, drop l
  else if levelLt l x then l :: x :: xs
  else x :: insertSorted l xs

||| Sort a list of levels, removing duplicates and dominated terms
covering
sortLevels : List Level -> List Level
sortLevels [] = []
sortLevels (x :: xs) = insertSorted x (sortLevels xs)

||| Build a right-associative Max tree from a sorted list
||| [a, b, c] => Max a (Max b c)
buildMax : List Level -> Level
buildMax [] = Zero
buildMax [x] = x
buildMax (x :: xs) = Max x (buildMax xs)

export covering
simplify : Level -> Level
simplify Zero = Zero
simplify (Succ l) = Succ (simplify l)
simplify (Max l1 l2) =
  let l1' = simplify l1
      l2' = simplify l2
      -- Flatten all nested Max into atoms
      atoms = flattenMax l1' ++ flattenMax l2'
      -- Filter out Zero (max 0 x = x)
      nonZero = filter (\x => not (isZero x)) atoms
      -- Sort and deduplicate
      sorted = sortLevels nonZero
  in buildMax sorted
simplify (IMax l1 l2) =
  let l1' = simplify l1
      l2' = simplify l2
  in case l2' of
       Zero => Zero
       -- When l2' is Succ, IMax becomes Max (since Succ is always non-zero)
       (Succ _) => case (l1', l2') of
                     (Zero, _) => l2'
                     (_, Zero) => l1'  -- won't happen but needed for coverage
                     _ => if l1' == l2' then l1' else Max l1' l2'
       -- When l2' is Max a b and either a or b is non-zero, IMax becomes Max
       -- IMax x (Max a b) = Max x (Max a b) when (Max a b) is non-zero
       (Max a b) =>
         if isNonZero a || isNonZero b
           then simplify (Max l1' l2')  -- Reduce to Max since l2' is non-zero
           else if l1' == l2' then l1' else IMax l1' l2'
       -- When l2' is IMax v w: imax u (imax v w) = max (imax u w) (imax v w)
       -- This distributes IMax over the inner IMax
       (IMax v w) =>
         simplify (Max (IMax l1' w) (IMax v w))
       -- When l2' is a Param, check various simplification rules
       (Param n) => case l1' of
                      -- Key rule: imax 1 u = u for all u
                      -- Proof: if u=0, imax 1 0 = 0 = u; if u>=1, imax 1 u = max 1 u = u
                      Succ Zero => l2'
                      -- IMax (IMax x u) u = max (imax x u) u = max x u (when u > 0)
                      -- And max x u = u when x <= u or more specifically when x = 0 or x = u
                      IMax innerL (Param m) =>
                        if n == m
                          then case simplify innerL of
                                 Zero => l2'  -- IMax (IMax 0 u) u = u
                                 Param p => if p == n then l2' else IMax l1' l2'  -- IMax (IMax u u) u = u
                                 _ => IMax l1' l2'
                          else if l1' == l2' then l1' else IMax l1' l2'
                      -- imax 0 u = u (since if u=0 result is 0=u, if u>0 result is max 0 u = u)
                      Zero => l2'
                      _ => if l1' == l2' then l1' else IMax l1' l2'
simplify (Param n) = Param n

||| Check if a name occurs in a level (for occur check)
public export
occursIn : Name -> Level -> Bool
occursIn _ Zero = False
occursIn n (Succ l) = occursIn n l
occursIn n (Max l1 l2) = occursIn n l1 || occursIn n l2
occursIn n (IMax l1 l2) = occursIn n l1 || occursIn n l2
occursIn n (Param m) = n == m

||| Check if a name occurs as a proper subterm in a level (for cycle detection)
|||
||| Returns False for the identity case: occursInProper n (Param n) = False
||| Returns True when n is nested inside Succ/Max/IMax.
|||
||| This distinguishes between:
||| - u := Param u (identity substitution, allowed)
||| - u := Succ (Param u) (creates cycle, rejected)
public export
occursInProper : Name -> Level -> Bool
occursInProper _ Zero = False
occursInProper n (Succ l) = occursIn n l  -- Any occurrence inside Succ is proper
occursInProper n (Max l1 l2) = occursIn n l1 || occursIn n l2  -- Inside Max is proper
occursInProper n (IMax l1 l2) = occursIn n l1 || occursIn n l2  -- Inside IMax is proper
occursInProper n (Param m) = False  -- Param n is NOT a proper subterm of itself

||| Substitute a parameter with a level (with proper occur check for cycle detection)
|||
||| Returns Nothing only if substitution would create a genuine cycle,
||| i.e., when n appears as a proper subterm of replacement.
|||
||| Identity substitutions like `u := Param u` are allowed (they are no-ops).
|||
||| Examples:
|||   substParamSafe "u" (Param "u") level = Just level  -- Identity, allowed
|||   substParamSafe "u" Zero level = Just (subst result)  -- Concrete, allowed
|||   substParamSafe "u" (Succ (Param "u")) level = Nothing  -- Cycle!
public export covering
substParamSafe : Name -> Level -> Level -> Maybe Level
substParamSafe n replacement level =
  -- Proper occur check: reject only if n is a proper subterm of replacement
  -- This allows identity substitutions like u := Param u (which are no-ops)
  if occursInProper n replacement
    then Nothing
    else Just (simplify (go level))  -- Simplify after substitution!
  where
    go : Level -> Level
    go Zero = Zero
    go (Succ l) = Succ (go l)
    go (Max l1 l2) = Max (go l1) (go l2)
    go (IMax l1 l2) = IMax (go l1) (go l2)
    go (Param m) = if n == m then replacement else Param m

||| Substitute a parameter with a level
||| NOTE: This version does not check for cycles. Use substParamSafe for untrusted input.
||| Simplifies the result to handle IMax properly.
public export covering
substParam : Name -> Level -> Level -> Level
substParam n replacement = simplify . go
  where
    go : Level -> Level
    go Zero = Zero
    go (Succ l) = Succ (go l)
    go (Max l1 l2) = Max (go l1) (go l2)
    go (IMax l1 l2) = IMax (go l1) (go l2)
    go (Param m) = if n == m then replacement else Param m

||| Substitute all parameters using a list of replacements (with occur check)
||| Returns Nothing if any substitution would create a cycle
public export covering
substParamsSafe : List (Name, Level) -> Level -> Maybe Level
substParamsSafe [] l = Just l
substParamsSafe ((n, repl) :: rest) l = do
  l' <- substParamSafe n repl l
  substParamsSafe rest l'

||| Substitute all parameters using a list of replacements
||| NOTE: This version does not check for cycles. Use substParamsSafe for untrusted input.
public export covering
substParams : List (Name, Level) -> Level -> Level
substParams ps l = foldl (\acc, (n, repl) => substParam n repl acc) l ps

||| Collect all parameter names in a level
public export
params : Level -> List Name
params Zero = []
params (Succ l) = params l
params (Max l1 l2) = params l1 ++ params l2
params (IMax l1 l2) = params l1 ++ params l2
params (Param n) = [n]
