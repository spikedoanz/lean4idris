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

||| Add n Succ wrappers to a level
||| e.g., addOffset 2 (Param u) = Succ (Succ (Param u))
addOffset : Nat -> Level -> Level
addOffset Z l = l
addOffset (S n) l = Succ (addOffset n l)

||| Subtract n Succ wrappers from a level
||| Uses getOffsetBase to extract offset, then rebuilds with reduced offset
||| e.g., subtractOffset 1 (Succ (Succ (Param u))) = Succ (Param u)
subtractOffset : Nat -> Level -> Level
subtractOffset n l =
  let (offset, base) = getOffsetBase l
  in addOffset (minus offset n) base

||| Find the minimum offset (Succ count) across a list of levels
||| Returns 0 for empty list or if any atom has no Succ wrapper
findMinOffset : List Level -> Nat
findMinOffset [] = 0
findMinOffset (x :: xs) =
  let (offset, _) = getOffsetBase x
  in foldl (\acc, l => let (o, _) = getOffsetBase l in min acc o) offset xs

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
      -- Factor out common Succ prefix: max (a+n) (b+n) = (max a b) + n
      minOff = findMinOffset sorted
      stripped = if minOff > 0
                 then map (subtractOffset minOff) sorted
                 else sorted
      base = buildMax stripped
  in addOffset minOff base
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

------------------------------------------------------------------------
-- Level Normalization (Géran's Canonical Form)
--
-- Based on "A Canonical Form for Universe Levels in Impredicative Type Theory"
-- by Yoan Géran, and the implementation in lean4lean.
--
-- The normal form represents a level as a collection of "nodes", where each
-- node is indexed by an "imax path" (a sorted list of parameter names that
-- represents nested imax conditions).
------------------------------------------------------------------------

||| Variable node: a parameter with an offset
||| Represents terms like `u + 3`
public export
record VarNode where
  constructor MkVarNode
  var : Name
  offset : Nat

public export
Eq VarNode where
  v1 == v2 = v1.var == v2.var && v1.offset == v2.offset

public export
Show VarNode where
  show v = show v.var ++ (if v.offset == 0 then "" else "+" ++ show v.offset)

||| Compare VarNodes by name first, then offset
public export
compareVarNode : VarNode -> VarNode -> Ordering
compareVarNode v1 v2 = case compareName v1.var v2.var of
  EQ => compare v1.offset v2.offset
  c => c
  where
    compareName : Name -> Name -> Ordering
    compareName n1 n2 = compare (show n1) (show n2)

||| Normalized node: represents one component of the canonical form
||| Each node is associated with an "imax path" (List Name) in NormLevel
public export
record NormNode where
  constructor MkNormNode
  const : Nat           -- constant term (e.g., 3 in "max 3 u")
  vars : List VarNode   -- variable terms with offsets, sorted by name

public export
Eq NormNode where
  n1 == n2 = n1.const == n2.const && n1.vars == n2.vars

public export
Show NormNode where
  show n = "NormNode{const=" ++ show n.const ++ ", vars=" ++ show n.vars ++ "}"

||| Default empty node
public export
defaultNormNode : NormNode
defaultNormNode = MkNormNode 0 []

||| Normalized level: a map from imax paths to nodes
||| The path represents the condition under which this node applies.
||| Empty path [] is the unconditional part.
||| Path [u] means "when u > 0".
||| Path [u, v] means "when u > 0 and v > 0".
public export
NormLevel : Type
NormLevel = List (List Name, NormNode)

showNormLevelEntries : List (List Name, NormNode) -> String
showNormLevelEntries [] = ""
showNormLevelEntries [(p, n)] = "(" ++ show p ++ ", " ++ show n ++ ")"
showNormLevelEntries ((p, n) :: rest) = "(" ++ show p ++ ", " ++ show n ++ "), " ++ showNormLevelEntries rest

public export
Show NormLevel where
  show [] = "NormLevel[]"
  show xs = "NormLevel[" ++ showNormLevelEntries xs ++ "]"

||| Compare two lists of names lexicographically
comparePath : List Name -> List Name -> Ordering
comparePath [] [] = EQ
comparePath [] (_ :: _) = LT
comparePath (_ :: _) [] = GT
comparePath (n1 :: ns1) (n2 :: ns2) = case compare (show n1) (show n2) of
  EQ => comparePath ns1 ns2
  c => c

||| Insert into path-sorted list, replacing if path exists
insertNormLevel : List Name -> NormNode -> NormLevel -> NormLevel
insertNormLevel path node [] = [(path, node)]
insertNormLevel path node ((p, n) :: rest) = case comparePath path p of
  LT => (path, node) :: (p, n) :: rest
  EQ => (path, node) :: rest
  GT => (p, n) :: insertNormLevel path node rest

||| Lookup a path in NormLevel
lookupNormLevel : List Name -> NormLevel -> Maybe NormNode
lookupNormLevel path [] = Nothing
lookupNormLevel path ((p, n) :: rest) = case comparePath path p of
  EQ => Just n
  _ => lookupNormLevel path rest

||| Modify a node at a path (or insert default if not present)
modifyNormLevel : List Name -> (NormNode -> NormNode) -> NormLevel -> NormLevel
modifyNormLevel path f nl = case lookupNormLevel path nl of
  Just n => insertNormLevel path (f n) nl
  Nothing => insertNormLevel path (f defaultNormNode) nl

||| Add a variable to a sorted list of VarNodes
||| If variable already exists, keep maximum offset
addVarToList : Name -> Nat -> List VarNode -> List VarNode
addVarToList v k [] = [MkVarNode v k]
addVarToList v k (vn :: rest) = case compare (show v) (show vn.var) of
  LT => MkVarNode v k :: vn :: rest
  EQ => MkVarNode v (max k vn.offset) :: rest
  GT => vn :: addVarToList v k rest

||| Add a variable term to a NormLevel at a given path
addVar : Name -> Nat -> List Name -> NormLevel -> NormLevel
addVar v k path = modifyNormLevel path (\n => { vars := addVarToList v k n.vars } n)

||| Add a node entry for a variable at a given path
addNode : Name -> List Name -> NormLevel -> NormLevel
addNode v path = modifyNormLevel path (\n => { vars := addVarToList v 0 n.vars } n)

||| Add a constant term to a NormLevel at a given path
||| Constants 0 and 1 at non-empty paths are trivially dominated, so skip them
addConst : Nat -> List Name -> NormLevel -> NormLevel
addConst k path nl =
  if k == 0 || (k == 1 && not (isNil path))
    then nl
    else modifyNormLevel path (\n => { const := max k n.const } n) nl

||| Insert a name into a sorted path, returning Nothing if already present
orderedInsertName : Name -> List Name -> Maybe (List Name)
orderedInsertName n [] = Just [n]
orderedInsertName n (m :: ms) = case compare (show n) (show m) of
  LT => Just (n :: m :: ms)
  EQ => Nothing  -- Already present
  GT => map (m ::) (orderedInsertName n ms)

||| Core normalization function
||| Recursively processes a level, building up the normalized representation
|||
||| @l The level to normalize
||| @path The current imax path (sorted list of parameters we're "inside")
||| @k The current offset (number of Succ wrappers)
||| @acc The accumulated normal form
export covering
normalizeAux : (l : Level) -> (path : List Name) -> (k : Nat) -> (acc : NormLevel) -> NormLevel
normalizeAux Zero path k acc = addConst k path acc
normalizeAux (Succ u) path k acc = normalizeAux u path (S k) acc
normalizeAux (Max u v) path k acc = normalizeAux v path k (normalizeAux u path k acc)
-- imax u 0 = 0, so just add constant
normalizeAux (IMax _ Zero) path k acc = addConst k path acc
-- imax u (succ v) = max u (succ v), since succ v is always > 0
normalizeAux (IMax u (Succ v)) path k acc =
  normalizeAux v path (S k) (normalizeAux u path k acc)
-- imax u (max v w) = max (imax u v) (imax u w)
normalizeAux (IMax u (Max v w)) path k acc =
  normalizeAux (IMax u w) path k (normalizeAux (IMax u v) path k acc)
-- imax u (imax v w) = max (imax u w) (imax v w)
normalizeAux (IMax u (IMax v w)) path k acc =
  normalizeAux (IMax v w) path k (normalizeAux (IMax u w) path k acc)
-- imax u (param v): enter the "v > 0" branch
normalizeAux (IMax u (Param v)) path k acc =
  case orderedInsertName v path of
    Just path' => normalizeAux u path' k (addNode v path' acc)
    Nothing => normalizeAux u path k acc  -- v already in path, skip
-- param v: add variable term
normalizeAux (Param v) path k acc =
  case orderedInsertName v path of
    Just path' =>
      let acc' = addConst k path (addNode v path' acc)
      in if k == 0 then acc' else addVar v k path' acc'
    Nothing =>
      if k == 0 then acc else addVar v k path acc

||| Check if path1 is a subset of path2 (both sorted)
isSubsetPath : List Name -> List Name -> Bool
isSubsetPath [] _ = True
isSubsetPath (_ :: _) [] = False
isSubsetPath (x :: xs) (y :: ys) = case compare (show x) (show y) of
  LT => False  -- x not in ys
  EQ => isSubsetPath xs ys
  GT => isSubsetPath (x :: xs) ys

||| Remove variables from v1 that are dominated by v2
||| Both lists must be sorted by variable name
subsumeVars : List VarNode -> List VarNode -> List VarNode
subsumeVars [] _ = []
subsumeVars xs [] = xs
subsumeVars (x :: xs) (y :: ys) = case compare (show x.var) (show y.var) of
  LT => x :: subsumeVars xs (y :: ys)
  EQ => if x.offset <= y.offset
          then subsumeVars xs ys  -- x dominated by y, remove it
          else x :: subsumeVars xs ys
  GT => subsumeVars (x :: xs) ys

||| Check if vars1 <= vars2 (for level ordering)
leVars : List VarNode -> List VarNode -> Bool
leVars [] _ = True
leVars (_ :: _) [] = False
leVars (x :: xs) (y :: ys) = case compare (show x.var) (show y.var) of
  LT => False  -- x.var not in ys
  EQ => x.offset <= y.offset && leVars xs ys
  GT => leVars (x :: xs) ys

||| Get max offset from a list of VarNodes
maxVarOffset : List VarNode -> Nat
maxVarOffset [] = 0
maxVarOffset (v :: vs) = foldl (\a, vn => max a vn.offset) v.offset vs

||| Check if n2 at p2 subsumes parts of n1 at p1
subsumeBy : List Name -> NormNode -> (List Name, NormNode) -> NormNode
subsumeBy p1 n1 (p2, n2) =
  if not (isSubsetPath p2 p1) then n1
  else
    let same = length p1 == length p2
        -- Remove constant if dominated
        n1' = if n1.const == 0 ||
                 ((same || n1.const > n2.const) &&
                  (isNil n2.vars || n1.const > maxVarOffset n1.vars + 1))
                then n1
                else { const := 0 } n1
        -- Remove dominated variables
        n1'' = if same || isNil n2.vars then n1'
               else { vars := subsumeVars n1'.vars n2.vars } n1'
    in n1''

||| Process a single node, removing terms dominated by other nodes
processNode : NormLevel -> (List Name, NormNode) -> (List Name, NormNode)
processNode nl (p1, n1) =
  let n1' = foldl (subsumeBy p1) n1 nl
  in (p1, n1')

||| Apply subsumption to remove dominated terms
||| For each node n1 at path p1, check if any other node n2 at path p2
||| dominates it (when p2 is a subset of p1)
export
subsumption : NormLevel -> NormLevel
subsumption acc = map (processNode acc) acc

||| Normalize a level to canonical form
export covering
normalize : Level -> NormLevel
normalize l =
  let initial = insertNormLevel [] defaultNormNode []
  in subsumption (normalizeAux l [] 0 initial)

||| Check if two NormLevels are equal
export
normLevelEq : NormLevel -> NormLevel -> Bool
normLevelEq nl1 nl2 =
  all (\(p, n) => lookupNormLevel p nl2 == Just n) nl1 &&
  all (\(p, n) => lookupNormLevel p nl1 == Just n) nl2

||| Check if two levels are equivalent using canonical form normalization
||| This is the main entry point for level comparison
export covering
isLevelEquiv : Level -> Level -> Bool
isLevelEquiv u v =
  u == v || normLevelEq (normalize u) (normalize v)

||| Check if two lists of levels are pairwise equivalent
export covering
isLevelEquivList : List Level -> List Level -> Bool
isLevelEquivList [] [] = True
isLevelEquivList (u :: us) (v :: vs) = isLevelEquiv u v && isLevelEquivList us vs
isLevelEquivList _ _ = False
