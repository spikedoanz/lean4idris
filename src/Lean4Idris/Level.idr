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

||| Simplify a level expression
||| Applies basic normalization rules
export
simplify : Level -> Level
simplify Zero = Zero
simplify (Succ l) = Succ (simplify l)
simplify (Max l1 l2) =
  let l1' = simplify l1
      l2' = simplify l2
  in case (l1', l2') of
       (Zero, _) => l2'
       (_, Zero) => l1'
       _ => if l1' == l2' then l1' else Max l1' l2'
simplify (IMax l1 l2) =
  let l1' = simplify l1
      l2' = simplify l2
  in case l2' of
       Zero => Zero
       -- When l2' is Succ, IMax becomes Max, which is already simplified
       (Succ _) => case (l1', l2') of
                     (Zero, _) => l2'
                     (_, Zero) => l1'  -- won't happen but needed for coverage
                     _ => if l1' == l2' then l1' else Max l1' l2'
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
public export
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
public export
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
public export
substParamsSafe : List (Name, Level) -> Level -> Maybe Level
substParamsSafe [] l = Just l
substParamsSafe ((n, repl) :: rest) l = do
  l' <- substParamSafe n repl l
  substParamsSafe rest l'

||| Substitute all parameters using a list of replacements
||| NOTE: This version does not check for cycles. Use substParamsSafe for untrusted input.
public export
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
