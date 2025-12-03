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

||| Substitute a parameter with a level
public export
substParam : Name -> Level -> Level -> Level
substParam n replacement = go
  where
    go : Level -> Level
    go Zero = Zero
    go (Succ l) = Succ (go l)
    go (Max l1 l2) = Max (go l1) (go l2)
    go (IMax l1 l2) = IMax (go l1) (go l2)
    go (Param m) = if n == m then replacement else Param m

||| Substitute all parameters using a list of replacements
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
