||| Names for the Proof Layer
|||
||| Simple string-based names for global constants.
||| This mirrors the implementation's Name type but simplified.
module Lean4Idris.Proofs.Name

import Decidable.Equality

%default total

------------------------------------------------------------------------
-- Name Type
------------------------------------------------------------------------

||| A name is just a string for simplicity.
||| The implementation uses a more complex hierarchical name structure,
||| but for proofs we only need equality checking.
public export
Name : Type
Name = String

------------------------------------------------------------------------
-- Decidable Equality
------------------------------------------------------------------------

||| Names have decidable equality (inherited from String)
public export
nameEq : (n1 : Name) -> (n2 : Name) -> Dec (n1 = n2)
nameEq n1 n2 = decEq n1 n2
