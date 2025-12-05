||| Type checker for Lean 4 kernel
||| Re-exports all submodules for backwards compatibility.
module Lean4Idris.TypeChecker

import public Lean4Idris.TypeChecker.Monad
import public Lean4Idris.TypeChecker.Reduction
import public Lean4Idris.TypeChecker.Infer
import public Lean4Idris.TypeChecker.DefEq
import public Lean4Idris.TypeChecker.Validate
