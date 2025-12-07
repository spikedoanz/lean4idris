# lean4idris

A Lean 4 type checker written in Idris 2, targeting the [lean4export](https://github.com/leanprover/lean4export) format.

## Status

- [x] Parser for names, levels, expressions, declarations
- [x] Well-scoped expressions (indexed by depth)
- [x] Type inference (`inferType`) for closed terms
- [x] Type inference (`inferTypeOpen`) for open terms with local context
- [x] Reduction (`whnf`) - beta, let, delta, iota, projection, and quotient reduction
- [x] Definitional equality (`isDefEq`) - structural + beta + delta + eta
- [x] Delta reduction with reducibility hints (abbrev unfolds, opaque doesn't)
- [x] Eta expansion (λx. f x = f) [x] Iota reduction (recursor computation when major premise is a constructor)
- [x] Projection reduction (struct.field when struct is a constructor)
- [x] Quotient reduction (Quot.lift f h (Quot.mk r a) → f a)
- [x] Universe level normalization (simplify imax, max)
- [x] Local context for typing under binders
- [x] Proof irrelevance (proofs of Prop are definitionally equal)
- [x] Declaration validation (axioms, definitions, theorems)
- [ ] Completeness.
  - [ ] tier 1 :~97%
  - [ ] tier 2
  - [ ] tier 3
  - [ ] tier 4
  - [ ] tier 5
  - [ ] tier 6
  - [ ] tier 7
  - [ ] tier 8
  - [ ] tier 9
  - [ ] tier 10


## Coverage
> note: by convention, lean exports are stored in ~/.cache/lean4exports/

to get commands to manually check the coverage of the current built checker, run `./manual.sh`

> note to be careful to use a directory where it won't be likely to be overwritten / overwrite
something else /tmp is used by the human, if you're claude, please use the local dir instead
and clean up afterwards

example:

```sh
./build/exec/lean4idris --no-cache /Users/spike/.cache/lean4exports/tier01-init/Init.PropLemmas.export | tee /tmp/Init.PropLemmas.export.log
```

to obtain failures, just grep for them from the log file 
```sh
cat /tmp/Init.PropLemmas.export.log | grep CHECKING | grep FAIL
```

> this obviously also works for `ok`
> also useful, is to inverse grep for `ok` and `FAIL` which will get theorems which are stuck

the last time coverage for tier01 was checked was in e7ef3af7b17dff418dce3e3951a5908e1c797f2b

current failed checks are stored in FAIL.txt
> these don't include the ones that come after the hanged checks, so it might
be undercounting

current hanged checks are stored in HANG.txt
> hang also just takes a very long time, so hanging doesn't necessarily
mean fail, it more likely means inefficiency on the part of the type checker

```
tier01-init/Init.Classical.export
> hangs
tier01-init/Init.Core.export
TOTAL 3761 OK 27 FAIL 48 TIMEOUT 0 CACHED 3686 OK% 98.7
tier01-init/Init.Data.Array.Basic.export
> hangs
tier01-init/Init.Data.Char.Basic.export
> hangs
tier01-init/Init.Data.Fin.Basic.export
TOTAL 5222 OK 13 FAIL 145 TIMEOUT 0 CACHED 5064 OK% 97.2
tier01-init/Init.Data.Int.Basic.export
TOTAL 5221 OK 4 FAIL 129 TIMEOUT 0 CACHED 5088 OK% 97.5
tier01-init/Init.Data.List.Basic.export
TOTAL 5675 OK 5 FAIL 203 TIMEOUT 0 CACHED 5467 OK% 96.4
tier01-init/Init.Data.List.Lemmas.export
tier01-init/Init.Data.Nat.Basic.export
TOTAL 4599 OK 4 FAIL 120 TIMEOUT 0 CACHED 4475 OK% 97.3
tier01-init/Init.Data.Nat.Lemmas.export
tier01-init/Init.Data.Option.Basic.export
TOTAL 4201 OK 4 FAIL 60 TIMEOUT 0 CACHED 4137 OK% 98.5
tier01-init/Init.Data.String.Basic.export
> hangs
tier01-init/Init.Data.UInt.Basic.export
> hangs
tier01-init/Init.Prelude.export
TOTAL 2046 OK 8 FAIL 36 TIMEOUT 0 CACHED 2002 OK% 98.2
tier01-init/Init.PropLemmas.export
> hangs

tier02-std/Std.Data.DHashMap.export
tier02-std/Std.Data.DTreeMap.export
tier02-std/Std.Data.HashMap.export
tier02-std/Std.Data.HashSet.export
tier02-std/Std.Data.TreeMap.export
tier02-std/Std.Data.TreeSet.export
tier02-std/Std.Sat.CNF.export
tier02-std/Std.Tactic.BVDecide.export

tier03-lean/Lean.Data.Name.export
tier03-lean/Lean.Data.PersistentHashMap.export
tier03-lean/Lean.Data.RBMap.export
tier03-lean/Lean.Declaration.export
tier03-lean/Lean.Elab.Command.export
tier03-lean/Lean.Elab.Term.export
tier03-lean/Lean.Environment.export
tier03-lean/Lean.Expr.export
tier03-lean/Lean.Level.export
tier03-lean/Lean.LocalContext.export
tier03-lean/Lean.Meta.Basic.export
tier03-lean/Lean.Meta.InferType.export
tier03-lean/Lean.Meta.Reduce.export
tier03-lean/Lean.Meta.WHNF.export

tier04-batteries-data/Batteries.Data.Array.Basic.export

tier04-batteries-data/Batteries.Data.Array.Lemmas.export
tier04-batteries-data/Batteries.Data.BitVec.Basic.export
tier04-batteries-data/Batteries.Data.Fin.Basic.export
tier04-batteries-data/Batteries.Data.Fin.Lemmas.export
tier04-batteries-data/Batteries.Data.HashMap.Basic.export
tier04-batteries-data/Batteries.Data.Int.export
tier04-batteries-data/Batteries.Data.List.Basic.export
tier04-batteries-data/Batteries.Data.List.Lemmas.export
tier04-batteries-data/Batteries.Data.Nat.Basic.export
tier04-batteries-data/Batteries.Data.Nat.Lemmas.export
tier04-batteries-data/Batteries.Data.RBMap.Basic.export
tier04-batteries-data/Batteries.Data.String.Basic.export
tier04-batteries-data/Batteries.Data.Vector.Basic.export

tier05-batteries-tactic/Batteries.Lean.HashMap.export
tier05-batteries-tactic/Batteries.Lean.Meta.Basic.export
tier05-batteries-tactic/Batteries.Lean.Meta.Expr.export
tier05-batteries-tactic/Batteries.Lean.Syntax.export
tier05-batteries-tactic/Batteries.Tactic.Alias.export
tier05-batteries-tactic/Batteries.Tactic.Basic.export
tier05-batteries-tactic/Batteries.Tactic.Exact.export
tier05-batteries-tactic/Batteries.Tactic.Lint.Basic.export

tier06-mathlib-data/Mathlib.Data.Bool.Basic.export
tier06-mathlib-data/Mathlib.Data.Fin.Basic.export
tier06-mathlib-data/Mathlib.Data.Int.Basic.export
tier06-mathlib-data/Mathlib.Data.Int.Order.Basic.export
tier06-mathlib-data/Mathlib.Data.List.Basic.export
tier06-mathlib-data/Mathlib.Data.Nat.Basic.export
tier06-mathlib-data/Mathlib.Data.Nat.Prime.Basic.export
tier06-mathlib-data/Mathlib.Data.Option.Basic.export
tier06-mathlib-data/Mathlib.Logic.Basic.export

tier07-mathlib-algebra/Mathlib.Algebra.Field.Basic.export
tier07-mathlib-algebra/Mathlib.Algebra.Group.Basic.export
tier07-mathlib-algebra/Mathlib.Algebra.Group.Defs.export
tier07-mathlib-algebra/Mathlib.Algebra.Order.Monoid.Basic.export
tier07-mathlib-algebra/Mathlib.Algebra.Ring.Basic.export
tier07-mathlib-algebra/Mathlib.Algebra.Ring.Defs.export
tier07-mathlib-algebra/Mathlib.GroupTheory.Perm.Basic.export

tier08-mathlib-analysis/Mathlib.Analysis.Normed.Field.Basic.export
tier08-mathlib-analysis/Mathlib.Analysis.SpecialFunctions.Pow.Real.export
tier08-mathlib-analysis/Mathlib.Order.Filter.Basic.export
tier08-mathlib-analysis/Mathlib.Topology.Basic.export
tier08-mathlib-analysis/Mathlib.Topology.MetricSpace.Basic.export
tier08-mathlib-analysis/Mathlib.Topology.Order.export

tier09-mathlib-category/Mathlib.CategoryTheory.Category.Basic.export
tier09-mathlib-category/Mathlib.CategoryTheory.Functor.Basic.export
tier09-mathlib-category/Mathlib.CategoryTheory.Iso.export
tier09-mathlib-category/Mathlib.CategoryTheory.Limits.Shapes.Terminal.export
tier09-mathlib-category/Mathlib.CategoryTheory.NatTrans.export
tier09-mathlib-category/Mathlib.CategoryTheory.Yoneda.export

tier10-mathlib-advanced/Mathlib.Data.Tree.Basic.export
tier01-init/Init.Data.UInt.Basic.export
tier10-mathlib-advanced/Mathlib.Data.W.Basic.export
tier10-mathlib-advanced/Mathlib.GroupTheory.QuotientGroup.Basic.export
tier10-mathlib-advanced/Mathlib.Logic.Equiv.Basic.export
tier10-mathlib-advanced/Mathlib.SetTheory.Cardinal.Basic.export
tier10-mathlib-advanced/Mathlib.SetTheory.Ordinal.Basic.export
```


Known blocking issues tracked in [GitHub Issues](https://github.com/spikedoanz/lean4idris/issues).


## Current slow checks

```
Checking: Char.isValidChar_zero...
Checking: Array.eraseIdx.induct...
Checking: Lean.Omega.Constraint.combo_sat...
Checking: Nat.testBit_or...
Checking: Lean.Omega.Constraint.combo_sat...
Checking: Char.isValidChar_zero...
```



### Running coverage tests

```bash
# Type check an export file, continue on errors, save full output
pack run lean4idris -c test/exports/tier01-init/Init.Prelude.export 2>&1 | tee results/Init.Prelude.txt

# Just see the summary
grep "Summary:" results/Init.Prelude.txt

# See all failures
grep "FAIL" results/Init.Prelude.txt
```

## Build

Requires [pack](https://github.com/stefan-hoeck/idris2-pack).

```bash
pack build lean4idris        # build library
pack build lean4idris-test   # build tests
pack run lean4idris-test     # run tests
```

## Usage

```idris
import Lean4Idris.Export.Parser
import Lean4Idris.Pretty

main : IO ()
main = do
  let input = "0.0.0\n1 #NS 0 Nat\n1 #US 0\n1 #ES 1\n"
  case parseExport input of
    Left err => putStrLn err
    Right st => do
      for_ (getNames st) $ \(i, n) => putStrLn $ show n
      for_ (getExprs st) $ \(i, e) => putStrLn $ ppClosedExpr e
```

## Project Structure

```
src/Lean4Idris/
  Name.idr          -- Hierarchical names
  Level.idr         -- Universe levels
  Expr.idr          -- Well-scoped expressions (Expr n indexed by scope depth)
  Decl.idr          -- Declarations
  Subst.idr         -- Substitution operations
  TypeChecker.idr   -- Core type checking (inferType, whnf, isDefEq)
  Pretty.idr        -- Pretty printing
  Export/
    Token.idr       -- Export format tokens
    Lexer.idr       -- Tokenizer
    Parser.idr      -- Parser
```

## References

- [lean4lean](https://github.com/digama0/lean4lean) - Lean kernel in Lean
- [nanoda_lib](https://github.com/ammkrn/nanoda_lib) - Lean type checker in Rust
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/) - Documentation
