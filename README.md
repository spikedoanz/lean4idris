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
  - [ ] tier 1
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

Type checking coverage on Lean 4 export files:

| Export File       | Decls | Passed | Failed | Coverage |
|-------------      |--------------|--------|--------|----------|
| Init.Prelude      | 2036  | 1832 | 204 | 90.0% |
| Init.Core         | 3748  | 3402 | 346 | 90.8% |
| Init.Classical    | 8044  | 6577 | 1467 | 81.8% |
| Init.Data.Nat.Basic | 4586 | 4050 | 536 | 88.3% |


## tier 1

```
> TODO: this should be automated in CI
> should just export it to {githash}_{pathtoexport}.log
```

```
tested on 564756727e377e7fe640b0932dcd690e027cb72d
test/exports/tier01-init/
test/exports/tier01-init/Init.Classical.export
    > timeout
test/exports/tier01-init/Init.Core.export
    > 3465 passed, 283 failed
test/exports/tier01-init/Init.Data.Array.Basic.export
    > 5930 passed, 1195 failed
test/exports/tier01-init/Init.Data.Char.Basic.export
    > 4736 passed, 584 failed
test/exports/tier01-init/Init.Data.Fin.Basic.export
    > 4661 passed, 548 failed
test/exports/tier01-init/Init.Data.Int.Basic.export
    > 4692 passed, 516 failed
test/exports/tier01-init/Init.Data.List.Basic.export
    > 4897 passed, 765 failed
test/exports/tier01-init/Init.Data.List.Lemmas.export
test/exports/tier01-init/Init.Data.Nat.Basic.export
    > 4164 passed, 422 failed
test/exports/tier01-init/Init.Data.Nat.Lemmas.export
    > 8555 passed, 2488 failed
test/exports/tier01-init/Init.Data.Option.Basic.export
    > 
test/exports/tier01-init/Init.Data.String.Basic.export
test/exports/tier01-init/Init.Data.UInt.Basic.export
test/exports/tier01-init/Init.Prelude.export
    > 1891 passed, 145 failed
test/exports/tier01-init/Init.PropLemmas.export
    > 6688 passed, 1297 failed

test/exports/tier02-std
test/exports/tier02-std/Std.Data.DHashMap.export
test/exports/tier02-std/Std.Data.DTreeMap.export
test/exports/tier02-std/Std.Data.HashMap.export
test/exports/tier02-std/Std.Data.HashSet.export
test/exports/tier02-std/Std.Data.TreeMap.export
test/exports/tier02-std/Std.Data.TreeSet.export
test/exports/tier02-std/Std.Sat.CNF.export
test/exports/tier02-std/Std.Tactic.BVDecide.export

test/exports/tier03-lean
test/exports/tier03-lean/Lean.Data.Name.export
test/exports/tier03-lean/Lean.Data.PersistentHashMap.export
test/exports/tier03-lean/Lean.Data.RBMap.export
test/exports/tier03-lean/Lean.Declaration.export
test/exports/tier03-lean/Lean.Elab.Command.export
test/exports/tier03-lean/Lean.Elab.Term.export
test/exports/tier03-lean/Lean.Environment.export
test/exports/tier03-lean/Lean.Expr.export
test/exports/tier03-lean/Lean.Level.export
test/exports/tier03-lean/Lean.LocalContext.export
test/exports/tier03-lean/Lean.Meta.Basic.export
test/exports/tier03-lean/Lean.Meta.InferType.export
test/exports/tier03-lean/Lean.Meta.Reduce.export
test/exports/tier03-lean/Lean.Meta.WHNF.export

test/exports/tier04-batteries-data
test/exports/tier04-batteries-data/Batteries.Data.Array.Basic.export

test/exports/tier04-batteries-data/Batteries.Data.Array.Lemmas.export
test/exports/tier04-batteries-data/Batteries.Data.BitVec.Basic.export
test/exports/tier04-batteries-data/Batteries.Data.Fin.Basic.export
test/exports/tier04-batteries-data/Batteries.Data.Fin.Lemmas.export
test/exports/tier04-batteries-data/Batteries.Data.HashMap.Basic.export
test/exports/tier04-batteries-data/Batteries.Data.Int.export
test/exports/tier04-batteries-data/Batteries.Data.List.Basic.export
test/exports/tier04-batteries-data/Batteries.Data.List.Lemmas.export
test/exports/tier04-batteries-data/Batteries.Data.Nat.Basic.export
test/exports/tier04-batteries-data/Batteries.Data.Nat.Lemmas.export
test/exports/tier04-batteries-data/Batteries.Data.RBMap.Basic.export
test/exports/tier04-batteries-data/Batteries.Data.String.Basic.export
test/exports/tier04-batteries-data/Batteries.Data.Vector.Basic.export

test/exports/tier05-batteries-tactic
test/exports/tier05-batteries-tactic/Batteries.Lean.HashMap.export
test/exports/tier05-batteries-tactic/Batteries.Lean.Meta.Basic.export
test/exports/tier05-batteries-tactic/Batteries.Lean.Meta.Expr.export
test/exports/tier05-batteries-tactic/Batteries.Lean.Syntax.export
test/exports/tier05-batteries-tactic/Batteries.Tactic.Alias.export
test/exports/tier05-batteries-tactic/Batteries.Tactic.Basic.export
test/exports/tier05-batteries-tactic/Batteries.Tactic.Exact.export
test/exports/tier05-batteries-tactic/Batteries.Tactic.Lint.Basic.export

test/exports/tier06-mathlib-data
test/exports/tier06-mathlib-data/Mathlib.Data.Bool.Basic.export
test/exports/tier06-mathlib-data/Mathlib.Data.Fin.Basic.export
test/exports/tier06-mathlib-data/Mathlib.Data.Int.Basic.export
test/exports/tier06-mathlib-data/Mathlib.Data.Int.Order.Basic.export
test/exports/tier06-mathlib-data/Mathlib.Data.List.Basic.export
test/exports/tier06-mathlib-data/Mathlib.Data.Nat.Basic.export
test/exports/tier06-mathlib-data/Mathlib.Data.Nat.Prime.Basic.export
test/exports/tier06-mathlib-data/Mathlib.Data.Option.Basic.export
test/exports/tier06-mathlib-data/Mathlib.Logic.Basic.export

test/exports/tier07-mathlib-algebra
test/exports/tier07-mathlib-algebra/Mathlib.Algebra.Field.Basic.export
test/exports/tier07-mathlib-algebra/Mathlib.Algebra.Group.Basic.export
test/exports/tier07-mathlib-algebra/Mathlib.Algebra.Group.Defs.export
test/exports/tier07-mathlib-algebra/Mathlib.Algebra.Order.Monoid.Basic.export
test/exports/tier07-mathlib-algebra/Mathlib.Algebra.Ring.Basic.export
test/exports/tier07-mathlib-algebra/Mathlib.Algebra.Ring.Defs.export
test/exports/tier07-mathlib-algebra/Mathlib.GroupTheory.Perm.Basic.export

test/exports/tier08-mathlib-analysis
test/exports/tier08-mathlib-analysis/Mathlib.Analysis.Normed.Field.Basic.export
test/exports/tier08-mathlib-analysis/Mathlib.Analysis.SpecialFunctions.Pow.Real.export
test/exports/tier08-mathlib-analysis/Mathlib.Order.Filter.Basic.export
test/exports/tier08-mathlib-analysis/Mathlib.Topology.Basic.export
test/exports/tier08-mathlib-analysis/Mathlib.Topology.MetricSpace.Basic.export
test/exports/tier08-mathlib-analysis/Mathlib.Topology.Order.export

test/exports/tier09-mathlib-category
test/exports/tier09-mathlib-category/Mathlib.CategoryTheory.Category.Basic.export
test/exports/tier09-mathlib-category/Mathlib.CategoryTheory.Functor.Basic.export
test/exports/tier09-mathlib-category/Mathlib.CategoryTheory.Iso.export
test/exports/tier09-mathlib-category/Mathlib.CategoryTheory.Limits.Shapes.Terminal.export
test/exports/tier09-mathlib-category/Mathlib.CategoryTheory.NatTrans.export
test/exports/tier09-mathlib-category/Mathlib.CategoryTheory.Yoneda.export

test/exports/tier10-mathlib-advanced
test/exports/tier10-mathlib-advanced/Mathlib.Data.Tree.Basic.export
test/exports/tier01-init/Init.Data.UInt.Basic.export
test/exports/tier10-mathlib-advanced/Mathlib.Data.W.Basic.export
test/exports/tier10-mathlib-advanced/Mathlib.GroupTheory.QuotientGroup.Basic.export
test/exports/tier10-mathlib-advanced/Mathlib.Logic.Equiv.Basic.export
test/exports/tier10-mathlib-advanced/Mathlib.SetTheory.Cardinal.Basic.export
test/exports/tier10-mathlib-advanced/Mathlib.SetTheory.Ordinal.Basic.export
```


Known blocking issues tracked in [GitHub Issues](https://github.com/spikedoanz/lean4idris/issues).

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
