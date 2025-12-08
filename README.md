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

```
Commit hash: 9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3
------------------------------------------------------------
Total:    24668
OK:    24045
Fail:      621
OK%: 97.48%
------------------------------------------------------------
Hang:
Nat.testBit_one_zero...
String.bytes_append...
------------------------------------------------------------
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.String.Basic.export.log
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.Option.Basic.export.log
TOTAL 4201 OK 4 FAIL 46 TIMEOUT 0 CACHED 4151 OK% 98.9
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Prelude.export.log
TOTAL 2046 OK 4 FAIL 21 TIMEOUT 0 CACHED 2021 OK% 98.9
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.Nat.Lemmas.export.log
TOTAL 11126 OK 2261 FAIL 392 TIMEOUT 0 CACHED 8473 OK% 96.4
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.Char.Basic.export.log
TOTAL 5333 OK 4 FAIL 144 TIMEOUT 0 CACHED 5185 OK% 97.2
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.Int.Basic.export.log
TOTAL 5221 OK 4 FAIL 114 TIMEOUT 0 CACHED 5103 OK% 97.8
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Classical.export.log
TOTAL 8127 OK 7873 FAIL 254 TIMEOUT 0 CACHED 0 OK% 96.8
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.Nat.Basic.export.log
TOTAL 4599 OK 4 FAIL 106 TIMEOUT 0 CACHED 4489 OK% 97.6
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Core.export.log
TOTAL 3761 OK 4 FAIL 33 TIMEOUT 0 CACHED 3724 OK% 99.1
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.List.Lemmas.export.log
TOTAL 10953 OK 2651 FAIL 433 TIMEOUT 0 CACHED 7869 OK% 96.0
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.PropLemmas.export.log
TOTAL 8068 OK 4 FAIL 246 TIMEOUT 0 CACHED 7818 OK% 96.9
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.Fin.Basic.export.log
TOTAL 5222 OK 4 FAIL 130 TIMEOUT 0 CACHED 5088 OK% 97.5
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.Array.Basic.export.log
TOTAL 7175 OK 4 FAIL 241 TIMEOUT 0 CACHED 6930 OK% 96.6
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.UInt.Basic.export.log
9d55ff36e07e60cfa2d558e9ad3a44c5f1bbddc3/Init.Data.List.Basic.export.log
TOTAL 5675 OK 4 FAIL 159 TIMEOUT 0 CACHED 5512 OK% 97.1
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
