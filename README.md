# lean4idris

A Lean 4 type checker written in Idris 2, targeting the [lean4export](https://github.com/leanprover/lean4export) format.

## Status

**Milestone 8 complete**: Declaration validation.

- [x] Parser for names, levels, expressions, declarations
- [x] Well-scoped expressions (indexed by depth)
- [x] Type inference (`inferType`) for closed terms
- [x] Type inference (`inferTypeOpen`) for open terms with local context
- [x] Reduction (`whnf`) - beta, let, delta, iota, projection, and quotient reduction
- [x] Definitional equality (`isDefEq`) - structural + beta + delta + eta
- [x] Delta reduction with reducibility hints (abbrev unfolds, opaque doesn't)
- [x] Eta expansion (λx. f x = f)
- [x] Iota reduction (recursor computation when major premise is a constructor)
- [x] Projection reduction (struct.field when struct is a constructor)
- [x] Quotient reduction (Quot.lift f h (Quot.mk r a) → f a)
- [x] Universe level normalization (simplify imax, max)
- [x] Local context for typing under binders
- [x] Proof irrelevance (proofs of Prop are definitionally equal)
- [x] Declaration validation (axioms, definitions, theorems)

## Coverage

Type checking coverage on Lean 4 export files:

| Export File | Declarations | Passed | Failed | Coverage |
|-------------|--------------|--------|--------|----------|
| Init.Prelude | 2036 | 1788 | 248 | 87.8% |
| Init.Core | 3748 | 3353 | 395 | 89.5% |
| Init.Classical | 8044 | 6577 | 1467 | 81.8% |
| Init.Data.Nat.Basic | 4586 | 4050 | 536 | 88.3% |

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
