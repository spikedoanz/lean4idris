# lean4idris

A Lean 4 type checker written in Idris 2, targeting the [lean4export](https://github.com/leanprover/lean4export) format.

## Goals

### Primary: Soundness
- [ ] Prove that if lean4idris accepts a declaration, Lean 4 kernel also accepts it
- [ ] No false positives (accepting invalid proofs)

### Secondary: Completeness
- [ ] Match lean4lean's acceptance rate on standard library exports
- [ ] Track coverage across tiers (see below)

### Non-goals (for now)
- Performance optimization
- Full Lean 4 toolchain compatibility
- IDE integration

## Status

### Implemented Features
- [x] Parser for names, levels, expressions, declarations
- [x] Well-scoped expressions (indexed by depth)
- [x] Type inference (`inferType`) for closed terms
- [x] Type inference (`inferTypeOpen`) for open terms with local context
- [x] Reduction (`whnf`) - beta, let, delta, iota, projection, quotient
- [x] Definitional equality (`isDefEq`) - structural + beta + delta + eta
- [x] Delta reduction with reducibility hints
- [x] Eta expansion (λx. f x = f)
- [x] Iota reduction (recursor computation)
- [x] Projection reduction (struct.field)
- [x] Quotient reduction (Quot.lift/ind)
- [x] Universe level normalization
- [x] Local context for typing under binders
- [x] Proof irrelevance (proofs of Prop are definitionally equal)
- [x] Declaration validation (axioms, definitions, theorems)
- [x] Fuel-based timeout (per declaration)

### Known Limitations
- Some complex recursive definitions timeout
- Not all edge cases in universe polymorphism handled
- See [GitHub Issues](https://github.com/spikedoanz/lean4idris/issues) for blockers

## Coverage

Tested on lean4idris commit `564756727e377e7fe640b0932dcd690e027cb72d`

### Tier 1: Init (Core Lean library)
| File | OK | Fail | Timeout | OK% |
|------|-----|------|---------|-----|
| Init.Prelude | 1891 | 145 | 0 | 92.8% |
| Init.Core | 3465 | 283 | 0 | 92.4% |
| Init.Classical | 6739 | 1305 | 0 | 83.8% |
| Init.PropLemmas | 6688 | 1297 | 0 | 83.8% |
| Init.Data.Nat.Basic | 4164 | 422 | 0 | 90.8% |
| Init.Data.Nat.Lemmas | 8555 | 2488 | 0 | 77.5% |
| Init.Data.Int.Basic | 4692 | 516 | 0 | 90.1% |
| Init.Data.List.Basic | 4897 | 765 | 0 | 86.5% |
| Init.Data.Array.Basic | 5930 | 1195 | 0 | 83.2% |
| Init.Data.Char.Basic | 4736 | 584 | 0 | 89.0% |
| Init.Data.Fin.Basic | 4661 | 548 | 0 | 89.5% |
| Init.Data.Option.Basic | 3851 | 337 | 0 | 91.9% |

### Tier 2-10: Not yet systematically tested
See `test/exports/` for available export files.

## Build

Requires [pack](https://github.com/stefan-hoeck/idris2-pack).

```bash
pack build lean4idris        # build
pack run lean4idris-test     # run tests
```

## Usage

### CLI

```bash
# Default: check all declarations, continue on errors
lean4idris file.export

# Stop on first error
lean4idris -e file.export

# Custom fuel limit per declaration (default: 100000)
lean4idris -f 1000000 file.export

# Verbose error output
lean4idris -v file.export
```

Output format (parsable):
```
TOTAL 2036 OK 1891 FAIL 145 TIMEOUT 0 OK% 92.8
```

### Library

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
  Main.idr          -- CLI entry point
  Export/
    Token.idr       -- Export format tokens
    Lexer.idr       -- Tokenizer
    Parser.idr      -- Parser
```

## References

- [lean4lean](https://github.com/digama0/lean4lean) - Lean kernel in Lean
- [nanoda_lib](https://github.com/ammkrn/nanoda_lib) - Lean type checker in Rust
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/) - Documentation
