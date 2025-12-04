# lean4idris

A Lean 4 type checker written in Idris 2, targeting the [lean4export](https://github.com/leanprover/lean4export) format.

## Status

**Milestone 6 complete**: Proof irrelevance.

- [x] Parser for names, levels, expressions, declarations
- [x] Well-scoped expressions (indexed by depth)
- [x] Type inference (`inferType`) for closed terms
- [x] Type inference (`inferTypeOpen`) for open terms with local context
- [x] Reduction (`whnf`) - beta, let, delta, iota, and projection reduction
- [x] Definitional equality (`isDefEq`) - structural + beta + delta + eta
- [x] Delta reduction with reducibility hints (abbrev unfolds, opaque doesn't)
- [x] Eta expansion (λx. f x = f)
- [x] Iota reduction (recursor computation when major premise is a constructor)
- [x] Projection reduction (struct.field when struct is a constructor)
- [x] Universe level normalization (simplify imax, max)
- [x] Local context for typing under binders
- [x] Proof irrelevance (proofs of Prop are definitionally equal)
- [ ] Quotient type reduction
- [ ] Declaration validation

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
