# Contributing

## Before Submitting a PR

1. **Build**: `pack build lean4idris`
2. **Test**: `pack test`
3. **Regression check** (optional, requires exports):
   ```bash
   python3 scripts/check-regression.py
   ```

## Regression Testing

The regression system tracks which theorems pass/fail across commits.

### Setup

Export files live in `~/.cache/lean4exports/` organized by tier:
```
~/.cache/lean4exports/
  tier01-init/
    Init.Prelude.export
    Init.Prelude.export.status.jsonl
    Init.Core.export
    Init.Core.export.status.jsonl
    ...
```

### Generating a Baseline

```bash
python3 scripts/generate-status.py 10000
```

This creates `.status.jsonl` files next to each `.export` file.

### Status File Format

JSONL with header line containing commit and fuel:
```jsonl
{"commit":"abc123","fuel":10000}
{"decl":"CoeHTC","status":"ok"}
{"decl":"List.brecOn.go","status":"timeout"}
{"decl":"List.brecOn","status":"fail"}
```

### Checking for Regressions

```bash
python3 scripts/check-regression.py
```

A regression is when a declaration that was `ok` in the baseline is now `fail` or `timeout`.

Regressions are not allowed unless explicitly discussed.

## Updating the Baseline

If your PR improves theorem checking (more theorems pass), regenerate status files:
```bash
python3 scripts/generate-status.py 10000
```

Commit any `.status.jsonl` file changes if they show improvements.
