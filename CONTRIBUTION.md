# Contributing to lean4idris

## Before Committing

- [ ] Run `pack test lean4idris` to ensure basic tests pass

## Regression Testing

This project includes infrastructure for testing changes against the Lean 4 Init library exports.

### Prerequisites

Ensure you have the Lean 4 export files cached:
```bash
ls ~/.cache/lean4exports/tier01-init/*.export
```

### Running Tests

1. **Build the project:**
   ```bash
   pack build
   ```

2. **Run the test suite:**
   ```bash
   ./tools/manual.sh | bash 2>&1 | tee /tmp/test_run.log
   ```

   This runs the type checker on all Init library exports with:
   - 100,000 fuel limit per declaration
   - Timing information captured via `time`
   - Output logged to `/tmp/<filename>.log`

3. **Create a log directory for this commit:**
   ```bash
   COMMIT=$(git rev-parse HEAD)
   mkdir -p logs/$COMMIT
   cp /tmp/*.export.log logs/$COMMIT/
   ```

### Important: Preserving Log History

**Never modify, move, or delete existing log directories.** Each log directory is a historical record tied to a specific commit hash. These logs enable comparing performance across different versions of the code.

- Do NOT rename existing log directories
- Do NOT move logs from one commit directory to another
- Do NOT delete old log directories
- Only ADD new log directories for new commits

### Analyzing Results

1. **Get statistics for a commit:**
   ```bash
   ./logs/get_stats.sh logs/<commit-hash>
   ```

   This shows:
   - Total unique declarations checked
   - OK / FAIL / TIMEOUT counts
   - Overall OK percentage
   - Any declarations that hung (didn't complete)

2. **Find recent commits with logs:**
   ```bash
   ./logs/sort_by_commit.sh
   ```

   Lists commit hashes (most recent first) that have corresponding log directories.

### Comparing Commits

To compare your changes against a baseline:

1. **Identify the baseline commit:**
   ```bash
   ./logs/sort_by_commit.sh | head -5
   ```

2. **Run stats on both:**
   ```bash
   ./logs/get_stats.sh logs/<baseline-hash>
   ./logs/get_stats.sh logs/<your-commit-hash>
   ```

3. **Compare key metrics:**
   - OK count should not decrease significantly
   - TIMEOUT count should not increase significantly
   - OK% should remain stable or improve

### Timing Comparison

The test output includes timing information for each file. To extract timing:

```bash
grep -E "^real|^Getting declarations" /tmp/test_run.log
```

This shows wall-clock time for each export file, useful for detecting performance regressions.

### Example Workflow

```bash
# Create a feature branch
git checkout -b feature/my-change

# Make your changes...

# Build and test
pack build
./tools/manual.sh | bash 2>&1 | tee /tmp/test_run.log

# Save results
COMMIT=$(git rev-parse HEAD)
mkdir -p logs/$COMMIT
cp /tmp/*.export.log logs/$COMMIT/

# Compare with baseline (e.g., main branch)
git checkout main
pack build
./tools/manual.sh | bash 2>&1 | tee /tmp/baseline_run.log
BASELINE=$(git rev-parse HEAD)
mkdir -p logs/$BASELINE
cp /tmp/*.export.log logs/$BASELINE/

# Analyze
./logs/get_stats.sh logs/$BASELINE
./logs/get_stats.sh logs/$COMMIT
```

### Using Git Worktrees for Parallel Testing

For faster A/B comparison, use git worktrees to test branches in parallel:

```bash
# Create a worktree for the feature branch
git worktree add ../lean4idris-feature feature/my-change

# Run tests in parallel
cd /path/to/lean4idris && pack build && ./tools/manual.sh | bash 2>&1 | tee /tmp/baseline.log &
cd /path/to/lean4idris-feature && pack build && ./tools/manual.sh | bash 2>&1 | tee /tmp/feature.log &
wait

# Compare results
```
