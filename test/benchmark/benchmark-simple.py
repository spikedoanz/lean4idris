#!/usr/bin/env python3
"""
Simple benchmark for lean4idris type checker.
Measures parse time and type-check time on export files.
"""

import subprocess
import time
import sys
from pathlib import Path
import statistics

PROJECT_ROOT = Path(__file__).parent.parent.parent
LEAN4IDRIS = PROJECT_ROOT / "test" / "benchmark" / "build" / "exec" / "lean4idris-bench"
EXAMPLES_DIR = PROJECT_ROOT / "lean4export" / "examples"
REDTEAM_DIR = PROJECT_ROOT / "test" / "redteam" / "soundness"


def run_benchmark(export_path: Path, runs: int = 5) -> dict:
    """Run benchmark on a single file."""
    times = []
    status = "OK"
    output = ""

    for _ in range(runs):
        start = time.perf_counter()
        result = subprocess.run(
            [str(LEAN4IDRIS), str(export_path)],
            capture_output=True, text=True, timeout=60
        )
        elapsed = time.perf_counter() - start
        output = result.stdout + result.stderr

        if result.returncode != 0 or "ERROR" in output:
            if "TYPECHECK_ERROR" in output:
                status = "TYPECHECK_ERROR"
            elif "PARSE_ERROR" in output:
                status = "PARSE_ERROR"
            else:
                status = "ERROR"
            break
        times.append(elapsed * 1000)  # ms

    return {
        "file": export_path.name,
        "size_kb": export_path.stat().st_size / 1024,
        "status": status,
        "median_ms": statistics.median(times) if times else None,
        "min_ms": min(times) if times else None,
        "max_ms": max(times) if times else None,
        "output": output.strip().split("\n")[-1] if output else "",
    }


def main():
    if not LEAN4IDRIS.exists():
        print(f"ERROR: lean4idris-bench not found at {LEAN4IDRIS}")
        print("Build with: cd test/benchmark && pack build bench.ipkg")
        sys.exit(1)

    print("=" * 70)
    print("  lean4idris Type Checker Benchmark")
    print("=" * 70)
    print()

    # Find export files that are expected to PASS (from redteam tests)
    valid_tests = {"11-bvar-escape-lambda.export", "29-app-defequal-not-structural.export",
                   "30-whnf-deep-beta.export", "46-level-param-cyclic.export"}

    exports = []
    if EXAMPLES_DIR.exists():
        exports.extend(EXAMPLES_DIR.glob("*.export"))
    if REDTEAM_DIR.exists():
        for f in REDTEAM_DIR.glob("*.export"):
            if f.name in valid_tests:
                exports.append(f)

    exports = sorted(set(exports), key=lambda p: p.stat().st_size)

    print(f"Found {len(exports)} export files (valid tests only)")
    print()
    print(f"{'File':<50} {'Size':>8} {'Status':<12} {'Time':>10}")
    print("-" * 85)

    results = []
    for export in exports:
        result = run_benchmark(export)
        results.append(result)

        time_str = f"{result['median_ms']:.1f}ms" if result['median_ms'] else "N/A"
        print(f"{result['file']:<50} {result['size_kb']:>7.1f}K {result['status']:<12} {time_str:>10}")

    print("-" * 85)
    print()

    # Summary
    successful = [r for r in results if r['status'] == 'OK']
    if successful:
        total_size = sum(r['size_kb'] for r in successful)
        total_time = sum(r['median_ms'] for r in successful)
        avg_time = statistics.mean(r['median_ms'] for r in successful)
        print(f"Successful: {len(successful)}/{len(results)}")
        print(f"Total size: {total_size:.1f} KB")
        print(f"Total time: {total_time:.1f} ms")
        if total_time > 0:
            print(f"Throughput: {total_size / (total_time / 1000):.1f} KB/s")
        print(f"Avg time per file: {avg_time:.1f} ms")
    else:
        print("No successful benchmarks.")

    # Show errors
    errors = [r for r in results if r['status'] != 'OK']
    if errors:
        print()
        print("Errors:")
        for r in errors[:5]:
            print(f"  {r['file']}: {r['output']}")


if __name__ == "__main__":
    main()
