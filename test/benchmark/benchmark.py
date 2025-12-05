#!/usr/bin/env python3
"""
Benchmark script comparing lean4idris vs lean4lean type checker performance.

Usage:
    python3 test/benchmark/benchmark.py [--generate] [--runs N]
"""

import subprocess
import time
import os
import sys
import argparse
from pathlib import Path
from dataclasses import dataclass
from typing import Optional
import statistics

PROJECT_ROOT = Path(__file__).parent.parent.parent
LEAN4IDRIS_CHECKER = PROJECT_ROOT / "test" / "benchmark" / "build" / "exec" / "lean4idris-bench"
LEAN4LEAN_CHECKER = PROJECT_ROOT / "lean4lean" / ".lake" / "build" / "bin" / "lean4lean"
LEAN4EXPORT = PROJECT_ROOT / "lean4export" / ".lake" / "build" / "bin" / "lean4export"
BENCHMARK_DIR = PROJECT_ROOT / "test" / "benchmark" / "exports"


@dataclass
class BenchResult:
    name: str
    size_kb: float
    decls: int
    lean4idris_time: Optional[float]  # seconds
    lean4lean_time: Optional[float]   # seconds
    lean4idris_status: str
    lean4lean_status: str


def run_timed(cmd: list[str], timeout: int = 300) -> tuple[float, str, int]:
    """Run command and return (time_seconds, output, returncode)."""
    start = time.perf_counter()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=PROJECT_ROOT
        )
        elapsed = time.perf_counter() - start
        return elapsed, result.stdout + result.stderr, result.returncode
    except subprocess.TimeoutExpired:
        return timeout, "TIMEOUT", -1
    except Exception as e:
        return 0, f"ERROR: {e}", -1


def count_declarations(export_path: Path) -> int:
    """Count declarations in export file."""
    count = 0
    with open(export_path) as f:
        for line in f:
            if line.startswith(("#AX ", "#DEF ", "#THM ", "#IND ", "#CTOR ", "#REC ", "#QUOT")):
                count += 1
    return count


def benchmark_file(export_path: Path, runs: int = 3) -> BenchResult:
    """Benchmark a single export file."""
    name = export_path.stem
    size_kb = export_path.stat().st_size / 1024
    decls = count_declarations(export_path)

    print(f"  Benchmarking {name} ({size_kb:.1f} KB, {decls} decls)...")

    # Benchmark lean4idris
    lean4idris_times = []
    lean4idris_status = "OK"
    for i in range(runs):
        elapsed, output, rc = run_timed([str(LEAN4IDRIS_CHECKER), str(export_path)])
        if rc != 0:
            if "TIMEOUT" in output:
                lean4idris_status = "TIMEOUT"
            elif "error" in output.lower() or "Error" in output:
                lean4idris_status = "ERROR"
            else:
                lean4idris_status = f"FAIL({rc})"
            break
        lean4idris_times.append(elapsed)

    lean4idris_time = statistics.median(lean4idris_times) if lean4idris_times else None

    # Benchmark lean4lean
    lean4lean_times = []
    lean4lean_status = "OK"
    for i in range(runs):
        elapsed, output, rc = run_timed([str(LEAN4LEAN_CHECKER), str(export_path)])
        if rc != 0:
            if "TIMEOUT" in output:
                lean4lean_status = "TIMEOUT"
            elif "error" in output.lower() or "Error" in output:
                lean4lean_status = "ERROR"
            else:
                lean4lean_status = f"FAIL({rc})"
            break
        lean4lean_times.append(elapsed)

    lean4lean_time = statistics.median(lean4lean_times) if lean4lean_times else None

    return BenchResult(
        name=name,
        size_kb=size_kb,
        decls=decls,
        lean4idris_time=lean4idris_time,
        lean4lean_time=lean4lean_time,
        lean4idris_status=lean4idris_status,
        lean4lean_status=lean4lean_status,
    )


def generate_exports():
    """Generate export files for benchmarking."""
    BENCHMARK_DIR.mkdir(parents=True, exist_ok=True)

    # Small exports
    exports_to_generate = [
        ("Nat", ["Nat.add", "Nat.sub", "Nat.mul"]),
        ("List", ["List.map", "List.filter", "List.foldl"]),
        ("Bool", ["Bool.and", "Bool.or", "Bool.not"]),
    ]

    print("Generating benchmark exports...")
    for module, consts in exports_to_generate:
        out_path = BENCHMARK_DIR / f"{module}.export"
        if out_path.exists():
            print(f"  {out_path.name} already exists, skipping")
            continue

        print(f"  Generating {module}.export...")
        cmd = [str(LEAN4EXPORT), module, "--"] + consts
        result = subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT / "lean4export")
        if result.returncode == 0:
            out_path.write_text(result.stdout)
            print(f"    -> {out_path.stat().st_size / 1024:.1f} KB")
        else:
            print(f"    FAILED: {result.stderr}")

    # Copy existing example exports
    examples_dir = PROJECT_ROOT / "lean4export" / "examples"
    for export_file in examples_dir.glob("*.export"):
        dest = BENCHMARK_DIR / export_file.name
        if not dest.exists():
            dest.write_text(export_file.read_text())
            print(f"  Copied {export_file.name}")


def print_results(results: list[BenchResult]):
    """Print benchmark results as a table."""
    print()
    print("=" * 90)
    print("  BENCHMARK RESULTS")
    print("=" * 90)
    print()
    print(f"{'Export':<40} {'Size':>8} {'Decls':>6} {'lean4idris':>12} {'lean4lean':>12} {'Ratio':>8}")
    print("-" * 90)

    for r in sorted(results, key=lambda x: x.size_kb):
        idris_str = f"{r.lean4idris_time*1000:.1f}ms" if r.lean4idris_time else r.lean4idris_status
        lean_str = f"{r.lean4lean_time*1000:.1f}ms" if r.lean4lean_time else r.lean4lean_status

        if r.lean4idris_time and r.lean4lean_time:
            ratio = r.lean4idris_time / r.lean4lean_time
            ratio_str = f"{ratio:.2f}x"
        else:
            ratio_str = "N/A"

        print(f"{r.name:<40} {r.size_kb:>7.1f}K {r.decls:>6} {idris_str:>12} {lean_str:>12} {ratio_str:>8}")

    print("-" * 90)
    print()

    # Summary statistics
    valid_results = [r for r in results if r.lean4idris_time and r.lean4lean_time]
    if valid_results:
        avg_ratio = statistics.mean(r.lean4idris_time / r.lean4lean_time for r in valid_results)
        print(f"Average ratio (lean4idris / lean4lean): {avg_ratio:.2f}x")

        total_idris = sum(r.lean4idris_time for r in valid_results)
        total_lean = sum(r.lean4lean_time for r in valid_results)
        print(f"Total time - lean4idris: {total_idris*1000:.1f}ms, lean4lean: {total_lean*1000:.1f}ms")


def main():
    parser = argparse.ArgumentParser(description="Benchmark lean4idris vs lean4lean")
    parser.add_argument("--generate", action="store_true", help="Generate export files first")
    parser.add_argument("--runs", type=int, default=3, help="Number of runs per benchmark")
    args = parser.parse_args()

    # Check binaries exist
    if not LEAN4IDRIS_CHECKER.exists():
        print(f"ERROR: lean4idris benchmark binary not found at {LEAN4IDRIS_CHECKER}")
        print("Build with: cd test/benchmark && pack build bench.ipkg")
        sys.exit(1)

    if not LEAN4LEAN_CHECKER.exists():
        print(f"ERROR: lean4lean binary not found at {LEAN4LEAN_CHECKER}")
        print("Build with: cd lean4lean && lake build")
        sys.exit(1)

    if args.generate:
        generate_exports()

    # Find export files
    export_files = list(BENCHMARK_DIR.glob("*.export")) if BENCHMARK_DIR.exists() else []

    # Also check examples directory
    examples_dir = PROJECT_ROOT / "lean4export" / "examples"
    if examples_dir.exists():
        export_files.extend(examples_dir.glob("*.export"))

    if not export_files:
        print("No export files found. Run with --generate first.")
        sys.exit(1)

    print(f"Found {len(export_files)} export files")
    print(f"Running {args.runs} iterations per benchmark")
    print()

    results = []
    for export_path in sorted(set(export_files)):
        result = benchmark_file(export_path, runs=args.runs)
        results.append(result)

    print_results(results)


if __name__ == "__main__":
    main()
