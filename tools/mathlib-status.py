#!/usr/bin/env python3
"""
Mathlib Typecheck Status Tracker

Runs the lean4idris typechecker against all exported Mathlib modules
and tracks pass/fail status with timing information.

Usage:
    ./tools/mathlib-status.py              # Run all exports
    ./tools/mathlib-status.py --tier 1     # Run specific tier
    ./tools/mathlib-status.py --report     # Show status report only
    ./tools/mathlib-status.py --json       # Output JSON results
    ./tools/mathlib-status.py --csv        # Output CSV results
"""

import argparse
import csv
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, asdict, fields
from datetime import datetime
from pathlib import Path
from typing import Optional

# Throttling: delay between tests to avoid CPU overload
DEFAULT_THROTTLE_DELAY = 1.0  # seconds between tests


@dataclass
class TestResult:
    """Result of typechecking a single export file."""
    module: str
    tier: int
    status: str  # "pass", "fail", "timeout", "error", "pending"
    duration_secs: float
    error_message: Optional[str] = None
    file_size_mb: float = 0.0
    declaration_count: int = 0
    timestamp: str = ""
    conjecture: str = ""  # Hypothesized reason for failure


@dataclass
class StatusReport:
    """Overall status report for all modules."""
    total: int
    passed: int
    failed: int
    timeout: int
    error: int
    pending: int
    last_run: str
    results: list


TIER_DIRS = {
    1: "tier1-core",
    2: "tier2-simple-mathlib",
    3: "tier3-algebraic",
    4: "tier4-analysis",
    5: "tier5-category",
    6: "tier6-adversarial",
}

TIER_NAMES = {
    1: "Core Library (Init.*)",
    2: "Simple Mathlib (Data/Logic)",
    3: "Algebraic Structures",
    4: "Analysis/Topology",
    5: "Category Theory",
    6: "Adversarial (mutual/nested/quotients)",
}


def get_repo_root() -> Path:
    """Find repository root (contains lean4idris.ipkg)."""
    current = Path(__file__).resolve().parent.parent
    if (current / "lean4idris.ipkg").exists():
        return current
    raise RuntimeError("Cannot find repository root")


def get_export_dir(tier: int, repo_root: Path) -> Path:
    """Get export directory for a tier."""
    return repo_root / "test" / "exports" / TIER_DIRS[tier]


def find_exports(tier: int, repo_root: Path) -> list[Path]:
    """Find all .export files for a tier."""
    export_dir = get_export_dir(tier, repo_root)
    if not export_dir.exists():
        return []
    return sorted(export_dir.glob("*.export"))


def get_checker_path(repo_root: Path) -> Path:
    """Get path to the typechecker executable."""
    # Main lean4idris CLI
    checker = repo_root / "build" / "exec" / "lean4idris"
    if checker.exists():
        return checker
    raise RuntimeError(
        "Type checker not found. Build with:\n"
        "  pack build lean4idris.ipkg"
    )


def run_typecheck(
    export_path: Path,
    checker_path: Path,
    timeout_secs: int = 300,
    nice_level: int = 10
) -> TestResult:
    """Run typechecker on an export file."""
    module_name = export_path.stem
    tier = get_tier_from_path(export_path)

    file_size_mb = export_path.stat().st_size / (1024 * 1024)

    timestamp = datetime.now().isoformat()
    start_time = time.time()

    try:
        # Use nice to reduce process priority and avoid system overload
        cmd = ["nice", f"-n{nice_level}", str(checker_path), str(export_path)]
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout_secs,
            cwd=export_path.parent.parent.parent.parent,  # repo root
        )
        duration = time.time() - start_time

        # Parse output for declaration count if available
        decl_count = 0
        for line in result.stdout.split("\n"):
            if "declarations" in line.lower():
                try:
                    decl_count = int("".join(c for c in line if c.isdigit()))
                except ValueError:
                    pass

        if result.returncode == 0:
            # Check for actual success in output
            if "ACCEPTED" in result.stdout or "Successfully" in result.stdout:
                status = "pass"
                error_msg = None
            elif "TYPECHECK_ERROR" in result.stdout or "FAILED" in result.stdout:
                status = "fail"
                # Extract error message
                error_msg = extract_error(result.stdout)
            else:
                # Assume pass if no error indicators
                status = "pass"
                error_msg = None
        else:
            status = "fail"
            error_msg = extract_error(result.stdout + result.stderr)

        conj = conjecture_failure(error_msg, module_name) if status != "pass" else ""
        return TestResult(
            module=module_name,
            tier=tier,
            status=status,
            duration_secs=round(duration, 2),
            error_message=error_msg,
            file_size_mb=round(file_size_mb, 2),
            declaration_count=decl_count,
            timestamp=timestamp,
            conjecture=conj,
        )

    except subprocess.TimeoutExpired:
        duration = time.time() - start_time
        return TestResult(
            module=module_name,
            tier=tier,
            status="timeout",
            duration_secs=round(duration, 2),
            error_message=f"Timeout after {timeout_secs}s",
            file_size_mb=round(file_size_mb, 2),
            timestamp=timestamp,
            conjecture="PERF: Computation timeout (fuel exhaustion)",
        )
    except Exception as e:
        duration = time.time() - start_time
        return TestResult(
            module=module_name,
            tier=tier,
            status="error",
            duration_secs=round(duration, 2),
            error_message=str(e),
            file_size_mb=round(file_size_mb, 2),
            timestamp=timestamp,
            conjecture="ERROR: Runtime exception",
        )


def extract_error(output: str) -> str:
    """Extract first meaningful error message from output."""
    for line in output.split("\n"):
        line = line.strip()
        if any(kw in line for kw in ["Error", "FAILED", "error:", "TYPECHECK_ERROR"]):
            # Truncate long error messages
            return line[:200] + ("..." if len(line) > 200 else "")
    return output[:200] + ("..." if len(output) > 200 else "")


def conjecture_failure(error_msg: Optional[str], module: str) -> str:
    """Generate a conjecture about why a test failed based on error patterns."""
    if not error_msg:
        return ""

    err = error_msg.lower()

    # Parse errors - lexer/parser issues
    if "parse error" in err or "lexer error" in err:
        if "unexpected '#[" in err:
            return "LEXER: New attribute syntax not supported"
        if "unexpected token: ." in err:
            return "PARSER: Dot notation or namespace syntax issue"
        return "PARSER: Export format incompatibility"

    # Universe level issues
    if "cyclic universe" in err:
        return "UNIVERSE: Cyclic level parameter detection"
    if "universe" in err and "level" in err:
        return "UNIVERSE: Level constraint issue"
    if "outparam" in err.lower():
        return "UNIVERSE: outParam handling"

    # Projection issues
    if "projection" in err:
        return "PROJECTION: Projection typing not fully implemented"

    # Recursor issues
    if "recursor" in err or "rec" in err:
        return "RECURSOR: Recursor typing/validation issue"

    # Inductive issues
    if "inductive" in err:
        return "INDUCTIVE: Inductive type validation"

    # DefEq issues
    if "defeq" in err or "def eq" in err or "definitional" in err:
        return "DEFEQ: Definitional equality check failed"

    # Type mismatch
    if "type mismatch" in err or "expected" in err:
        return "TYPE: Type mismatch in checking"

    # Timeout
    if "timeout" in err:
        return "PERF: Computation timeout (fuel exhaustion)"

    # File issues
    if "file" in err and ("read" in err or "not found" in err):
        return "IO: File reading issue"

    # Quotient types
    if "quot" in err:
        return "QUOT: Quotient type handling"

    # Let bindings
    if "let" in err:
        return "LET: Let binding issue"

    # Unknown
    return "UNKNOWN: Unclassified error"


def get_tier_from_path(path: Path) -> int:
    """Extract tier number from export path."""
    for tier, dirname in TIER_DIRS.items():
        if dirname in str(path):
            return tier
    return 0


def load_previous_results(status_file: Path) -> dict[str, TestResult]:
    """Load previous results from status file."""
    if not status_file.exists():
        return {}

    try:
        with open(status_file) as f:
            data = json.load(f)
        return {
            r["module"]: TestResult(**r)
            for r in data.get("results", [])
        }
    except (json.JSONDecodeError, KeyError):
        return {}


def save_results(status_file: Path, results: list[TestResult]):
    """Save results to status file."""
    passed = sum(1 for r in results if r.status == "pass")
    failed = sum(1 for r in results if r.status == "fail")
    timeout = sum(1 for r in results if r.status == "timeout")
    error = sum(1 for r in results if r.status == "error")
    pending = sum(1 for r in results if r.status == "pending")

    report = StatusReport(
        total=len(results),
        passed=passed,
        failed=failed,
        timeout=timeout,
        error=error,
        pending=pending,
        last_run=datetime.now().isoformat(),
        results=[asdict(r) for r in results],
    )

    with open(status_file, "w") as f:
        json.dump(asdict(report), f, indent=2)


def print_report(results: list[TestResult], verbose: bool = False):
    """Print status report to console."""
    print("=" * 60)
    print("  Mathlib Typecheck Status Report")
    print("=" * 60)
    print()

    # Group by tier
    by_tier: dict[int, list[TestResult]] = {}
    for r in results:
        by_tier.setdefault(r.tier, []).append(r)

    for tier in sorted(by_tier.keys()):
        tier_results = by_tier[tier]
        passed = sum(1 for r in tier_results if r.status == "pass")
        failed = sum(1 for r in tier_results if r.status == "fail")
        other = len(tier_results) - passed - failed

        tier_name = TIER_NAMES.get(tier, f"Tier {tier}")
        print(f"## Tier {tier}: {tier_name}")
        print(f"   Pass: {passed}/{len(tier_results)}", end="")
        if failed > 0:
            print(f" | Fail: {failed}", end="")
        if other > 0:
            print(f" | Other: {other}", end="")
        print()

        if verbose:
            for r in tier_results:
                status_icon = {
                    "pass": "[PASS]",
                    "fail": "[FAIL]",
                    "timeout": "[TIME]",
                    "error": "[ERR ]",
                    "pending": "[PEND]",
                }.get(r.status, "[????]")

                print(f"   {status_icon} {r.module} ({r.file_size_mb}MB, {r.duration_secs}s)")
                if r.error_message and r.status != "pass":
                    print(f"          {r.error_message[:80]}")
        print()

    # Summary
    total = len(results)
    passed = sum(1 for r in results if r.status == "pass")
    failed = sum(1 for r in results if r.status == "fail")

    print("=" * 60)
    print("  Summary")
    print("=" * 60)
    print(f"Total:   {total}")
    print(f"Passed:  {passed} ({100*passed/total:.1f}%)" if total > 0 else "Passed:  0")
    print(f"Failed:  {failed}")
    print()


def print_json_report(results: list[TestResult]):
    """Print JSON status report."""
    passed = sum(1 for r in results if r.status == "pass")
    failed = sum(1 for r in results if r.status == "fail")
    timeout = sum(1 for r in results if r.status == "timeout")
    error = sum(1 for r in results if r.status == "error")
    pending = sum(1 for r in results if r.status == "pending")

    report = {
        "total": len(results),
        "passed": passed,
        "failed": failed,
        "timeout": timeout,
        "error": error,
        "pending": pending,
        "last_run": datetime.now().isoformat(),
        "results": [asdict(r) for r in results],
    }
    print(json.dumps(report, indent=2))


def save_csv_report(results: list[TestResult], csv_path: Path):
    """Save results to CSV file."""
    fieldnames = [f.name for f in fields(TestResult)]

    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for r in results:
            writer.writerow(asdict(r))

    print(f"CSV saved to: {csv_path}")


def init_csv(csv_path: Path):
    """Initialize CSV file with headers."""
    fieldnames = [f.name for f in fields(TestResult)]
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()


def append_csv(result: TestResult, csv_path: Path):
    """Append a single result to CSV file."""
    fieldnames = [f.name for f in fields(TestResult)]
    with open(csv_path, "a", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writerow(asdict(result))


def main():
    parser = argparse.ArgumentParser(description="Mathlib Typecheck Status Tracker")
    parser.add_argument("--tier", type=int, choices=[1, 2, 3, 4, 5, 6],
                        help="Run specific tier only")
    parser.add_argument("--report", action="store_true",
                        help="Show status report from previous run (don't run tests)")
    parser.add_argument("--json", action="store_true",
                        help="Output results as JSON")
    parser.add_argument("--csv", action="store_true",
                        help="Save results to CSV file")
    parser.add_argument("--verbose", "-v", action="store_true",
                        help="Show detailed per-module results")
    parser.add_argument("--timeout", type=int, default=300,
                        help="Timeout per module in seconds (default: 300)")
    parser.add_argument("--module", type=str,
                        help="Run only specific module (partial match)")
    parser.add_argument("--throttle", type=float, default=DEFAULT_THROTTLE_DELAY,
                        help=f"Delay between tests in seconds (default: {DEFAULT_THROTTLE_DELAY})")
    parser.add_argument("--nice", type=int, default=10,
                        help="Nice priority for subprocess (default: 10, range: 0-19)")
    args = parser.parse_args()

    repo_root = get_repo_root()
    status_file = repo_root / "test" / "exports" / "mathlib-status.json"
    csv_file = repo_root / "test" / "exports" / "mathlib-status.csv"

    # Report-only mode
    if args.report:
        prev_results = load_previous_results(status_file)
        if not prev_results:
            print("No previous results found. Run tests first.")
            sys.exit(1)
        results = list(prev_results.values())
        if args.json:
            print_json_report(results)
        else:
            print_report(results, args.verbose)
        return

    # Find all exports
    exports: list[Path] = []
    tiers = [args.tier] if args.tier else [1, 2, 3, 4, 5, 6]

    for tier in tiers:
        tier_exports = find_exports(tier, repo_root)
        if args.module:
            tier_exports = [e for e in tier_exports if args.module.lower() in e.stem.lower()]
        exports.extend(tier_exports)

    if not exports:
        print("No export files found. Run:")
        print("  ./tools/export-mathlib.sh all")
        sys.exit(1)

    # Get checker
    try:
        checker = get_checker_path(repo_root)
    except RuntimeError as e:
        print(f"Error: {e}")
        sys.exit(1)

    print(f"Found {len(exports)} export file(s)")
    print(f"Using checker: {checker}")
    print()

    # Load previous results to preserve status for modules not being tested
    prev_results = load_previous_results(status_file)

    # Initialize CSV for incremental writes
    csv_incremental = repo_root / "test" / "exports" / "mathlib-status-incremental.csv"
    init_csv(csv_incremental)

    # Run tests
    results: list[TestResult] = []
    for i, export_path in enumerate(exports, 1):
        module_name = export_path.stem
        print(f"[{i}/{len(exports)}] Testing {module_name}...", end=" ", flush=True)

        result = run_typecheck(export_path, checker, args.timeout)
        results.append(result)

        # Write incrementally so we don't lose progress
        append_csv(result, csv_incremental)

        status_str = {
            "pass": "PASS",
            "fail": "FAIL",
            "timeout": "TIMEOUT",
            "error": "ERROR",
        }.get(result.status, result.status.upper())

        print(f"{status_str} ({result.duration_secs}s)")

        if result.error_message and result.status != "pass":
            print(f"    Error: {result.error_message[:80]}")

    # Merge with previous results for modules not tested
    all_modules = set(r.module for r in results)
    for module, prev_result in prev_results.items():
        if module not in all_modules:
            results.append(prev_result)

    # Sort by tier then module name
    results.sort(key=lambda r: (r.tier, r.module))

    # Save and report
    save_results(status_file, results)

    # Always save CSV for easy reference
    save_csv_report(results, csv_file)

    print()
    if args.json:
        print_json_report(results)
    else:
        print_report(results, args.verbose)


if __name__ == "__main__":
    main()
