#!/usr/bin/env python3
"""
Generate theorem status JSON for regression tracking.

Runs lean4idris on all export files and produces a JSON report.
"""

import subprocess
import json
import sys
import os
import time
import re
from pathlib import Path
from datetime import datetime

# Default fuel limit for CI
DEFAULT_FUEL = 10000

def run_checker(export_file: Path, fuel: int) -> dict:
    """Run lean4idris on an export file and parse results."""
    start = time.time()

    cmd = [
        "pack", "run", "lean4idris",
        "--no-cache",
        "-f", str(fuel),
        str(export_file)
    ]

    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        cwd=Path(__file__).parent.parent
    )

    elapsed = time.time() - start
    stdout = result.stdout + result.stderr

    # Parse declaration results from stdout
    declarations = {}
    for line in stdout.split('\n'):
        # Match "Checking: <name>... <status>"
        match = re.match(r'Checking: (.+)\.\.\. (ok|FAIL|TIMEOUT|\[cached\] ok)', line)
        if match:
            name, status = match.groups()
            # Normalize cached to ok
            if status == '[cached] ok':
                status = 'ok'
            declarations[name] = status

    # Parse summary line: "TOTAL n OK n FAIL n TIMEOUT n CACHED n OK% pct"
    summary = {"total": 0, "ok": 0, "fail": 0, "timeout": 0, "cached": 0, "ok_pct": 0.0}
    for line in stdout.split('\n'):
        if line.startswith('TOTAL '):
            parts = line.split()
            for i, key in enumerate(['total', 'ok', 'fail', 'timeout', 'cached']):
                try:
                    idx = parts.index(key.upper()) + 1
                    summary[key] = int(parts[idx])
                except (ValueError, IndexError):
                    pass
            try:
                idx = parts.index('OK%') + 1
                summary['ok_pct'] = float(parts[idx])
            except (ValueError, IndexError):
                pass

    return {
        "time_seconds": round(elapsed, 2),
        "summary": summary,
        "declarations": declarations
    }


def main():
    import argparse
    parser = argparse.ArgumentParser(description='Generate theorem status JSON')
    parser.add_argument('--fuel', type=int, default=DEFAULT_FUEL, help='Fuel limit')
    parser.add_argument('--tier', type=str, help='Only run specific tier (e.g., tier01-init)')
    parser.add_argument('--output', type=str, default='status.json', help='Output file')
    parser.add_argument('--compact', action='store_true', help='Only store failures, not all declarations')
    args = parser.parse_args()

    repo_root = Path(__file__).parent.parent
    exports_dir = repo_root / 'test' / 'exports'

    # Find all tiers
    tiers = sorted([d for d in exports_dir.iterdir() if d.is_dir()])
    if args.tier:
        tiers = [t for t in tiers if t.name == args.tier]
        if not tiers:
            print(f"Tier not found: {args.tier}", file=sys.stderr)
            sys.exit(1)

    status = {
        "version": "1.0",
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "fuel": args.fuel,
        "tiers": {}
    }

    total_start = time.time()

    for tier_dir in tiers:
        tier_name = tier_dir.name
        print(f"\n=== {tier_name} ===", file=sys.stderr)

        tier_status = {
            "files": {},
            "summary": {"total": 0, "ok": 0, "fail": 0, "timeout": 0}
        }

        export_files = sorted(tier_dir.glob('*.export'))
        for export_file in export_files:
            file_name = export_file.name
            print(f"  {file_name}...", end='', file=sys.stderr, flush=True)

            result = run_checker(export_file, args.fuel)

            # Aggregate summary
            for key in ['total', 'ok', 'fail', 'timeout']:
                tier_status['summary'][key] += result['summary'][key]

            # Store file result
            if args.compact:
                # Only store failures
                failures = {k: v for k, v in result['declarations'].items() if v != 'ok'}
                tier_status['files'][file_name] = {
                    "time_seconds": result['time_seconds'],
                    "summary": result['summary'],
                    "failures": failures
                }
            else:
                tier_status['files'][file_name] = result

            print(f" {result['summary']['ok']}/{result['summary']['total']} ok ({result['time_seconds']}s)", file=sys.stderr)

        status['tiers'][tier_name] = tier_status

    status['total_time_seconds'] = round(time.time() - total_start, 2)

    # Write output
    output_path = repo_root / args.output
    with open(output_path, 'w') as f:
        json.dump(status, f, indent=2)

    print(f"\nStatus written to {output_path}", file=sys.stderr)

    # Print summary
    print("\n=== Summary ===", file=sys.stderr)
    for tier_name, tier_data in status['tiers'].items():
        s = tier_data['summary']
        pct = (s['ok'] / s['total'] * 100) if s['total'] > 0 else 0
        print(f"  {tier_name}: {s['ok']}/{s['total']} ({pct:.1f}%)", file=sys.stderr)


if __name__ == '__main__':
    main()
