#!/usr/bin/env python3
import subprocess, json, re, sys, os
from pathlib import Path

EXPORTS_DIR = Path(os.path.expanduser('~/.cache/lean4exports'))
# Only check Init.Prelude for now (fast CI, still has bugs to fix)
CI_FILES = ['Init.Prelude.export']

def load_status(path):
    status = {}
    with open(path) as f:
        next(f)  # skip header
        for line in f:
            if line.strip():
                r = json.loads(line)
                status[r['decl']] = r['status']
    return status

def run_checker(export_file, fuel):
    result = subprocess.run(
        ['pack', 'run', 'lean4idris', '--no-cache', '-f', str(fuel), str(export_file)],
        capture_output=True, text=True
    )
    status = {}
    for line in (result.stdout + result.stderr).split('\n'):
        m = re.match(r'Checking: (.+)\.\.\. (ok|FAIL|TIMEOUT)', line)
        if m:
            status[m.group(1)] = m.group(2).lower()
    return status

def main():
    fuel = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    regressions = []

    for status_file in sorted(EXPORTS_DIR.rglob('*.status.jsonl')):
        export_file = Path(str(status_file).replace('.status.jsonl', ''))
        if not export_file.exists():
            continue
        if export_file.name not in CI_FILES:
            continue

        baseline = load_status(status_file)
        current = run_checker(export_file, fuel)

        for decl, old_status in baseline.items():
            new_status = current.get(decl, 'missing')
            if old_status == 'ok' and new_status != 'ok':
                regressions.append((export_file.name, decl, old_status, new_status))

    if regressions:
        print(f"REGRESSIONS: {len(regressions)}")
        for file, decl, old, new in regressions[:50]:
            print(f"  {file}:{decl} {old}->{new}")
        sys.exit(1)

    print("No regressions")

if __name__ == '__main__':
    main()
