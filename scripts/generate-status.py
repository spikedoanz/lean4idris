#!/usr/bin/env python3
import subprocess, json, re, sys, os
from pathlib import Path

EXPORTS_DIR = Path(os.path.expanduser('~/.cache/lean4exports'))
# Only check Init.Prelude for now (fast CI, still has bugs to fix)
CI_FILES = ['Init.Prelude.export']

def get_commit():
    return subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip()[:7]

def run_checker(export_file, fuel):
    result = subprocess.run(
        ['pack', 'run', 'lean4idris', '--no-cache', '-f', str(fuel), str(export_file)],
        capture_output=True, text=True
    )
    for line in (result.stdout + result.stderr).split('\n'):
        m = re.match(r'Checking: (.+)\.\.\. (ok|FAIL|TIMEOUT)', line)
        if m:
            yield m.group(1), m.group(2).lower()

def main():
    fuel = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    commit = get_commit()

    for tier in sorted(EXPORTS_DIR.iterdir()):
        if not tier.is_dir():
            continue
        for export in sorted(tier.glob('*.export')):
            if export.name not in CI_FILES:
                continue
            status_file = Path(str(export) + '.status.jsonl')
            with open(status_file, 'w') as f:
                f.write(json.dumps({"commit": commit, "fuel": fuel}) + '\n')
                for decl, status in run_checker(export, fuel):
                    f.write(json.dumps({"decl": decl, "status": status}) + '\n')
            print(f"{tier.name}/{export.name}")

if __name__ == '__main__':
    main()
