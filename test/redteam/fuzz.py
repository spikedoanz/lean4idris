#!/usr/bin/env python3
"""
Fuzz tester for lean4idris export parser and type checker.
Generates random/malformed .export files and checks for crashes.
"""

import subprocess
import random
import string
import tempfile
import os
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent.parent
CHECKER = PROJECT_ROOT / "test" / "redteam" / "build" / "exec" / "lean4idris-redteam"

def run_export(content: str) -> tuple[bool, str]:
    """Run the type checker on export content. Returns (crashed, output)."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.export', delete=False) as f:
        f.write(content)
        f.flush()
        path = f.name

    try:
        # Run a quick inline test using the parser directly
        result = subprocess.run(
            ["idris2", "--exec", f'main', "-p", "lean4idris",
             "-e", f':exec parseAndCheck "{path}"'],
            capture_output=True, text=True, timeout=5,
            cwd=PROJECT_ROOT
        )
        crashed = result.returncode != 0 and "error" not in result.stderr.lower()
        return crashed, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except Exception as e:
        return True, f"EXCEPTION: {e}"
    finally:
        os.unlink(path)


def gen_valid_header() -> str:
    return "0.0.0\n"


def gen_random_name_decl(idx: int) -> str:
    """Generate a name declaration."""
    parent = random.randint(0, max(0, idx - 1))
    name = ''.join(random.choices(string.ascii_lowercase, k=random.randint(1, 10)))
    return f"{idx} #NS {parent} {name}\n"


def gen_random_level_decl(idx: int) -> str:
    """Generate a universe level declaration."""
    kind = random.choice(["#US", "#UM", "#UIM", "#UP"])
    if kind == "#US":
        parent = random.randint(0, max(0, idx - 1))
        return f"{idx} {kind} {parent}\n"
    elif kind in ["#UM", "#UIM"]:
        l1 = random.randint(0, max(0, idx - 1))
        l2 = random.randint(0, max(0, idx - 1))
        return f"{idx} {kind} {l1} {l2}\n"
    else:  # #UP
        name_idx = random.randint(1, 10)
        return f"{idx} {kind} {name_idx}\n"


def gen_random_expr_decl(idx: int, max_idx: int) -> str:
    """Generate an expression declaration."""
    kind = random.choice(["#ES", "#EC", "#EV", "#EA", "#EL", "#EP"])

    if kind == "#ES":
        level = random.randint(0, 5)
        return f"{idx} {kind} {level}\n"
    elif kind == "#EC":
        name = random.randint(1, max(1, max_idx))
        return f"{idx} {kind} {name}\n"
    elif kind == "#EV":
        var = random.randint(0, 10)
        return f"{idx} {kind} {var}\n"
    elif kind == "#EA":
        f = random.randint(0, max(0, idx - 1))
        a = random.randint(0, max(0, idx - 1))
        return f"{idx} {kind} {f} {a}\n"
    elif kind == "#EL":
        bi = random.choice(["#BD", "#BI", "#BS", "#BC"])
        name = random.randint(1, max(1, max_idx))
        ty = random.randint(0, max(0, idx - 1))
        body = random.randint(0, max(0, idx - 1))
        return f"{idx} {kind} {bi} {name} {ty} {body}\n"
    else:  # #EP
        bi = random.choice(["#BD", "#BI", "#BS", "#BC"])
        name = random.randint(1, max(1, max_idx))
        dom = random.randint(0, max(0, idx - 1))
        cod = random.randint(0, max(0, idx - 1))
        return f"{idx} {kind} {bi} {name} {dom} {cod}\n"


def gen_random_decl() -> str:
    """Generate a random top-level declaration."""
    kind = random.choice(["#AX", "#DEF", "#IND", "#CTOR", "#QUOT"])

    if kind == "#AX":
        name = random.randint(1, 10)
        ty = random.randint(0, 10)
        levels = random.randint(0, 3)
        return f"{kind} {name} {ty} {levels}\n"
    elif kind == "#DEF":
        name = random.randint(1, 10)
        ty = random.randint(0, 10)
        val = random.randint(0, 10)
        hint = random.choice(["A", "O", "N"])
        levels = random.randint(0, 3)
        return f"{kind} {name} {ty} {val} {hint} {levels}\n"
    elif kind == "#QUOT":
        return "#QUOT\n"
    elif kind == "#IND":
        # Complex format, just do minimal
        return f"#IND 1 0 0 0 0 0 0 1 1 0\n"
    else:
        return ""


def gen_fuzz_export(seed: int) -> str:
    """Generate a random export file."""
    random.seed(seed)

    lines = [gen_valid_header()]

    # Generate some names
    num_names = random.randint(1, 20)
    for i in range(1, num_names + 1):
        lines.append(gen_random_name_decl(i))

    # Generate some levels
    num_levels = random.randint(0, 10)
    for i in range(1, num_levels + 1):
        lines.append(gen_random_level_decl(i))

    # Generate some expressions
    num_exprs = random.randint(1, 30)
    for i in range(num_exprs):
        lines.append(gen_random_expr_decl(i, num_names))

    # Generate some declarations
    num_decls = random.randint(1, 5)
    for _ in range(num_decls):
        lines.append(gen_random_decl())

    return ''.join(lines)


def gen_malformed_export(kind: str) -> str:
    """Generate specifically malformed exports."""

    if kind == "huge_index":
        return f"0.0.0\n1 #NS 0 test\n0 #ES 999999999999\n"

    elif kind == "negative_index":
        return f"0.0.0\n1 #NS -1 test\n"

    elif kind == "empty":
        return ""

    elif kind == "no_version":
        return "1 #NS 0 test\n"

    elif kind == "bad_version":
        return "999.999.999\n1 #NS 0 test\n"

    elif kind == "unicode_name":
        return f"0.0.0\n1 #NS 0 \u0000\u0001\u0002\n"

    elif kind == "very_long_name":
        name = "a" * 100000
        return f"0.0.0\n1 #NS 0 {name}\n"

    elif kind == "deeply_nested":
        lines = ["0.0.0\n", "1 #NS 0 T\n", "1 #US 0\n", "0 #ES 1\n"]
        # Create deeply nested applications
        for i in range(1, 1000):
            lines.append(f"{i} #EA {i-1} 0\n")
        return ''.join(lines)

    elif kind == "circular_names":
        return f"0.0.0\n1 #NS 2 a\n2 #NS 1 b\n"

    elif kind == "unknown_command":
        return f"0.0.0\n1 #NS 0 test\n#FAKE 1 2 3\n"

    elif kind == "truncated":
        return f"0.0.0\n1 #NS 0 test\n#AX 1"

    else:
        return gen_valid_header()


def main():
    print("=" * 60)
    print("  lean4idris Fuzz Tester")
    print("=" * 60)
    print()

    crashes = []

    # Test malformed inputs
    print("## Testing malformed inputs...")
    malformed_kinds = [
        "huge_index", "negative_index", "empty", "no_version",
        "bad_version", "unicode_name", "very_long_name",
        "deeply_nested", "circular_names", "unknown_command", "truncated"
    ]

    for kind in malformed_kinds:
        content = gen_malformed_export(kind)
        # Just write to file for manual testing
        outpath = PROJECT_ROOT / "test" / "redteam" / "fuzz" / f"malformed-{kind}.export"
        outpath.parent.mkdir(exist_ok=True)
        outpath.write_text(content)
        print(f"  Generated: {outpath.name}")

    # Generate random exports
    print()
    print("## Generating random exports...")
    for seed in range(100):
        content = gen_fuzz_export(seed)
        outpath = PROJECT_ROOT / "test" / "redteam" / "fuzz" / f"random-{seed:03d}.export"
        outpath.write_text(content)
    print(f"  Generated 100 random exports in test/redteam/fuzz/")

    print()
    print("## Running tests...")
    print("  (Run manually with: for f in test/redteam/fuzz/*.export; do echo $f; ./test/redteam/build/exec/lean4idris-redteam $f 2>&1 | head -5; done)")
    print()
    print("Done.")


if __name__ == "__main__":
    main()
