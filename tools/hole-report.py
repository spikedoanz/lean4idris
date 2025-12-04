#!/usr/bin/env python3
"""
Generate an HTML report of holes in Idris proof files.

Usage: python tools/hole-report.py [directory] [-o output.html]
"""

import re
import sys
from pathlib import Path
from dataclasses import dataclass
from collections import defaultdict

@dataclass
class Hole:
    name: str
    file: str
    line: int
    context: list[str]  # surrounding lines
    in_function: str | None = None

def find_holes(file_path: Path) -> list[Hole]:
    """Find all holes (?name) in an Idris file."""
    holes = []
    lines = file_path.read_text().splitlines()

    # Track current function/definition
    current_fn = None
    fn_pattern = re.compile(r'^(\w+)\s*:.*->|^(\w+)\s*:\s*\(|^(\w+)\s*=')

    for i, line in enumerate(lines):
        # Update current function
        fn_match = fn_pattern.match(line)
        if fn_match:
            current_fn = fn_match.group(1) or fn_match.group(2) or fn_match.group(3)

        # Find holes
        hole_pattern = re.compile(r'\?(\w+)')
        for match in hole_pattern.finditer(line):
            hole_name = match.group(1)

            # Get context (3 lines before and after)
            start = max(0, i - 3)
            end = min(len(lines), i + 4)
            context = [(j + 1, lines[j], j == i) for j in range(start, end)]

            holes.append(Hole(
                name=hole_name,
                file=str(file_path),
                line=i + 1,
                context=context,
                in_function=current_fn
            ))

    return holes

def generate_html(holes: list[Hole], base_dir: Path) -> str:
    """Generate HTML report."""

    # Group by file
    by_file = defaultdict(list)
    for hole in holes:
        rel_path = Path(hole.file).relative_to(base_dir)
        by_file[str(rel_path)].append(hole)

    # Group by category (inferred from hole name)
    categories = {
        'substitution': [],
        'weakening': [],
        'reduction': [],
        'typing': [],
        'conversion': [],
        'other': []
    }

    for hole in holes:
        name_lower = hole.name.lower()
        if 'subst' in name_lower:
            categories['substitution'].append(hole)
        elif 'weaken' in name_lower:
            categories['weakening'].append(hole)
        elif 'step' in name_lower or 'beta' in name_lower or 'det' in name_lower:
            categories['reduction'].append(hole)
        elif 'type' in name_lower or 'var' in name_lower:
            categories['typing'].append(hole)
        elif 'conv' in name_lower or 'eq' in name_lower:
            categories['conversion'].append(hole)
        else:
            categories['other'].append(hole)

    html = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Idris Proof Holes Report</title>
    <style>
        :root {
            --bg: #1a1a2e;
            --bg-light: #16213e;
            --bg-code: #0f0f1a;
            --text: #eee;
            --text-dim: #888;
            --accent: #e94560;
            --accent2: #0f3460;
            --green: #4ecca3;
            --yellow: #ffd369;
            --blue: #00adb5;
        }

        * { box-sizing: border-box; }

        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            background: var(--bg);
            color: var(--text);
            margin: 0;
            padding: 20px;
            line-height: 1.6;
        }

        .container {
            max-width: 1200px;
            margin: 0 auto;
        }

        h1 {
            color: var(--accent);
            border-bottom: 2px solid var(--accent);
            padding-bottom: 10px;
        }

        h2 {
            color: var(--blue);
            margin-top: 40px;
        }

        h3 {
            color: var(--green);
            margin-top: 30px;
        }

        .summary {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
            gap: 15px;
            margin: 20px 0;
        }

        .stat-card {
            background: var(--bg-light);
            padding: 20px;
            border-radius: 8px;
            text-align: center;
        }

        .stat-card .number {
            font-size: 2.5em;
            font-weight: bold;
            color: var(--accent);
        }

        .stat-card .label {
            color: var(--text-dim);
            font-size: 0.9em;
        }

        .stat-card.complete .number {
            color: var(--green);
        }

        .progress-bar {
            background: var(--bg-light);
            height: 30px;
            border-radius: 15px;
            overflow: hidden;
            margin: 20px 0;
        }

        .progress-fill {
            height: 100%;
            background: linear-gradient(90deg, var(--green), var(--blue));
            display: flex;
            align-items: center;
            justify-content: center;
            font-weight: bold;
            transition: width 0.5s;
        }

        .file-section {
            background: var(--bg-light);
            border-radius: 8px;
            margin: 20px 0;
            overflow: hidden;
        }

        .file-header {
            background: var(--accent2);
            padding: 15px 20px;
            font-family: monospace;
            display: flex;
            justify-content: space-between;
            align-items: center;
        }

        .file-header .count {
            background: var(--accent);
            padding: 2px 10px;
            border-radius: 10px;
            font-size: 0.9em;
        }

        .hole-card {
            border-top: 1px solid var(--bg);
            padding: 15px 20px;
        }

        .hole-name {
            font-family: monospace;
            font-size: 1.1em;
            color: var(--yellow);
        }

        .hole-meta {
            color: var(--text-dim);
            font-size: 0.85em;
            margin: 5px 0;
        }

        .code-context {
            background: var(--bg-code);
            border-radius: 4px;
            padding: 10px;
            margin-top: 10px;
            overflow-x: auto;
        }

        .code-line {
            font-family: 'Fira Code', 'Consolas', monospace;
            font-size: 0.85em;
            white-space: pre;
            display: block;
            padding: 2px 0;
        }

        .code-line.highlight {
            background: rgba(233, 69, 96, 0.2);
            margin: 0 -10px;
            padding: 2px 10px;
        }

        .line-number {
            color: var(--text-dim);
            user-select: none;
            display: inline-block;
            width: 40px;
            text-align: right;
            margin-right: 15px;
        }

        .hole-marker {
            color: var(--accent);
            font-weight: bold;
        }

        .category-section {
            margin: 30px 0;
        }

        .category-header {
            display: flex;
            align-items: center;
            gap: 10px;
        }

        .category-count {
            background: var(--accent2);
            padding: 2px 8px;
            border-radius: 4px;
            font-size: 0.8em;
        }

        .toc {
            background: var(--bg-light);
            padding: 20px;
            border-radius: 8px;
            margin: 20px 0;
        }

        .toc h3 {
            margin-top: 0;
        }

        .toc ul {
            columns: 2;
            list-style: none;
            padding: 0;
        }

        .toc li {
            padding: 3px 0;
        }

        .toc a {
            color: var(--blue);
            text-decoration: none;
        }

        .toc a:hover {
            text-decoration: underline;
        }

        @media (max-width: 600px) {
            .toc ul {
                columns: 1;
            }
            .summary {
                grid-template-columns: repeat(2, 1fr);
            }
        }
    </style>
</head>
<body>
    <div class="container">
        <h1>🔍 Idris Proof Holes Report</h1>

        <div class="summary">
            <div class="stat-card">
                <div class="number">""" + str(len(holes)) + """</div>
                <div class="label">Total Holes</div>
            </div>
            <div class="stat-card">
                <div class="number">""" + str(len(by_file)) + """</div>
                <div class="label">Files</div>
            </div>
            <div class="stat-card">
                <div class="number">""" + str(len(categories['substitution'])) + """</div>
                <div class="label">Substitution</div>
            </div>
            <div class="stat-card">
                <div class="number">""" + str(len(categories['weakening'])) + """</div>
                <div class="label">Weakening</div>
            </div>
            <div class="stat-card">
                <div class="number">""" + str(len(categories['conversion'])) + """</div>
                <div class="label">Conversion</div>
            </div>
        </div>

        <div class="progress-bar">
            <div class="progress-fill" style="width: 0%">
                0% Complete
            </div>
        </div>

        <div class="toc">
            <h3>📂 Files</h3>
            <ul>
"""

    for file_path in sorted(by_file.keys()):
        count = len(by_file[file_path])
        html += f'                <li><a href="#file-{file_path.replace("/", "-")}">{file_path}</a> ({count})</li>\n'

    html += """            </ul>
        </div>

        <h2>📁 Holes by File</h2>
"""

    for file_path in sorted(by_file.keys()):
        file_holes = by_file[file_path]
        file_id = file_path.replace("/", "-")

        html += f"""
        <div class="file-section" id="file-{file_id}">
            <div class="file-header">
                <span>{file_path}</span>
                <span class="count">{len(file_holes)} holes</span>
            </div>
"""

        for hole in file_holes:
            html += f"""
            <div class="hole-card">
                <div class="hole-name">?{hole.name}</div>
                <div class="hole-meta">
                    Line {hole.line}
                    {f' • in <code>{hole.in_function}</code>' if hole.in_function else ''}
                </div>
                <div class="code-context">
"""
            for line_num, line_text, is_hole_line in hole.context:
                escaped_line = (line_text
                    .replace('&', '&amp;')
                    .replace('<', '&lt;')
                    .replace('>', '&gt;'))

                # Highlight the hole
                escaped_line = re.sub(
                    r'\?(\w+)',
                    r'<span class="hole-marker">?\1</span>',
                    escaped_line
                )

                highlight = ' highlight' if is_hole_line else ''
                html += f'                    <span class="code-line{highlight}"><span class="line-number">{line_num}</span>{escaped_line}</span>\n'

            html += """                </div>
            </div>
"""

        html += """        </div>
"""

    html += """
        <h2>📊 Holes by Category</h2>
"""

    category_names = {
        'substitution': '🔄 Substitution Lemmas',
        'weakening': '📈 Weakening Lemmas',
        'reduction': '⚡ Reduction Properties',
        'typing': '🏷️ Typing Lemmas',
        'conversion': '🔀 Conversion/Equality',
        'other': '📦 Other'
    }

    for cat, cat_holes in categories.items():
        if not cat_holes:
            continue

        html += f"""
        <div class="category-section">
            <div class="category-header">
                <h3>{category_names[cat]}</h3>
                <span class="category-count">{len(cat_holes)}</span>
            </div>
            <ul>
"""
        for hole in cat_holes:
            rel_file = Path(hole.file).relative_to(base_dir)
            html += f'                <li><code>?{hole.name}</code> — {rel_file}:{hole.line}</li>\n'

        html += """            </ul>
        </div>
"""

    html += """
        <footer style="margin-top: 50px; padding-top: 20px; border-top: 1px solid var(--accent2); color: var(--text-dim); text-align: center;">
            Generated by hole-report.py • lean4idris
        </footer>
    </div>
</body>
</html>
"""

    return html

def main():
    import argparse

    parser = argparse.ArgumentParser(description='Generate HTML report of Idris proof holes')
    parser.add_argument('directory', nargs='?', default='src/Lean4Idris/Proofs',
                        help='Directory to scan for .idr files')
    parser.add_argument('-o', '--output', default='holes.html',
                        help='Output HTML file')

    args = parser.parse_args()

    base_dir = Path.cwd()
    scan_dir = base_dir / args.directory

    if not scan_dir.exists():
        print(f"Error: Directory {scan_dir} does not exist", file=sys.stderr)
        sys.exit(1)

    # Find all holes
    all_holes = []
    for idr_file in scan_dir.rglob('*.idr'):
        holes = find_holes(idr_file)
        all_holes.extend(holes)
        if holes:
            print(f"  {idr_file.relative_to(base_dir)}: {len(holes)} holes")

    print(f"\nTotal: {len(all_holes)} holes in {len(set(h.file for h in all_holes))} files")

    # Generate HTML
    html = generate_html(all_holes, base_dir)

    output_path = Path(args.output)
    output_path.write_text(html)
    print(f"\nReport written to {output_path}")

if __name__ == '__main__':
    main()
