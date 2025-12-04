#!/usr/bin/env python3
"""
Generate an interactive dependency graph for Idris proof files.

Analyzes imports, function calls, and hole dependencies to create
a visual graph using D3.js force-directed layout.

Usage: python tools/proof-graph.py [directory] [-o output.html]
"""

import re
import sys
import json
import math
from pathlib import Path
from dataclasses import dataclass, field
from collections import defaultdict

@dataclass
class Definition:
    name: str
    file: str
    line: int
    type_sig: str = ""
    has_holes: bool = False
    holes: list[str] = field(default_factory=list)
    calls: list[str] = field(default_factory=list)  # functions this def uses
    kind: str = "function"  # function, data, lemma, theorem

@dataclass
class Module:
    name: str
    file: str
    imports: list[str] = field(default_factory=list)
    definitions: list[Definition] = field(default_factory=list)
    holes: list[str] = field(default_factory=list)

def parse_module(file_path: Path) -> Module:
    """Parse an Idris file to extract module info, definitions, and dependencies."""
    content = file_path.read_text()
    lines = content.splitlines()

    module_name = ""
    imports = []
    definitions = []

    # Extract module name
    for line in lines:
        if match := re.match(r'^module\s+([\w.]+)', line):
            module_name = match.group(1)
            break

    # Extract imports
    for line in lines:
        if match := re.match(r'^import\s+([\w.]+)', line):
            imports.append(match.group(1))

    # Extract definitions
    current_def = None
    current_type = ""
    in_type_sig = False

    # Patterns
    type_sig_pattern = re.compile(r'^(\w+)\s*:\s*(.+)')
    def_pattern = re.compile(r'^(\w+)\s+.*=')
    data_pattern = re.compile(r'^data\s+(\w+)')
    hole_pattern = re.compile(r'\?(\w+)')
    believe_me_pattern = re.compile(r'\bbelieve_me\b')

    # Known function names in our codebase (for dependency tracking)
    known_names = set()

    # First pass: collect all definition names
    for i, line in enumerate(lines):
        if match := type_sig_pattern.match(line):
            known_names.add(match.group(1))
        if match := data_pattern.match(line):
            known_names.add(match.group(1))

    # Second pass: parse definitions and find dependencies
    for i, line in enumerate(lines):
        # Skip comments
        stripped = line.strip()
        if stripped.startswith('--') or stripped.startswith('|||'):
            continue

        # Data type
        if match := data_pattern.match(line):
            name = match.group(1)
            definitions.append(Definition(
                name=name,
                file=str(file_path),
                line=i + 1,
                kind="data"
            ))
            continue

        # Type signature
        if match := type_sig_pattern.match(line):
            # Save previous definition before starting a new one
            if current_def and current_def.name not in [d.name for d in definitions]:
                definitions.append(current_def)

            name = match.group(1)
            type_sig = match.group(2)

            # Determine kind based on name/type
            kind = "function"
            if any(kw in name.lower() for kw in ['lemma', 'theorem', 'proof']):
                kind = "lemma"
            elif 'Lemma' in type_sig or '=' in type_sig:
                kind = "lemma"

            current_def = Definition(
                name=name,
                file=str(file_path),
                line=i + 1,
                type_sig=type_sig,
                kind=kind
            )
            continue

        # Definition body - look for holes, believe_me, and calls
        # Include: lines starting with def name, '=', or indented continuation lines
        in_def_body = current_def and (
            stripped.startswith(current_def.name) or
            stripped.startswith('=') or
            (line and line[0].isspace())  # indented continuation
        )
        if in_def_body:
            # Find holes
            for match in hole_pattern.finditer(line):
                hole_name = match.group(1)
                current_def.holes.append(hole_name)
                current_def.has_holes = True

            # Detect believe_me (treated as unproven)
            if believe_me_pattern.search(line):
                current_def.has_holes = True
                if 'believe_me' not in current_def.holes:
                    current_def.holes.append('believe_me')

            # Find calls to known functions
            words = re.findall(r'\b(\w+)\b', line)
            for word in words:
                if word in known_names and word != current_def.name:
                    if word not in current_def.calls:
                        current_def.calls.append(word)

        # Check if we're still in the same definition
        if current_def and line and not line[0].isspace() and not stripped.startswith(current_def.name):
            if current_def.name not in [d.name for d in definitions]:
                definitions.append(current_def)
            current_def = None

    # Don't forget the last definition
    if current_def and current_def.name not in [d.name for d in definitions]:
        definitions.append(current_def)

    # Collect all holes in module
    all_holes = []
    for defn in definitions:
        all_holes.extend(defn.holes)

    return Module(
        name=module_name,
        file=str(file_path),
        imports=imports,
        definitions=definitions,
        holes=all_holes
    )

def compute_depth(node_id: str, links: list[dict], memo: dict) -> int:
    """Compute depth of a node (0 = leaf/no dependencies, higher = more dependencies)."""
    if node_id in memo:
        return memo[node_id]

    # Find all nodes this node depends on (outgoing "calls" or "imports" links)
    dependencies = [l['target'] for l in links
                   if l['source'] == node_id and l['type'] in ('calls', 'imports')]

    if not dependencies:
        memo[node_id] = 0
        return 0

    max_dep_depth = max(compute_depth(dep, links, memo) for dep in dependencies)
    memo[node_id] = max_dep_depth + 1
    return memo[node_id]

def build_dependency_graph(modules: list[Module]) -> dict:
    """Build a graph structure for D3.js visualization."""
    nodes = []
    links = []
    node_ids = {}

    # Color scheme: green = proven, white = unproven/has holes
    colors = {
        'module': '#6b7280',      # gray for modules
        'data': '#8b5cf6',        # purple for data types
        'function': '#22c55e',    # green for proven functions
        'function_unproven': '#ffffff',  # white for unproven
        'lemma': '#22c55e',       # green for proven lemmas
        'lemma_unproven': '#ffffff',     # white for unproven
        'hole': '#ef4444',        # red for holes
    }

    # Add module nodes
    for mod in modules:
        short_name = mod.name.split('.')[-1]
        node_id = f"mod_{mod.name}"
        node_ids[mod.name] = node_id
        nodes.append({
            'id': node_id,
            'label': short_name,
            'fullName': mod.name,
            'type': 'module',
            'color': colors['module'],
            'size': 8 + math.sqrt(len(mod.definitions)) * 4,  # sqrt scaling
            'holes': len(mod.holes),
            'file': mod.file,
        })

    # Add definition nodes
    for mod in modules:
        for defn in mod.definitions:
            node_id = f"def_{mod.name}_{defn.name}"
            node_ids[f"{mod.name}.{defn.name}"] = node_id
            node_ids[defn.name] = node_id  # Also index by short name

            # Choose color based on proof status
            if defn.has_holes:
                color = colors.get(f'{defn.kind}_unproven', colors['function_unproven'])
            else:
                color = colors.get(defn.kind, colors['function'])

            nodes.append({
                'id': node_id,
                'label': defn.name,
                'fullName': f"{mod.name}.{defn.name}",
                'type': defn.kind,
                'color': color,
                'size': 4 + math.sqrt(len(defn.calls) + 1) * 3,  # sqrt scaling like Mathlib
                'hasHoles': defn.has_holes,
                'holes': defn.holes,
                'line': defn.line,
                'file': defn.file,
                'typeSig': defn.type_sig[:50] + ('...' if len(defn.type_sig) > 50 else ''),
                'proven': not defn.has_holes,
            })

            # Link to parent module
            links.append({
                'source': node_ids[mod.name],
                'target': node_id,
                'type': 'contains',
            })

    # Add hole nodes
    all_holes = set()
    for mod in modules:
        for defn in mod.definitions:
            for hole in defn.holes:
                if hole not in all_holes:
                    all_holes.add(hole)
                    hole_id = f"hole_{hole}"
                    node_ids[hole] = hole_id
                    nodes.append({
                        'id': hole_id,
                        'label': f"?{hole}",
                        'type': 'hole',
                        'color': colors['hole'],
                        'size': 6,
                    })

                # Link definition to hole
                def_id = node_ids.get(defn.name)
                hole_id = f"hole_{hole}"
                if def_id:
                    links.append({
                        'source': def_id,
                        'target': hole_id,
                        'type': 'has_hole',
                    })

    # Add module import links
    for mod in modules:
        for imp in mod.imports:
            if imp in node_ids:
                links.append({
                    'source': node_ids[mod.name],
                    'target': node_ids[imp],
                    'type': 'imports',
                })

    # Add function call links
    for mod in modules:
        for defn in mod.definitions:
            source_id = node_ids.get(defn.name)
            if not source_id:
                continue
            for call in defn.calls:
                target_id = node_ids.get(call)
                if target_id and source_id != target_id:
                    links.append({
                        'source': source_id,
                        'target': target_id,
                        'type': 'calls',
                    })

    # Compute depth for each node (for hierarchical layout)
    # Depth = how many layers of dependencies below this node
    memo = {}
    # Build simple adjacency for depth computation (using node IDs directly)
    simple_links = [{'source': l['source'], 'target': l['target'], 'type': l['type']}
                    for l in links]

    for node in nodes:
        node['depth'] = compute_depth(node['id'], simple_links, memo)

    max_depth = max((n['depth'] for n in nodes), default=0)
    for node in nodes:
        node['maxDepth'] = max_depth

    return {'nodes': nodes, 'links': links}

def generate_html(graph: dict, modules: list[Module]) -> str:
    """Generate interactive HTML visualization."""

    total_holes = sum(len(m.holes) for m in modules)
    total_defs = sum(len(m.definitions) for m in modules)

    graph_json = json.dumps(graph, indent=2)

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Proof Dependency Graph</title>
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <style>
        :root {{
            --bg: #000000;
            --bg-light: #111111;
            --bg-card: #1a1a1a;
            --text: #f0f0f0;
            --text-dim: #666;
            --green: #22c55e;
            --white: #ffffff;
            --red: #ef4444;
            --purple: #8b5cf6;
            --gray: #6b7280;
        }}

        * {{ box-sizing: border-box; margin: 0; padding: 0; }}

        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            background: var(--bg);
            color: var(--text);
            overflow: hidden;
        }}

        #graph {{
            width: 100vw;
            height: 100vh;
        }}

        .controls {{
            position: fixed;
            top: 20px;
            left: 20px;
            background: var(--bg-card);
            padding: 15px 20px;
            border-radius: 12px;
            border: 1px solid #333;
            z-index: 100;
            max-width: 300px;
            backdrop-filter: blur(10px);
        }}

        .controls h1 {{
            font-size: 1.1em;
            font-weight: 600;
            color: var(--text);
            margin-bottom: 12px;
        }}

        .stats {{
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 8px;
            margin-bottom: 15px;
        }}

        .stat {{
            text-align: center;
            padding: 10px 8px;
            background: var(--bg-light);
            border-radius: 8px;
            border: 1px solid #222;
        }}

        .stat .num {{
            font-size: 1.4em;
            font-weight: 600;
            color: var(--text);
        }}

        .stat.proven .num {{
            color: var(--green);
        }}

        .stat.unproven .num {{
            color: var(--white);
        }}

        .stat .label {{
            font-size: 0.7em;
            color: var(--text-dim);
            text-transform: uppercase;
            letter-spacing: 0.5px;
        }}

        .legend {{
            display: flex;
            flex-wrap: wrap;
            gap: 8px;
            margin-top: 10px;
        }}

        .legend-item {{
            display: flex;
            align-items: center;
            gap: 5px;
            font-size: 0.8em;
        }}

        .legend-dot {{
            width: 12px;
            height: 12px;
            border-radius: 50%;
        }}

        .tooltip {{
            position: fixed;
            background: var(--bg-card);
            border: 1px solid #444;
            padding: 12px 16px;
            border-radius: 8px;
            pointer-events: none;
            z-index: 200;
            max-width: 320px;
            display: none;
            box-shadow: 0 4px 20px rgba(0,0,0,0.5);
        }}

        .tooltip h3 {{
            color: var(--text);
            font-family: 'SF Mono', Consolas, monospace;
            font-size: 0.95em;
            margin-bottom: 6px;
        }}

        .tooltip .type {{
            color: var(--text-dim);
            font-size: 0.8em;
        }}

        .tooltip .status {{
            margin-top: 6px;
            font-size: 0.85em;
        }}

        .tooltip .status.proven {{
            color: var(--green);
        }}

        .tooltip .status.unproven {{
            color: var(--white);
        }}

        .tooltip .holes {{
            color: var(--red);
            margin-top: 5px;
            font-size: 0.85em;
        }}

        .tooltip code {{
            background: var(--bg);
            padding: 2px 6px;
            border-radius: 4px;
            font-size: 0.8em;
            color: var(--text-dim);
        }}

        .node {{
            cursor: pointer;
        }}

        .node:hover {{
            filter: brightness(1.3);
        }}

        .link {{
            stroke-opacity: 0.3;
        }}

        .link.imports {{
            stroke: var(--gray);
            stroke-dasharray: 4,4;
        }}

        .link.contains {{
            stroke: #333;
        }}

        .link.calls {{
            stroke: #444;
        }}

        .link.has_hole {{
            stroke: var(--red);
            stroke-opacity: 0.5;
            stroke-dasharray: 3,3;
        }}

        .label {{
            font-size: 10px;
            fill: var(--text);
            pointer-events: none;
        }}

        .filter-btn {{
            background: var(--bg-light);
            border: 1px solid #333;
            color: var(--text-dim);
            padding: 6px 12px;
            border-radius: 6px;
            cursor: pointer;
            font-size: 0.75em;
            margin: 2px;
            transition: all 0.15s;
        }}

        .filter-btn:hover {{
            border-color: #555;
            color: var(--text);
        }}

        .filter-btn.active {{
            background: var(--green);
            border-color: var(--green);
            color: #000;
        }}

        .filters {{
            margin-top: 10px;
        }}
    </style>
</head>
<body>
    <div class="controls">
        <h1>Proof Dependency Graph</h1>
        <div class="stats">
            <div class="stat proven">
                <div class="num" id="proven-count">0</div>
                <div class="label">Proven</div>
            </div>
            <div class="stat unproven">
                <div class="num" id="unproven-count">0</div>
                <div class="label">Unproven</div>
            </div>
            <div class="stat">
                <div class="num">{len(modules)}</div>
                <div class="label">Modules</div>
            </div>
            <div class="stat">
                <div class="num">{total_holes}</div>
                <div class="label">Holes</div>
            </div>
        </div>
        <div class="filters">
            <button class="filter-btn active" data-type="all">All</button>
            <button class="filter-btn" data-type="proven">Proven</button>
            <button class="filter-btn" data-type="unproven">Unproven</button>
            <button class="filter-btn" data-type="module">Modules</button>
        </div>
        <div class="legend">
            <div class="legend-item">
                <div class="legend-dot" style="background: #22c55e"></div>
                <span>Proven</span>
            </div>
            <div class="legend-item">
                <div class="legend-dot" style="background: #ffffff; border: 1px solid #666"></div>
                <span>Unproven</span>
            </div>
            <div class="legend-item">
                <div class="legend-dot" style="background: #8b5cf6"></div>
                <span>Data</span>
            </div>
            <div class="legend-item">
                <div class="legend-dot" style="background: #6b7280"></div>
                <span>Module</span>
            </div>
        </div>
    </div>

    <div class="tooltip" id="tooltip"></div>

    <svg id="graph"></svg>

    <script>
        const graphData = {graph_json};

        const width = window.innerWidth;
        const height = window.innerHeight;

        const svg = d3.select("#graph")
            .attr("width", width)
            .attr("height", height);

        // Add zoom behavior
        const g = svg.append("g");

        svg.call(d3.zoom()
            .scaleExtent([0.1, 4])
            .on("zoom", (event) => {{
                g.attr("transform", event.transform);
            }}));

        // Create arrow markers for links
        svg.append("defs").selectAll("marker")
            .data(["imports", "calls", "contains", "has_hole"])
            .join("marker")
            .attr("id", d => `arrow-${{d}}`)
            .attr("viewBox", "0 -5 10 10")
            .attr("refX", 20)
            .attr("refY", 0)
            .attr("markerWidth", 5)
            .attr("markerHeight", 5)
            .attr("orient", "auto")
            .append("path")
            .attr("fill", d => {{
                if (d === "imports") return "#6b7280";
                if (d === "calls") return "#444";
                if (d === "has_hole") return "#ef4444";
                return "#333";
            }})
            .attr("d", "M0,-5L10,0L0,5");

        // Count proven/unproven
        const provenCount = graphData.nodes.filter(d => d.proven === true).length;
        const unprovenCount = graphData.nodes.filter(d => d.proven === false).length;
        document.getElementById("proven-count").textContent = provenCount;
        document.getElementById("unproven-count").textContent = unprovenCount;

        // Calculate max depth for vertical spacing
        const maxDepth = Math.max(...graphData.nodes.map(d => d.depth || 0));
        const verticalSpacing = height / (maxDepth + 2);

        // Custom force to push nodes to their depth level (top = highest depth)
        function forceY(alpha) {{
            for (const node of graphData.nodes) {{
                // Higher depth = higher on screen (lower y value)
                // depth 0 (leaves) at bottom, max depth (roots) at top
                const targetY = 80 + (maxDepth - (node.depth || 0)) * verticalSpacing;
                node.vy += (targetY - node.y) * alpha * 0.3;
            }}
        }}

        // Force simulation with hierarchical Y positioning
        const simulation = d3.forceSimulation(graphData.nodes)
            .force("link", d3.forceLink(graphData.links).id(d => d.id).distance(100).strength(0.3))
            .force("charge", d3.forceManyBody().strength(-300))
            .force("x", d3.forceX(width / 2).strength(0.05))
            .force("y", forceY)
            .force("collision", d3.forceCollide().radius(d => d.size + 10));

        // Draw links
        const link = g.append("g")
            .selectAll("line")
            .data(graphData.links)
            .join("line")
            .attr("class", d => `link ${{d.type}}`)
            .attr("stroke-width", 1.5)
            .attr("marker-end", d => `url(#arrow-${{d.type}})`);

        // Draw nodes
        const node = g.append("g")
            .selectAll("circle")
            .data(graphData.nodes)
            .join("circle")
            .attr("class", "node")
            .attr("r", d => d.size)
            .attr("fill", d => d.color)
            .attr("stroke", d => d.hasHoles ? "#ff6b6b" : "none")
            .attr("stroke-width", d => d.hasHoles ? 3 : 0)
            .call(d3.drag()
                .on("start", dragstarted)
                .on("drag", dragged)
                .on("end", dragended));

        // Add labels
        const label = g.append("g")
            .selectAll("text")
            .data(graphData.nodes)
            .join("text")
            .attr("class", "label")
            .attr("dx", d => d.size + 3)
            .attr("dy", 3)
            .text(d => d.label);

        // Tooltip
        const tooltip = d3.select("#tooltip");

        node.on("mouseover", (event, d) => {{
            let html = `<h3>${{d.label}}</h3>`;
            html += `<div class="type">${{d.type}}</div>`;
            if (d.typeSig) {{
                html += `<div><code>${{d.typeSig}}</code></div>`;
            }}
            if (d.proven !== undefined) {{
                const statusClass = d.proven ? 'proven' : 'unproven';
                const statusText = d.proven ? '✓ Proven' : '○ Unproven';
                html += `<div class="status ${{statusClass}}">${{statusText}}</div>`;
            }}
            if (d.holes && d.holes.length > 0) {{
                html += `<div class="holes">Holes: ${{d.holes.map(h => '?' + h).join(', ')}}</div>`;
            }}
            if (d.file) {{
                html += `<div class="type">${{d.file.split('/').pop()}}:${{d.line || ''}}</div>`;
            }}

            tooltip.html(html)
                .style("display", "block")
                .style("left", (event.pageX + 15) + "px")
                .style("top", (event.pageY - 10) + "px");
        }})
        .on("mouseout", () => {{
            tooltip.style("display", "none");
        }});

        // Update positions on tick
        simulation.on("tick", () => {{
            link
                .attr("x1", d => d.source.x)
                .attr("y1", d => d.source.y)
                .attr("x2", d => d.target.x)
                .attr("y2", d => d.target.y);

            node
                .attr("cx", d => d.x)
                .attr("cy", d => d.y);

            label
                .attr("x", d => d.x)
                .attr("y", d => d.y);
        }});

        // Drag functions
        function dragstarted(event) {{
            if (!event.active) simulation.alphaTarget(0.3).restart();
            event.subject.fx = event.subject.x;
            event.subject.fy = event.subject.y;
        }}

        function dragged(event) {{
            event.subject.fx = event.x;
            event.subject.fy = event.y;
        }}

        function dragended(event) {{
            if (!event.active) simulation.alphaTarget(0);
            event.subject.fx = null;
            event.subject.fy = null;
        }}

        // Filter buttons
        document.querySelectorAll('.filter-btn').forEach(btn => {{
            btn.addEventListener('click', () => {{
                document.querySelectorAll('.filter-btn').forEach(b => b.classList.remove('active'));
                btn.classList.add('active');

                const filterType = btn.dataset.type;

                const isVisible = (d) => {{
                    if (filterType === "all") return true;
                    if (filterType === "proven") return d.proven === true;
                    if (filterType === "unproven") return d.proven === false;
                    return d.type === filterType;
                }};

                node.style("opacity", d => isVisible(d) ? 1 : 0.08);
                label.style("opacity", d => isVisible(d) ? 1 : 0.08);
                link.style("opacity", filterType === "all" ? 0.3 : 0.05);
            }});
        }});
    </script>
</body>
</html>
"""
    return html

def main():
    import argparse

    parser = argparse.ArgumentParser(description='Generate proof dependency graph')
    parser.add_argument('directory', nargs='?', default='src/Lean4Idris/Proofs',
                        help='Directory to scan for .idr files')
    parser.add_argument('-o', '--output', default='docs/proof-graph.html',
                        help='Output HTML file')

    args = parser.parse_args()

    base_dir = Path.cwd()
    scan_dir = base_dir / args.directory

    if not scan_dir.exists():
        print(f"Error: Directory {scan_dir} does not exist", file=sys.stderr)
        sys.exit(1)

    # Parse all modules
    modules = []
    for idr_file in sorted(scan_dir.rglob('*.idr')):
        print(f"Parsing {idr_file.relative_to(base_dir)}...")
        module = parse_module(idr_file)
        modules.append(module)
        print(f"  {len(module.definitions)} definitions, {len(module.holes)} holes")

    print(f"\nBuilding dependency graph...")
    graph = build_dependency_graph(modules)
    print(f"  {len(graph['nodes'])} nodes, {len(graph['links'])} edges")

    # Generate HTML
    html = generate_html(graph, modules)

    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(html)
    print(f"\nGraph written to {output_path}")

if __name__ == '__main__':
    main()
