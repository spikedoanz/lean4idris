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

        # Definition body - look for holes and calls
        if current_def and (stripped.startswith(current_def.name) or stripped.startswith('=')):
            # Find holes
            for match in hole_pattern.finditer(line):
                hole_name = match.group(1)
                current_def.holes.append(hole_name)
                current_def.has_holes = True

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

def build_dependency_graph(modules: list[Module]) -> dict:
    """Build a graph structure for D3.js visualization."""
    nodes = []
    links = []
    node_ids = {}

    # Color scheme
    colors = {
        'module': '#e94560',
        'data': '#4ecca3',
        'function': '#00adb5',
        'lemma': '#ffd369',
        'hole': '#ff6b6b',
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
            'size': 20 + len(mod.definitions) * 2,
            'holes': len(mod.holes),
            'file': mod.file,
        })

    # Add definition nodes
    for mod in modules:
        for defn in mod.definitions:
            node_id = f"def_{mod.name}_{defn.name}"
            node_ids[f"{mod.name}.{defn.name}"] = node_id
            node_ids[defn.name] = node_id  # Also index by short name

            nodes.append({
                'id': node_id,
                'label': defn.name,
                'fullName': f"{mod.name}.{defn.name}",
                'type': defn.kind,
                'color': colors.get(defn.kind, colors['function']),
                'size': 8 + len(defn.calls) * 2,
                'hasHoles': defn.has_holes,
                'holes': defn.holes,
                'line': defn.line,
                'file': defn.file,
                'typeSig': defn.type_sig[:50] + ('...' if len(defn.type_sig) > 50 else ''),
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
            --bg: #1a1a2e;
            --bg-light: #16213e;
            --text: #eee;
            --text-dim: #888;
            --accent: #e94560;
            --green: #4ecca3;
            --yellow: #ffd369;
            --blue: #00adb5;
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
            background: var(--bg-light);
            padding: 15px;
            border-radius: 8px;
            z-index: 100;
            max-width: 280px;
        }}

        .controls h1 {{
            font-size: 1.2em;
            color: var(--accent);
            margin-bottom: 10px;
        }}

        .stats {{
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 10px;
            margin-bottom: 15px;
        }}

        .stat {{
            text-align: center;
            padding: 8px;
            background: var(--bg);
            border-radius: 4px;
        }}

        .stat .num {{
            font-size: 1.5em;
            font-weight: bold;
            color: var(--blue);
        }}

        .stat .label {{
            font-size: 0.75em;
            color: var(--text-dim);
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
            background: var(--bg-light);
            border: 1px solid var(--accent);
            padding: 10px 15px;
            border-radius: 6px;
            pointer-events: none;
            z-index: 200;
            max-width: 300px;
            display: none;
        }}

        .tooltip h3 {{
            color: var(--yellow);
            font-family: monospace;
            margin-bottom: 5px;
        }}

        .tooltip .type {{
            color: var(--text-dim);
            font-size: 0.85em;
        }}

        .tooltip .holes {{
            color: var(--accent);
            margin-top: 5px;
        }}

        .tooltip code {{
            background: var(--bg);
            padding: 2px 5px;
            border-radius: 3px;
            font-size: 0.85em;
        }}

        .node {{
            cursor: pointer;
        }}

        .node:hover {{
            filter: brightness(1.3);
        }}

        .link {{
            stroke-opacity: 0.4;
        }}

        .link.imports {{
            stroke: var(--accent);
            stroke-dasharray: 5,5;
        }}

        .link.contains {{
            stroke: var(--text-dim);
        }}

        .link.calls {{
            stroke: var(--blue);
        }}

        .link.has_hole {{
            stroke: #ff6b6b;
            stroke-dasharray: 3,3;
        }}

        .label {{
            font-size: 10px;
            fill: var(--text);
            pointer-events: none;
        }}

        .filter-btn {{
            background: var(--bg);
            border: 1px solid var(--text-dim);
            color: var(--text);
            padding: 5px 10px;
            border-radius: 4px;
            cursor: pointer;
            font-size: 0.8em;
            margin: 2px;
        }}

        .filter-btn:hover {{
            border-color: var(--accent);
        }}

        .filter-btn.active {{
            background: var(--accent);
            border-color: var(--accent);
        }}

        .filters {{
            margin-top: 10px;
        }}
    </style>
</head>
<body>
    <div class="controls">
        <h1>🔗 Proof Dependency Graph</h1>
        <div class="stats">
            <div class="stat">
                <div class="num">{len(modules)}</div>
                <div class="label">Modules</div>
            </div>
            <div class="stat">
                <div class="num">{total_defs}</div>
                <div class="label">Definitions</div>
            </div>
            <div class="stat">
                <div class="num">{total_holes}</div>
                <div class="label">Holes</div>
            </div>
            <div class="stat">
                <div class="num" id="visible-count">{len(graph['nodes'])}</div>
                <div class="label">Visible</div>
            </div>
        </div>
        <div class="filters">
            <button class="filter-btn active" data-type="all">All</button>
            <button class="filter-btn" data-type="module">Modules</button>
            <button class="filter-btn" data-type="lemma">Lemmas</button>
            <button class="filter-btn" data-type="hole">Holes</button>
            <button class="filter-btn" data-type="with-holes">With Holes</button>
        </div>
        <div class="legend">
            <div class="legend-item">
                <div class="legend-dot" style="background: #e94560"></div>
                <span>Module</span>
            </div>
            <div class="legend-item">
                <div class="legend-dot" style="background: #4ecca3"></div>
                <span>Data</span>
            </div>
            <div class="legend-item">
                <div class="legend-dot" style="background: #00adb5"></div>
                <span>Function</span>
            </div>
            <div class="legend-item">
                <div class="legend-dot" style="background: #ffd369"></div>
                <span>Lemma</span>
            </div>
            <div class="legend-item">
                <div class="legend-dot" style="background: #ff6b6b"></div>
                <span>Hole</span>
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
            .attr("markerWidth", 6)
            .attr("markerHeight", 6)
            .attr("orient", "auto")
            .append("path")
            .attr("fill", d => {{
                if (d === "imports") return "#e94560";
                if (d === "calls") return "#00adb5";
                if (d === "has_hole") return "#ff6b6b";
                return "#888";
            }})
            .attr("d", "M0,-5L10,0L0,5");

        // Force simulation
        const simulation = d3.forceSimulation(graphData.nodes)
            .force("link", d3.forceLink(graphData.links).id(d => d.id).distance(80))
            .force("charge", d3.forceManyBody().strength(-200))
            .force("center", d3.forceCenter(width / 2, height / 2))
            .force("collision", d3.forceCollide().radius(d => d.size + 5));

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

                node.style("opacity", d => {{
                    if (filterType === "all") return 1;
                    if (filterType === "with-holes") return d.hasHoles || d.type === "hole" ? 1 : 0.1;
                    return d.type === filterType ? 1 : 0.1;
                }});

                label.style("opacity", d => {{
                    if (filterType === "all") return 1;
                    if (filterType === "with-holes") return d.hasHoles || d.type === "hole" ? 1 : 0.1;
                    return d.type === filterType ? 1 : 0.1;
                }});

                link.style("opacity", d => {{
                    if (filterType === "all") return 0.4;
                    return 0.1;
                }});

                // Update visible count
                let count = graphData.nodes.filter(d => {{
                    if (filterType === "all") return true;
                    if (filterType === "with-holes") return d.hasHoles || d.type === "hole";
                    return d.type === filterType;
                }}).length;
                document.getElementById("visible-count").textContent = count;
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
