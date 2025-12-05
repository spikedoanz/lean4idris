#!/bin/bash
# Export Lean modules to the lean4export format for testing lean4idris
#
# This exports the FULL dependency hierarchy:
#   Tier 1: Init (core prelude - Nat, Bool, List, etc.)
#   Tier 2: Std (standard library data structures)
#   Tier 3: Lean (compiler/elaborator infrastructure)
#   Tier 4: Batteries.Data (community stdlib data structures)
#   Tier 5: Batteries.Tactic (community tactics)
#   Tier 6: Mathlib.Data (mathlib basic data)
#   Tier 7: Mathlib.Algebra (algebraic structures)
#   Tier 8: Mathlib.Analysis (analysis/topology)
#   Tier 9: Mathlib.CategoryTheory (category theory)
#   Tier 10: Mathlib.Advanced (heavy features - ordinals, quotients, etc.)
#
# Usage: ./tools/export-all.sh [tier|all]
#   tier: 1-10 or "all" (default: all)
#
# Prerequisites:
#   - lake (Lean build tool) must be installed
#   - elan (Lean version manager) recommended

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
EXPORTER_DIR="$REPO_ROOT/tools/mathlib-exporter"
EXPORT_DIR="$REPO_ROOT/test/exports"

TIER="${1:-all}"

# ============================================================================
# TIER 1: Init (Core Prelude)
# These are the foundational definitions that everything depends on
# ============================================================================
TIER1_MODULES=(
    "Init.Core"
    "Init.Prelude"
    "Init.Data.Nat.Basic"
    "Init.Data.Nat.Lemmas"
    "Init.Data.Bool.Basic"
    "Init.Data.Bool.Lemmas"
    "Init.Data.List.Basic"
    "Init.Data.List.Lemmas"
    "Init.Data.Array.Basic"
    "Init.Data.Option.Basic"
    "Init.Data.Int.Basic"
    "Init.Data.Fin.Basic"
    "Init.Data.UInt.Basic"
    "Init.Data.Char.Basic"
    "Init.Data.String.Basic"
    "Init.PropLemmas"
    "Init.Classical"
)

# ============================================================================
# TIER 2: Std (Standard Library)
# Data structures and utilities in the standard library
# Note: Std modules are HashMap/TreeMap focused, basic types are in Init
# ============================================================================
TIER2_MODULES=(
    "Std.Data.HashMap"
    "Std.Data.HashSet"
    "Std.Data.TreeMap"
    "Std.Data.TreeSet"
    "Std.Data.DHashMap"
    "Std.Data.DTreeMap"
    "Std.Tactic.BVDecide"
    "Std.Sat.CNF"
)

# ============================================================================
# TIER 3: Lean (Compiler Infrastructure)
# The Lean compiler, elaborator, and meta-programming infrastructure
# ============================================================================
TIER3_MODULES=(
    "Lean.Data.Name"
    "Lean.Data.HashMap"
    "Lean.Data.PersistentHashMap"
    "Lean.Data.RBMap"
    "Lean.Level"
    "Lean.Expr"
    "Lean.Declaration"
    "Lean.Environment"
    "Lean.LocalContext"
    "Lean.Meta.Basic"
    "Lean.Meta.InferType"
    "Lean.Meta.WHNF"
    "Lean.Meta.Reduce"
    "Lean.Elab.Term"
    "Lean.Elab.Command"
)

# ============================================================================
# TIER 4: Batteries.Data (Community Data Structures)
# Extensions to the standard library data structures
# ============================================================================
TIER4_MODULES=(
    "Batteries.Data.Nat.Basic"
    "Batteries.Data.Nat.Lemmas"
    "Batteries.Data.Int"
    "Batteries.Data.List.Basic"
    "Batteries.Data.List.Lemmas"
    "Batteries.Data.Array.Basic"
    "Batteries.Data.Array.Lemmas"
    "Batteries.Data.Fin.Basic"
    "Batteries.Data.Fin.Lemmas"
    "Batteries.Data.HashMap.Basic"
    "Batteries.Data.RBMap.Basic"
    "Batteries.Data.BitVec.Basic"
    "Batteries.Data.String.Basic"
    "Batteries.Data.Vector.Basic"
)

# ============================================================================
# TIER 5: Batteries.Lean & Batteries.Tactic
# Meta-programming utilities and tactics
# ============================================================================
TIER5_MODULES=(
    "Batteries.Lean.HashMap"
    "Batteries.Lean.Meta.Basic"
    "Batteries.Lean.Meta.Expr"
    "Batteries.Lean.Syntax"
    "Batteries.Tactic.Basic"
    "Batteries.Tactic.Alias"
    "Batteries.Tactic.Lint.Basic"
    "Batteries.Tactic.Exact"
)

# ============================================================================
# TIER 6: Mathlib.Data (Basic Mathematical Data Types)
# ============================================================================
TIER6_MODULES=(
    "Mathlib.Data.Nat.Basic"
    "Mathlib.Data.Nat.Prime.Basic"
    "Mathlib.Data.Int.Basic"
    "Mathlib.Data.Int.Order.Basic"
    "Mathlib.Data.List.Basic"
    "Mathlib.Data.Fin.Basic"
    "Mathlib.Data.Option.Basic"
    "Mathlib.Data.Bool.Basic"
    "Mathlib.Logic.Basic"
    "Mathlib.Init.Set"
)

# ============================================================================
# TIER 7: Mathlib.Algebra (Algebraic Structures)
# ============================================================================
TIER7_MODULES=(
    "Mathlib.Algebra.Group.Basic"
    "Mathlib.Algebra.Group.Defs"
    "Mathlib.Algebra.Ring.Basic"
    "Mathlib.Algebra.Ring.Defs"
    "Mathlib.Algebra.Field.Basic"
    "Mathlib.Algebra.Order.Monoid.Basic"
    "Mathlib.GroupTheory.Subgroup.Basic"
    "Mathlib.GroupTheory.Perm.Basic"
)

# ============================================================================
# TIER 8: Mathlib.Analysis (Analysis and Topology)
# ============================================================================
TIER8_MODULES=(
    "Mathlib.Topology.Basic"
    "Mathlib.Topology.Order"
    "Mathlib.Topology.MetricSpace.Basic"
    "Mathlib.Analysis.Normed.Field.Basic"
    "Mathlib.Analysis.SpecialFunctions.Pow.Real"
    "Mathlib.Order.Filter.Basic"
)

# ============================================================================
# TIER 9: Mathlib.CategoryTheory
# ============================================================================
TIER9_MODULES=(
    "Mathlib.CategoryTheory.Category.Basic"
    "Mathlib.CategoryTheory.Functor.Basic"
    "Mathlib.CategoryTheory.NatTrans"
    "Mathlib.CategoryTheory.Iso"
    "Mathlib.CategoryTheory.Yoneda"
    "Mathlib.CategoryTheory.Limits.Shapes.Terminal"
)

# ============================================================================
# TIER 10: Mathlib.Advanced (Heavy Features)
# Complex type theory features: quotients, ordinals, mutual inductives
# ============================================================================
TIER10_MODULES=(
    "Mathlib.Data.Tree.Basic"                    # Mutual inductives
    "Mathlib.Data.W.Basic"                       # W-types (nested inductives)
    "Mathlib.SetTheory.Ordinal.Basic"            # Heavy universe polymorphism
    "Mathlib.GroupTheory.QuotientGroup.Basic"    # Quotient types
    "Mathlib.SetTheory.Cardinal.Basic"           # Cardinals
    "Mathlib.Logic.Equiv.Basic"                  # Equivalences
)

echo "=== Lean4Idris Full Library Exporter ==="
echo "Repository root: $REPO_ROOT"
echo "Exporter dir: $EXPORTER_DIR"
echo "Export dir: $EXPORT_DIR"
echo ""

# Create directories for all tiers
mkdir -p "$EXPORT_DIR"/{tier01-init,tier02-std,tier03-lean,tier04-batteries-data,tier05-batteries-tactic,tier06-mathlib-data,tier07-mathlib-algebra,tier08-mathlib-analysis,tier09-mathlib-category,tier10-mathlib-advanced}

# Setup exporter project if needed
cd "$EXPORTER_DIR"

if [ ! -f "lake-manifest.json" ]; then
    echo "=== Setting up Mathlib project ==="
    lake update
fi

# Download Mathlib cache (much faster than building from source)
echo "=== Downloading Mathlib cache ==="
lake exe cache get || echo "Cache download failed, will build from source"

# Build lean4export
echo "=== Building lean4export ==="
lake build lean4export

export_module() {
    local module="$1"
    local output_file="$2"

    echo "Exporting: $module -> $output_file"

    # Use lake env to get correct LEAN_PATH
    if lake env .lake/packages/lean4export/.lake/build/bin/lean4export "$module" > "$output_file" 2>/dev/null; then
        local lines=$(wc -l < "$output_file")
        local size=$(du -h "$output_file" | cut -f1)
        echo "  Success: $lines lines, $size"
    else
        echo "  FAILED: $module"
        rm -f "$output_file"
        return 1
    fi
}

export_tier() {
    local tier_num="$1"
    local tier_dir="$2"
    shift 2
    local modules=("$@")

    echo ""
    echo "=== Exporting Tier $tier_num: $tier_dir ==="
    local success=0
    local failed=0

    for module in "${modules[@]}"; do
        # Convert module name to filename (Init.Core -> Init.Core.export)
        local filename="${module}.export"
        local output_path="$EXPORT_DIR/$tier_dir/$filename"

        if export_module "$module" "$output_path"; then
            ((success++))
        else
            ((failed++))
        fi
    done

    echo "Tier $tier_num: $success succeeded, $failed failed"
}

case "$TIER" in
    1)
        export_tier 1 "tier01-init" "${TIER1_MODULES[@]}"
        ;;
    2)
        export_tier 2 "tier02-std" "${TIER2_MODULES[@]}"
        ;;
    3)
        export_tier 3 "tier03-lean" "${TIER3_MODULES[@]}"
        ;;
    4)
        export_tier 4 "tier04-batteries-data" "${TIER4_MODULES[@]}"
        ;;
    5)
        export_tier 5 "tier05-batteries-tactic" "${TIER5_MODULES[@]}"
        ;;
    6)
        export_tier 6 "tier06-mathlib-data" "${TIER6_MODULES[@]}"
        ;;
    7)
        export_tier 7 "tier07-mathlib-algebra" "${TIER7_MODULES[@]}"
        ;;
    8)
        export_tier 8 "tier08-mathlib-analysis" "${TIER8_MODULES[@]}"
        ;;
    9)
        export_tier 9 "tier09-mathlib-category" "${TIER9_MODULES[@]}"
        ;;
    10)
        export_tier 10 "tier10-mathlib-advanced" "${TIER10_MODULES[@]}"
        ;;
    all)
        export_tier 1 "tier01-init" "${TIER1_MODULES[@]}"
        export_tier 2 "tier02-std" "${TIER2_MODULES[@]}"
        export_tier 3 "tier03-lean" "${TIER3_MODULES[@]}"
        export_tier 4 "tier04-batteries-data" "${TIER4_MODULES[@]}"
        export_tier 5 "tier05-batteries-tactic" "${TIER5_MODULES[@]}"
        export_tier 6 "tier06-mathlib-data" "${TIER6_MODULES[@]}"
        export_tier 7 "tier07-mathlib-algebra" "${TIER7_MODULES[@]}"
        export_tier 8 "tier08-mathlib-analysis" "${TIER8_MODULES[@]}"
        export_tier 9 "tier09-mathlib-category" "${TIER9_MODULES[@]}"
        export_tier 10 "tier10-mathlib-advanced" "${TIER10_MODULES[@]}"
        ;;
    init)
        # Quick mode: just tier 1-3 (Lean core)
        export_tier 1 "tier01-init" "${TIER1_MODULES[@]}"
        export_tier 2 "tier02-std" "${TIER2_MODULES[@]}"
        export_tier 3 "tier03-lean" "${TIER3_MODULES[@]}"
        ;;
    batteries)
        # Batteries only: tier 4-5
        export_tier 4 "tier04-batteries-data" "${TIER4_MODULES[@]}"
        export_tier 5 "tier05-batteries-tactic" "${TIER5_MODULES[@]}"
        ;;
    mathlib)
        # Mathlib only: tier 6-10
        export_tier 6 "tier06-mathlib-data" "${TIER6_MODULES[@]}"
        export_tier 7 "tier07-mathlib-algebra" "${TIER7_MODULES[@]}"
        export_tier 8 "tier08-mathlib-analysis" "${TIER8_MODULES[@]}"
        export_tier 9 "tier09-mathlib-category" "${TIER9_MODULES[@]}"
        export_tier 10 "tier10-mathlib-advanced" "${TIER10_MODULES[@]}"
        ;;
    *)
        echo "Unknown tier: $TIER"
        echo "Usage: $0 [1|2|3|4|5|6|7|8|9|10|all|init|batteries|mathlib]"
        echo ""
        echo "Tiers:"
        echo "  1       - Init (core prelude)"
        echo "  2       - Std (standard library)"
        echo "  3       - Lean (compiler infrastructure)"
        echo "  4       - Batteries.Data"
        echo "  5       - Batteries.Tactic"
        echo "  6       - Mathlib.Data"
        echo "  7       - Mathlib.Algebra"
        echo "  8       - Mathlib.Analysis"
        echo "  9       - Mathlib.CategoryTheory"
        echo "  10      - Mathlib.Advanced"
        echo ""
        echo "Shortcuts:"
        echo "  init      - Tiers 1-3 (Lean core only)"
        echo "  batteries - Tiers 4-5 (Batteries only)"
        echo "  mathlib   - Tiers 6-10 (Mathlib only)"
        echo "  all       - All tiers"
        exit 1
        ;;
esac

echo ""
echo "=== Export complete ==="
echo "Exports are in: $EXPORT_DIR"
ls -la "$EXPORT_DIR"/*/
