#!/bin/bash
# Export Lean modules to the lean4export format for testing lean4idris
#
# Usage: ./tools/export-mathlib.sh [tier]
#   tier: 1-6 or "all" (default: all)
#
# Prerequisites:
#   - lake (Lean build tool) must be installed
#   - elan (Lean version manager) recommended
#
# This script will:
#   1. Set up a Mathlib project with lean4export as dependency
#   2. Build Mathlib (downloads prebuilt cache via lake exe cache get)
#   3. Export specified modules to test/exports/

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
EXPORTER_DIR="$REPO_ROOT/tools/mathlib-exporter"
EXPORT_DIR="$REPO_ROOT/test/exports"

TIER="${1:-all}"

# Module lists by tier
TIER1_MODULES=(
    "Init.Core"
    "Init.Prelude"
    "Init.Data.Nat.Basic"
    "Init.Data.List.Basic"
    "Init.Data.Bool.Basic"
    "Init.Data.String.Basic"
)

TIER2_MODULES=(
    "Mathlib.Data.Nat.Basic"
    "Mathlib.Data.Nat.Prime.Basic"
    "Mathlib.Data.Int.Basic"
    "Mathlib.Data.List.Basic"
    "Mathlib.Data.Fin.Basic"
    "Mathlib.Data.Option.Basic"
    "Mathlib.Data.Bool.Basic"
    "Mathlib.Logic.Basic"
    "Mathlib.Init.Set"
)

TIER3_MODULES=(
    "Mathlib.Algebra.Group.Basic"
    "Mathlib.Algebra.Group.Defs"
    "Mathlib.Algebra.Ring.Basic"
    "Mathlib.Algebra.Field.Basic"
    "Mathlib.Algebra.Order.Monoid.Basic"
    "Mathlib.GroupTheory.Subgroup.Basic"
)

TIER4_MODULES=(
    "Mathlib.Topology.Basic"
    "Mathlib.Topology.Order"
    "Mathlib.Analysis.Normed.Field.Basic"
    "Mathlib.Order.Filter.Basic"
)

TIER5_MODULES=(
    "Mathlib.CategoryTheory.Category.Basic"
    "Mathlib.CategoryTheory.Functor.Basic"
    "Mathlib.CategoryTheory.NatTrans"
    "Mathlib.CategoryTheory.Yoneda"
)

TIER6_MODULES=(
    "Mathlib.Data.Tree.Basic"           # Mutual inductives
    "Mathlib.Data.W.Basic"              # Nested inductives
    "Mathlib.SetTheory.Ordinal.Basic"   # Heavy universe polymorphism
    "Mathlib.GroupTheory.QuotientGroup.Basic"  # Quotient types
)

echo "=== Lean4Idris Mathlib Exporter ==="
echo "Repository root: $REPO_ROOT"
echo "Exporter dir: $EXPORTER_DIR"
echo "Export dir: $EXPORT_DIR"
echo ""

# Create directories
mkdir -p "$EXPORT_DIR"/{tier1-core,tier2-simple-mathlib,tier3-algebraic,tier4-analysis,tier5-category,tier6-adversarial}

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
    # lean4export is built in the packages subdirectory
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
    echo "=== Exporting Tier $tier_num ==="
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
        export_tier 1 "tier1-core" "${TIER1_MODULES[@]}"
        ;;
    2)
        export_tier 2 "tier2-simple-mathlib" "${TIER2_MODULES[@]}"
        ;;
    3)
        export_tier 3 "tier3-algebraic" "${TIER3_MODULES[@]}"
        ;;
    4)
        export_tier 4 "tier4-analysis" "${TIER4_MODULES[@]}"
        ;;
    5)
        export_tier 5 "tier5-category" "${TIER5_MODULES[@]}"
        ;;
    6)
        export_tier 6 "tier6-adversarial" "${TIER6_MODULES[@]}"
        ;;
    all)
        export_tier 1 "tier1-core" "${TIER1_MODULES[@]}"
        export_tier 2 "tier2-simple-mathlib" "${TIER2_MODULES[@]}"
        export_tier 3 "tier3-algebraic" "${TIER3_MODULES[@]}"
        export_tier 4 "tier4-analysis" "${TIER4_MODULES[@]}"
        export_tier 5 "tier5-category" "${TIER5_MODULES[@]}"
        export_tier 6 "tier6-adversarial" "${TIER6_MODULES[@]}"
        ;;
    *)
        echo "Unknown tier: $TIER"
        echo "Usage: $0 [1|2|3|4|5|6|all]"
        exit 1
        ;;
esac

echo ""
echo "=== Export complete ==="
echo "Exports are in: $EXPORT_DIR"
ls -la "$EXPORT_DIR"/*/
