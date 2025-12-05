#!/bin/bash
set -e

cd /Users/spike/R/lean4idris-cache
rm -rf ~/.cache/lean4idris

echo "=== BASELINE: No cache, checking all tier01-init files ==="
echo ""

SECONDS=0
for f in /Users/spike/R/lean4idris/test/exports/tier01-init/*.export; do
  name=$(basename "$f")
  echo -n "$name: "
  pack run lean4idris --no-cache -f 10000 "$f" 2>&1 | grep "^TOTAL" || echo "FAILED"
done
baseline=$SECONDS

echo ""
echo "=== BASELINE TOTAL: ${baseline}s ==="
echo ""
echo ""

rm -rf ~/.cache/lean4idris

echo "=== WITH CACHE: checking all tier01-init files ==="
echo ""

SECONDS=0
for f in /Users/spike/R/lean4idris/test/exports/tier01-init/*.export; do
  name=$(basename "$f")
  echo -n "$name: "
  pack run lean4idris -f 10000 "$f" 2>&1 | grep "^TOTAL" || echo "FAILED"
done
cached=$SECONDS

echo ""
echo "=== WITH CACHE TOTAL: ${cached}s ==="
echo ""
echo "=== SPEEDUP: baseline=${baseline}s, cached=${cached}s ==="
