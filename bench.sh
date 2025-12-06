#!/bin/bash
set -e
rm -rf ~/.cache/lean4idris
SECONDS=0
for f in ~/.cache/lean4exports/tier01-init/*.export; do
  name=$(basename "$f")
  echo -n "$name: "
  ./build/exec/lean4idris -f 1000 "$f" 2>&1 | grep "^TOTAL" || echo "FAILED"
done
cached=$SECONDS
echo "=== WITH CACHE TOTAL: ${cached}s ==="
