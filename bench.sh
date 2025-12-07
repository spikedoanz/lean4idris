#!/bin/bash
set -e
SECONDS=0
for f in ~/.cache/lean4exports/tier01-init/*.export; do
  name=$(basename "$f")
  echo "tier01-init/$name:"
  echo "./build/exec/lean4idris --no-cache "$f" 2>&1 | tee /tmp/"$name.log" | grep "^TOTAL" || echo "FAILED""
  timeout 120 ./build/exec/lean4idris --no-cache "$f" 2>&1 | tee /tmp/"$name.log" | grep "^TOTAL" || echo "FAILED"
done
cached=$SECONDS
echo "=== TOTAL: ${cached}s ==="
