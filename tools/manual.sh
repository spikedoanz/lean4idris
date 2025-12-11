#!/bin/bash
set -e
for f in ~/.cache/lean4exports/tier01-init/*.export; do
  name=$(basename "$f")
  echo "{ time ./build/exec/lean4idris \"$f\" -v -f 100000 ; } 2>&1 | tee /tmp/\"$name.log\""
done
