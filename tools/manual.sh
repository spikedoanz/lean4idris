#!/bin/bash
set -e
for f in ~/.cache/lean4exports/tier01-init/*.export; do
  name=$(basename "$f")
  echo "time ./build/exec/lean4idris "$f" -v | tee /tmp/"$name.log""
done
