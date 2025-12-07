#!/bin/bash
set -e
for f in ~/.cache/lean4exports/tier01-init/*.export; do
  name=$(basename "$f")
  echo "./build/exec/lean4idris --no-cache "$f" | tee /tmp/"$name.log""
done
