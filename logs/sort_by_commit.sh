#!/bin/bash
# Sort log directories by git commit order (most recent first)

cd "$(dirname "$0")/.." || exit 1

# Get all commit hashes in order (most recent first)
git log --format='%H' --all | while read -r hash; do
    if [ -d "logs/$hash" ]; then
        echo "$hash"
    fi
done
