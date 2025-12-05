#!/bin/bash
# Run Claude Code in a sandboxed Docker container
# Mount current directory as /workspace

docker run -it --rm \
  -v "$(pwd):/workspace" \
  -e ANTHROPIC_API_KEY \
  claude-sandbox "$@"
