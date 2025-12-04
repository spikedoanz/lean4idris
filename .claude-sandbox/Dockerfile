FROM node:22-bookworm

# Install Claude Code globally
RUN npm install -g @anthropic-ai/claude-code

# Create non-root user
RUN useradd -m -s /bin/bash claude

# Set up workspace
WORKDIR /workspace
RUN chown claude:claude /workspace

USER claude

ENTRYPOINT ["claude"]
