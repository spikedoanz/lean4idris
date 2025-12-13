#!/bin/bash
pack cleanbuild
COMMIT=$(git rev-parse HEAD) && mkdir -p logs/$COMMIT && ./tools/manual.sh | bash 2>&1 ; cp /tmp/*.export.log logs/$COMMIT/ ; ./logs/get_stats.sh logs/$COMMIT

