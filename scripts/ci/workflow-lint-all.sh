#!/usr/bin/env bash
set -euo pipefail

# Run printf/quoting guard first
pnpm -s ci:guard:github-outputs

# Then run actionlint (Docker-based) if available
if command -v docker >/dev/null 2>&1; then
  bash scripts/ci/actionlint.sh
else
  printf "%s\n" "(info) Docker not available; skipping local actionlint. CI will run rhysd/actionlint@v1.7.1."
fi
EOF
chmod +x scripts/ci/workflow-lint-all.sh
