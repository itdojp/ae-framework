#!/usr/bin/env bash
set -euo pipefail

# Run printf/quoting guard first
pnpm -s ci:guard:github-outputs

# Then run actionlint (Docker-based) if available
if command -v docker >/dev/null 2>&1; then
  if docker version >/dev/null 2>&1; then
    # Do not fail local run if actionlint via docker is unavailable for any reason
    bash scripts/ci/actionlint.sh || printf "%s\n" "(info) Local actionlint failed or unavailable; CI will run rhysd/actionlint@v1.7.1."
  else
    printf "%s\n" "(info) Docker is present but not usable; skipping local actionlint. CI will run rhysd/actionlint@v1.7.1."
  fi
else
  printf "%s\n" "(info) Docker not available; skipping local actionlint. CI will run rhysd/actionlint@v1.7.1."
fi
