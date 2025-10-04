#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

PREVIEW_DIR="hermetic-reports/spec"
mkdir -p "$PREVIEW_DIR"

# Clean previous preview artifacts
rm -f "$PREVIEW_DIR"/generate-artifacts-diff.json

# Run Codex quickstart with tolerant flags so generation never fails hard.
CODEX_SKIP_QUALITY="1" CODEX_TOLERANT="1" pnpm run codex:quickstart >/dev/null

# Summarise changes under the generation targets.
node scripts/ci/report-generated-artifacts.mjs > "$PREVIEW_DIR"/generate-artifacts-diff.json

printf "generation preview written: %s\n" "$PREVIEW_DIR/generate-artifacts-diff.json"
