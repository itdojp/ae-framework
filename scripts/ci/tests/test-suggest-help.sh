#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

out=$(bash scripts/ci/echo-to-printf-suggest.sh --help)
printf '%s\n' "$out"

if ! printf '%s' "$out" | grep -q '^Usage:'; then
  echo "suggest tool --help did not print Usage header" >&2
  exit 1
fi

echo "[test] Suggest tool help test passed."

