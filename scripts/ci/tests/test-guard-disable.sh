#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

mkdir -p "$TMPDIR/empty"

echo "[test] Guard should skip when disabled via env..."
out=$(PRINTF_GUARD_DISABLE=1 bash scripts/ci/guard-github-outputs.sh "$TMPDIR/empty" 2>&1 || true)
printf '%s\n' "$out"
if ! printf '%s' "$out" | grep -q 'printf guard disabled'; then
  echo "guard did not report disabled state" >&2
  exit 1
fi

echo "[test] Guard disable test passed."

