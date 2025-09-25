#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

mkdir -p "$TMPDIR/wf"
cat > "$TMPDIR/wf/comments.yml" << 'YAML'
name: comments
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          # echo key=value >> $GITHUB_OUTPUT
          # echo "key=value" >> $GITHUB_ENV
YAML

out=$(bash scripts/ci/echo-to-printf-suggest.sh "$TMPDIR/wf" || true)
echo "$out"

if printf '%s' "$out" | grep -qi 'after:'; then
  echo "suggest tool should ignore commented lines, but produced suggestions" >&2
  exit 1
fi

echo "[test] Suggest tool comments-only test passed."

