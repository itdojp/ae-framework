#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

mkdir -p "$TMPDIR/wf"
cat > "$TMPDIR/wf/off.yml" << 'YAML'
name: off
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          echo "key=value" >> $GITHUB_OUTPUT
YAML

out=$(bash scripts/ci/echo-to-printf-suggest.sh "$TMPDIR/wf" || true)
echo "$out"

if ! printf '%s' "$out" | grep -q 'after:'; then
  echo "suggest tool did not print an after: suggestion" >&2
  exit 1
fi

echo "[test] Suggest tool basic test passed."

