#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

TMPDIR="$(mktemp -d)"
cleanup() { rm -rf "$TMPDIR"; }
trap cleanup EXIT

mkdir -p "$TMPDIR/wf"

# Offender cases: echo to $GITHUB_OUTPUT; unquoted target with printf to $GITHUB_ENV
cat > "$TMPDIR/wf/offender.yml" << 'YAML'
name: off
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          echo "bad=true" >> $GITHUB_OUTPUT
          printf "%s\n" "NAME=bad" >> $GITHUB_ENV
YAML

# Allowed cases: printf + quoted, grouped, ${GITHUB_ENV} form
cat > "$TMPDIR/wf/ok.yml" << 'YAML'
name: ok
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          printf "%s\n" "good=true" >> "$GITHUB_OUTPUT"
          {
            printf "%s\n" "one=1"
            printf "%s\n" "two=2"
          } >> "$GITHUB_OUTPUT"
          printf "%s\n" "NAME=good" >> "${GITHUB_ENV}"
YAML

echo "[test] Expect guard to fail on offender..."
if bash scripts/ci/guard-github-outputs.sh "$TMPDIR/wf"; then
  echo "Guard did not fail on offender (unexpected)" >&2
  exit 1
fi

# Additional offender: unquoted printf to ${GITHUB_OUTPUT}
cat > "$TMPDIR/wf/offender2.yml" << 'YAML'
name: off2
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          printf "%s\n" "BAD=true" >> ${GITHUB_OUTPUT}
YAML

echo "[test] Expect guard to fail on unquoted \${GITHUB_OUTPUT} offender..."
if bash scripts/ci/guard-github-outputs.sh "$TMPDIR/wf"; then
  echo "Guard did not fail on unquoted ${GITHUB_OUTPUT} offender (unexpected)" >&2
  exit 1
fi

echo "[test] Expect guard to pass on allowed cases..."
rm -f "$TMPDIR/wf/offender.yml" "$TMPDIR/wf/offender2.yml"

# Additional offender: tee -a to $GITHUB_OUTPUT
cat > "$TMPDIR/wf/offender3.yml" << 'YAML'
name: off3
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          echo "three=3" | tee -a "$GITHUB_OUTPUT"
YAML

echo "[test] Expect guard to fail on tee -a offender..."
if bash scripts/ci/guard-github-outputs.sh "$TMPDIR/wf"; then
  echo "Guard did not fail on tee -a offender (unexpected)" >&2
  exit 1
fi

rm -f "$TMPDIR/wf/offender3.yml"
bash scripts/ci/guard-github-outputs.sh "$TMPDIR/wf"
echo "[test] Guard basic tests passed."
