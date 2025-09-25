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
          printf "%s\n" "also_good=true" >> "${GITHUB_OUTPUT}"
          # Multi-line output using delimiter via printf lines
          printf "%s\n" "multi<<EOF" >> "$GITHUB_OUTPUT"
          printf "%s\n" "line1" >> "$GITHUB_OUTPUT"
          printf "%s\n" "line2" >> "$GITHUB_OUTPUT"
          printf "%s\n" "EOF" >> "$GITHUB_OUTPUT"
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

# Deprecated set-output offender
cat > "$TMPDIR/wf/offender4.yml" << 'YAML'
name: off4
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          echo "::set-output name=val::deprecated"
YAML

echo "[test] Expect guard to fail on ::set-output offender..."
if bash scripts/ci/guard-github-outputs.sh "$TMPDIR/wf"; then
  echo "Guard did not fail on ::set-output offender (unexpected)" >&2
  exit 1
fi

rm -f "$TMPDIR/wf/offender4.yml"

# Offender: printf without trailing newline
cat > "$TMPDIR/wf/offender5.yml" << 'YAML'
name: off5
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          printf "%s" "NO_NL=true" >> "$GITHUB_OUTPUT"
YAML

echo "[test] Expect guard to fail on printf without newline offender..."
if bash scripts/ci/guard-github-outputs.sh "$TMPDIR/wf"; then
  echo "Guard did not fail on printf without newline offender (unexpected)" >&2
  exit 1
fi

rm -f "$TMPDIR/wf/offender5.yml"

# Comments should be ignored
cat > "$TMPDIR/wf/comments.yml" << 'YAML'
name: comments
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          # echo "bad=true" >> $GITHUB_OUTPUT
          # printf "%s" "NO_NL=true" >> "$GITHUB_OUTPUT"
          # echo "::set-output name=val::deprecated"
          # echo "three=3" | tee -a "$GITHUB_OUTPUT"
          printf "%s\n" "ok=true" >> "$GITHUB_OUTPUT"
YAML

echo "[test] Expect guard to pass when offenders are only in comments..."
bash scripts/ci/guard-github-outputs.sh "$TMPDIR/wf"

# Offender: here-doc append (cat <<EOF >> "$GITHUB_OUTPUT")
cat > "$TMPDIR/wf/offender6.yml" << 'YAML'
name: off6
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          cat > /tmp/x <<EOF
          key=value
          EOF
          cat /tmp/x >> "$GITHUB_OUTPUT"
YAML

echo "[test] Expect guard to fail on here-doc/cat append offender..."
if bash scripts/ci/guard-github-outputs.sh "$TMPDIR/wf"; then
  echo "Guard did not fail on here-doc append offender (unexpected)" >&2
  exit 1
fi

rm -f "$TMPDIR/wf/offender6.yml"
echo "[test] Guard basic tests passed."

# Offender: single > overwrite to GITHUB_OUTPUT
cat > "$TMPDIR/wf/offender7.yml" << 'YAML'
name: off7
on: push
jobs:
  t:
    runs-on: ubuntu-latest
    steps:
      - run: |
          echo "overwrite=true" > "$GITHUB_OUTPUT"
YAML

echo "[test] Expect guard to fail on overwrite (single >) offender..."
if bash scripts/ci/guard-github-outputs.sh "$TMPDIR/wf"; then
  echo "Guard did not fail on overwrite offender (unexpected)" >&2
  exit 1
fi
