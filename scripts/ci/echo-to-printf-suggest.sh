#!/usr/bin/env bash
set -euo pipefail

# Suggest conversions from echo >> $GITHUB_OUTPUT/$GITHUB_ENV to policy-compliant printf

ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

TARGET_DIR="${1:-.github/workflows}"
if [ ! -d "$TARGET_DIR" ]; then
  echo "(info) target dir not found: $TARGET_DIR" >&2
  exit 0
fi

# Match echo ... >> $GITHUB_OUTPUT / $GITHUB_ENV (PCRE)
pattern_pcre='echo\s+.*>>\s*\$\{?GITHUB_(OUTPUT|ENV)\}?'

tmp="/tmp/_echo_suggest.$$"
trap 'rm -f "$tmp"' EXIT

if command -v rg >/dev/null 2>&1; then
  rg -n -P -S -g "*.yml" -g "*.yaml" "$pattern_pcre" "$TARGET_DIR" >"$tmp" || true
else
  grep -REn -E --include "*.yml" --include "*.yaml" "$pattern_pcre" "$TARGET_DIR" >"$tmp" || true
fi

if [ ! -s "$tmp" ]; then
  echo "(info) no echo offenders found under $TARGET_DIR" >&2
  exit 0
fi

echo "::group::echo -> printf suggestions (dry-run)"
while IFS= read -r line; do
  file=${line%%:*}
  rest=${line#*:}
  lineno=${rest%%:*}
  content=${line#*:*:}
  target="GITHUB_OUTPUT"
  if echo "$content" | grep -q '\$GITHUB_ENV'; then target="GITHUB_ENV"; fi

  # Try to capture a simple quoted payload echo "..." >> $GITHUB_*
  payload=$(echo "$content" | sed -n "s/^.*echo[[:space:]]\+\(['\"]\)\(.*\)\1[[:space:]]*>>.*$/\2/p")
  if [ -n "$payload" ]; then
    printf 'file:%s line:%s\n  before: %s\n  after:  printf "%%s\\n" "%s" >> "$%s"\n' "$file" "$lineno" "$content" "$payload" "$target"
  else
    printf 'file:%s line:%s\n  before: %s\n  note:   convert to printf "%%s\\n" "key=value" >> "$%s" (see docs/ci/echo-to-printf-recipes.md)\n' "$file" "$lineno" "$content" "$target"
  fi
done < "$tmp"
echo "::endgroup::"
