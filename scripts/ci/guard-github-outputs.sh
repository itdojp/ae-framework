#!/usr/bin/env bash
set -euo pipefail

# Guard 1: forbid using echo >> $GITHUB_OUTPUT or $GITHUB_ENV in workflows
# Guard 2: require quoting for target files (>> "$GITHUB_OUTPUT" / >> "$GITHUB_ENV")

cd "$(git rev-parse --show-toplevel)" || exit 1

pattern='\becho\b[^\n>]*>>[^\n$]*\$(GITHUB_OUTPUT|GITHUB_ENV)'

tmp_echo="/tmp/_echo_offenders.$$"
trap 'rm -f "$tmp_echo" "$unquoted_tmp"' EXIT

if command -v rg >/dev/null 2>&1; then
  rg -n -S "$pattern" .github/workflows >"$tmp_echo" || true
else
  grep -REn "$pattern" .github/workflows >"$tmp_echo" || true
fi

if [ -s "$tmp_echo" ]; then
  echo "🚫 Found forbidden echo >> \$GITHUB_OUTPUT/\$GITHUB_ENV usage in workflows:" >&2
  cat "$tmp_echo" >&2 || true
  echo "\nFix: replace with printf, e.g.: printf \"%s\\n\" \"key=value\" >> \"\$GITHUB_OUTPUT\"" >&2
  exit 1
fi

echo "✅ No forbidden echo redirections to GITHUB_OUTPUT/ENV detected."

# Check for unquoted target redirections (require >> "$GITHUB_OUTPUT" / >> "$GITHUB_ENV")
unquoted_tmp="/tmp/_unquoted_offenders.$$"

if command -v rg >/dev/null 2>&1; then
  # PCRE negative lookahead to detect unquoted targets
  if rg -P -n -S '>>\s*(?!"\$GITHUB_(OUTPUT|ENV)")\$GITHUB_(OUTPUT|ENV)' .github/workflows >"$unquoted_tmp"; then
    echo "🚫 Found unquoted redirection target to \$GITHUB_OUTPUT/\$GITHUB_ENV (quote the variable):" >&2
    cat "$unquoted_tmp" >&2 || true
    echo "\nFix: use >> \"\$GITHUB_OUTPUT\" (or \"\$GITHUB_ENV\")." >&2
    exit 1
  fi
else
  # Fallback heuristic: lines with >> $GITHUB_* minus quoted ones
  grep -REn '>>\s*\$GITHUB_(OUTPUT|ENV)' .github/workflows >"$unquoted_tmp" || true
  if [ -s "$unquoted_tmp" ]; then
    if grep -REn '>>\s*"\$GITHUB_(OUTPUT|ENV)"' .github/workflows >/dev/null; then
      offenders=$(grep -REn '>>\s*\$GITHUB_(OUTPUT|ENV)' .github/workflows | grep -v '>>\s*"\$GITHUB_')
    else
      offenders=$(cat "$unquoted_tmp")
    fi
    if [ -n "$offenders" ]; then
      echo "🚫 Found unquoted redirection target to \$GITHUB_OUTPUT/\$GITHUB_ENV (quote the variable):" >&2
      echo "$offenders" >&2
      echo "\nFix: use >> \"\$GITHUB_OUTPUT\" (or \"\$GITHUB_ENV\")." >&2
      exit 1
    fi
  fi
fi

echo "✅ All GITHUB_OUTPUT/ENV appends are quoted and use printf."

