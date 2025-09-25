#!/usr/bin/env bash
set -euo pipefail

# Guard 1: forbid using echo >> $GITHUB_OUTPUT or $GITHUB_ENV in workflows
# Guard 2: require quoting for target files (>> "$GITHUB_OUTPUT" / >> "$GITHUB_ENV")

cd "$(git rev-parse --show-toplevel)" || exit 1

# Allow disabling the guard in rare cases (debug), default is enabled
if [ "${PRINTF_GUARD_DISABLE:-0}" = "1" ]; then
  echo "(info) printf guard disabled via PRINTF_GUARD_DISABLE=1" >&2
  exit 0
fi

# Optional target directory (default: .github/workflows)
TARGET_DIR="${1:-.github/workflows}"
if [ ! -d "$TARGET_DIR" ]; then
  echo "⚠️  Target directory not found: $TARGET_DIR (nothing to check)" >&2
  exit 0
fi

pattern='\becho\b[^\n>]*>>[^\n$]*\$(GITHUB_OUTPUT|GITHUB_ENV)'

tmp_echo="/tmp/_echo_offenders.$$"
# Predeclare tmp vars to avoid set -u issues in EXIT trap before assignment
unquoted_tmp=""
non_printf_tmp=""
# Clean up any temp files created by this guard
trap 'rm -f "$tmp_echo" ${unquoted_tmp:+"$unquoted_tmp"} ${non_printf_tmp:+"$non_printf_tmp"}' EXIT

if command -v rg >/dev/null 2>&1; then
  rg -n -S "$pattern" "$TARGET_DIR" \
    | awk 'BEGIN{FS=":"} { line=$0; sub(/^[[:space:]]+/,"",$3); if ($3 ~ /^#/) next; print line }' \
    >"$tmp_echo" || true
else
  grep -REn "$pattern" "$TARGET_DIR" \
    | awk 'BEGIN{FS=":"} { line=$0; sub(/^[[:space:]]+/,"",$3); if ($3 ~ /^#/) next; print line }' \
    >"$tmp_echo" || true
fi

if [ -s "$tmp_echo" ]; then
  echo "🚫 Found forbidden echo >> \$GITHUB_OUTPUT/\$GITHUB_ENV usage in workflows:" >&2
  cat "$tmp_echo" >&2 || true
  echo "\nFix: replace with printf, e.g.: printf \"%s\\n\" \"key=value\" >> \"\$GITHUB_OUTPUT\"" >&2
  # GitHub annotations for easier review
  while IFS=":" read -r f l _; do
    if [ -n "${f:-}" ] && [ -n "${l:-}" ]; then
      printf '::error file=%s,line=%s::Use printf with quoted target (no echo)\n' "$f" "$l"
    fi
  done < "$tmp_echo"
  exit 1
fi

echo "✅ No forbidden echo redirections to GITHUB_OUTPUT/ENV detected."

# Check for unquoted target redirections (require >> "$GITHUB_OUTPUT" / >> "$GITHUB_ENV")
unquoted_tmp="/tmp/_unquoted_offenders.$$"

if command -v rg >/dev/null 2>&1; then
  # PCRE negative lookahead to detect unquoted targets; allow ${GITHUB_*} as well
  if rg -P -n -S '>>\s*(?!"\$\{?GITHUB_(OUTPUT|ENV)\}?")\$\{?GITHUB_(OUTPUT|ENV)\}?"?' "$TARGET_DIR" \
    | awk 'BEGIN{FS=":"} { line=$0; sub(/^[[:space:]]+/,"",$3); if ($3 ~ /^#/) next; print line }' \
    >"$unquoted_tmp"; then
    echo "🚫 Found unquoted redirection target to \$GITHUB_OUTPUT/\$GITHUB_ENV (quote the variable):" >&2
    cat "$unquoted_tmp" >&2 || true
    echo "\nFix: use >> \"\$GITHUB_OUTPUT\" (or \"\$GITHUB_ENV\")." >&2
    while IFS=":" read -r f l _; do
      if [ -n "${f:-}" ] && [ -n "${l:-}" ]; then
        printf '::error file=%s,line=%s::Quote $GITHUB_OUTPUT/$GITHUB_ENV in redirection\n' "$f" "$l"
      fi
    done < "$unquoted_tmp"
    exit 1
  fi
else
  # Fallback heuristic: lines with >> $GITHUB_* minus quoted ones
  grep -REn '>>\s*\$\{?GITHUB_(OUTPUT|ENV)\}?"?' "$TARGET_DIR" \
    | awk 'BEGIN{FS=":"} { line=$0; sub(/^[[:space:]]+/,"",$3); if ($3 ~ /^#/) next; print line }' \
    >"$unquoted_tmp" || true
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
      while IFS=":" read -r f l _; do
        if [ -n "${f:-}" ] && [ -n "${l:-}" ]; then
          printf '::error file=%s,line=%s::Quote $GITHUB_OUTPUT/$GITHUB_ENV in redirection\n' "$f" "$l"
        fi
      done <<< "$offenders"
      exit 1
    fi
  fi
fi

echo "✅ All GITHUB_OUTPUT/ENV appends are quoted and use printf."

# Enforce printf usage specifically (no other commands appending to targets)
non_printf_tmp="/tmp/_non_printf_offenders.$$"
if command -v rg >/dev/null 2>&1; then
  # Match any line appending to quoted targets that does not include 'printf'
  rg -n -S '>>\s*"\$\{?GITHUB_(OUTPUT|ENV)\}?"' "$TARGET_DIR" \
    | rg -v 'printf' \
    | rg -v '\}\s*>>\s*"\$GITHUB_(OUTPUT|ENV)"' >"$non_printf_tmp" || true
else
  grep -REn '>>\s*"\$\{?GITHUB_(OUTPUT|ENV)\}?"' "$TARGET_DIR" \
    | grep -v 'printf' \
    | grep -Ev '\}\s*>>\s*"\$GITHUB_(OUTPUT|ENV)"' >"$non_printf_tmp" || true
fi

if [ -s "$non_printf_tmp" ]; then
  echo "🚫 Found non-printf appends to \$GITHUB_OUTPUT/\$GITHUB_ENV. Policy requires printf." >&2
  cat "$non_printf_tmp" >&2 || true
  echo "\nFix: use printf, e.g.: printf \"%s\\n\" \"key=value\" >> \"\$GITHUB_OUTPUT\"" >&2
  while IFS=":" read -r f l _; do
    if [ -n "${f:-}" ] && [ -n "${l:-}" ]; then
      printf '::error file=%s,line=%s::Use printf for appends to special files\n' "$f" "$l"
    fi
  done < "$non_printf_tmp"
  exit 1
fi

echo "✅ All appends to GITHUB_OUTPUT/ENV use printf with proper quoting."

# Forbid tee -a to GITHUB_OUTPUT/ENV
tee_tmp="/tmp/_tee_offenders.$$"
if command -v rg >/dev/null 2>&1; then
  rg -n -S 'tee\s+-a\s+"?\$\{?GITHUB_(OUTPUT|ENV)\}?"?' "$TARGET_DIR" \
    | awk 'BEGIN{FS=":"} { line=$0; sub(/^[[:space:]]+/,"",$3); if ($3 ~ /^#/) next; print line }' \
    >"$tee_tmp" || true
else
  grep -REn 'tee\s+-a\s+"?\$\{?GITHUB_(OUTPUT|ENV)\}?"?' "$TARGET_DIR" \
    | awk 'BEGIN{FS=":"} { line=$0; sub(/^[[:space:]]+/,"",$3); if ($3 ~ /^#/) next; print line }' \
    >"$tee_tmp" || true
fi

if [ -s "$tee_tmp" ]; then
  echo "🚫 Using tee -a to append to \$GITHUB_OUTPUT/\$GITHUB_ENV is not allowed (use printf)." >&2
  cat "$tee_tmp" >&2 || true
  while IFS=":" read -r f l _; do
    if [ -n "${f:-}" ] && [ -n "${l:-}" ]; then
      printf '::error file=%s,line=%s::Do not use tee -a for appends; use printf\n' "$f" "$l"
    fi
  done < "$tee_tmp"
  exit 1
fi

# Forbid deprecated ::set-output command
setout_tmp="/tmp/_setoutput_offenders.$$"
if command -v rg >/dev/null 2>&1; then
  rg -n -S '::set-output\s+name=' "$TARGET_DIR" \
    | awk 'BEGIN{FS=":"} { line=$0; sub(/^[[:space:]]+/,"",$3); if ($3 ~ /^#/) next; print line }' \
    >"$setout_tmp" || true
else
  grep -REn '::set-output\s+name=' "$TARGET_DIR" \
    | awk 'BEGIN{FS=":"} { line=$0; sub(/^[[:space:]]+/,"",$3); if ($3 ~ /^#/) next; print line }' \
    >"$setout_tmp" || true
fi

if [ -s "$setout_tmp" ]; then
  echo "🚫 Deprecated ::set-output usage detected. Use \"printf >> \$GITHUB_OUTPUT\" instead." >&2
  cat "$setout_tmp" >&2 || true
  while IFS=":" read -r f l _; do
    if [ -n "${f:-}" ] && [ -n "${l:-}" ]; then
      printf '::error file=%s,line=%s::Deprecated ::set-output; use printf >> $GITHUB_OUTPUT\n' "$f" "$l"
    fi
  done < "$setout_tmp"
  exit 1
fi
