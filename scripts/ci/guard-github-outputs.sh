#!/usr/bin/env bash
set -euo pipefail

# Guard: forbid using echo >> $GITHUB_OUTPUT or $GITHUB_ENV in workflows
# Policy: use printf and quote the target file (>> "$GITHUB_OUTPUT" / >> "$GITHUB_ENV").

cd "$(git rev-parse --show-toplevel)" || exit 1

pattern='\becho\b[^\n>]*>>[^\n$]*\$(GITHUB_OUTPUT|GITHUB_ENV)'

if rg -n "$pattern" .github/workflows -S >/tmp/_echo_offenders.txt; then
  echo "🚫 Found forbidden echo >> \$GITHUB_OUTPUT/\$GITHUB_ENV usage in workflows:" >&2
  cat /tmp/_echo_offenders.txt >&2 || true
  echo "\nFix: replace with printf, e.g.: printf \"%s\\n\" \"key=value\" >> \"\$GITHUB_OUTPUT\"" >&2
  exit 1
else
  echo "✅ No forbidden echo redirections to GITHUB_OUTPUT/ENV detected."
fi
