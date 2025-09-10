#!/usr/bin/env bash
set -euo pipefail

FILE=${1:-}
if [ -z "$FILE" ] || [ ! -f "$FILE" ]; then
  echo "Usage: $0 path/to/issue.md" >&2
  exit 2
fi

# Derive repo owner/name from origin URL
ORIGIN=$(git remote get-url origin 2>/dev/null || echo "")
if [[ "$ORIGIN" =~ github.com[:/][^/]+/[^/]+ ]]; then
  OWNER=$(echo "$ORIGIN" | sed -E 's#.*github.com[:/]+([^/]+)/.*#\1#')
  NAME=$(basename "$ORIGIN" .git)
  REPO="$OWNER/$NAME"
else
  echo "Could not determine GitHub repo from 'origin'. Falling back to current directory repo context." >&2
  REPO=""
fi

# Extract first markdown H1 as title
TITLE=$(grep -m1 -E '^# ' "$FILE" | sed -E 's/^# +//')
if [ -z "$TITLE" ]; then
  TITLE="New Issue"
fi

set +e
if [ -n "$REPO" ]; then
  gh issue create -R "$REPO" -t "$TITLE" -F "$FILE"
else
  gh issue create -t "$TITLE" -F "$FILE"
fi
CODE=$?
set -e

if [ $CODE -ne 0 ]; then
  cat >&2 <<'EOS'
Failed to create the GitHub issue via gh CLI.

Troubleshooting:
  1) Authenticate:    gh auth login
  2) Verify repo:      git remote -v   # origin must be GitHub
  3) Retry:
     scripts/ci/create-issue-from-md.sh docs/proposals/ISSUE-openapi-and-jit-templates.md

Alternatively, create a new issue in the GitHub UI and paste the contents of the markdown file.
EOS
  exit $CODE
fi

echo "Issue created successfully."

