#!/usr/bin/env bash
set -euo pipefail

BASE_REF="$1"
QUICK_FLAG="$2"
EXTRA_ARGS_RAW="$3"

ensure_base_ref() {
  local ref=$1
  if git rev-parse --verify "${ref}^{commit}" >/dev/null 2>&1; then
    return 0
  fi

  # Try fetching the ref as provided (covers cases like origin/main or main)
  if git fetch --no-tags --depth=1 origin "$ref" >/dev/null 2>&1; then
    return 0
  fi

  # Fallback: if the ref includes a remote prefix (origin/foo) fetch only the branch name
  local trimmed="${ref#origin/}"
  git fetch --no-tags --depth=1 origin "$trimmed" >/dev/null 2>&1 || git fetch origin "$trimmed" >/dev/null 2>&1
}

ensure_base_ref "$BASE_REF"

CMD=("./scripts/mutation/run-scoped.sh")

if [[ "$QUICK_FLAG" == "true" ]]; then
  CMD+=("--quick")
fi

CMD+=("--auto-diff=$BASE_REF")

if [[ -n "$EXTRA_ARGS_RAW" ]]; then
  while IFS= read -r token; do
    token=$(echo "$token" | xargs)
    [[ -z "$token" ]] && continue
    CMD+=("$token")
  done <<< "$EXTRA_ARGS_RAW"
fi

"${CMD[@]}"

if ! node scripts/mutation/print-summary.mjs > mutation-summary.txt; then
  echo "ERROR: Failed to generate mutation-summary.txt. Ensure mutation.json exists and print-summary.mjs succeeds." >&2
  exit 1
fi

while IFS='=' read -r key value; do
  sanitized_key=${key//-/_}
  echo "${sanitized_key}=${value}" >> "$GITHUB_OUTPUT"
done < mutation-summary.txt

echo "summary_path=mutation-summary.txt" >> "$GITHUB_OUTPUT"
if [[ -d reports/mutation ]]; then
  echo "report_path=reports/mutation" >> "$GITHUB_OUTPUT"
else
  echo "report_path=" >> "$GITHUB_OUTPUT"
fi

cat mutation-summary.txt

if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  {
    echo '### Mutation Summary'
    while IFS='=' read -r key value; do
      echo "- ${key}: ${value}"
    done < mutation-summary.txt
  } >> "$GITHUB_STEP_SUMMARY"
fi
