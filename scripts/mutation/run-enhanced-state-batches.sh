#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
batch_dir="$repo_root/mutation/batches"
mutate_file="$batch_dir/enhanced-state-manager.txt"

mkdir -p "$batch_dir"

if [[ ! -f "$mutate_file" ]]; then
  cat <<'PATTERNS' > "$mutate_file"
src/utils/enhanced-state-manager.ts
PATTERNS
fi

quick_flag=${1-}
shift_args=()
if [[ "${quick_flag-}" == "--quick" ]]; then
  shift_args+=(--quick)
fi

while IFS= read -r pattern; do
  [[ -z "$pattern" ]] && continue
  echo "Running mutation batch for $pattern"
  scripts/mutation/run-scoped.sh "${shift_args[@]}" --mutate "$pattern"
done < "$mutate_file"
