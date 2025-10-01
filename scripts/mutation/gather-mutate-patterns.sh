#!/usr/bin/env bash
# Generate Stryker mutate glob patterns from git diff output.

set -euo pipefail

BASE_REF="origin/main"
OUTPUT=""
INCLUDE_PATTERNS=()
SILENT=false

usage() {
  cat <<'USAGE'
Usage: gather-mutate-patterns.sh [base_ref] [options]

Options:
  --output <path>   Write patterns to file (default: stdout)
  --include <glob>  Append an explicit mutate glob (repeatable)
  --silent          Suppress informational stderr output
  -h, --help        Show this help message
USAGE
}

while [[ ${1-} ]]; do
  case "$1" in
    --output)
      shift
      [[ ${1-} ]] || { echo "--output requires a path" >&2; exit 1; }
      OUTPUT="$1"
      shift
      ;;
    --include)
      shift
      [[ ${1-} ]] || { echo "--include requires a value" >&2; exit 1; }
      INCLUDE_PATTERNS+=("$1")
      shift
      ;;
    --silent)
      SILENT=true
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      break
      ;;
    *)
      BASE_REF="$1"
      shift
      ;;
  esac
done

MAP_FILE=$(mktemp)
trap 'rm -f "$MAP_FILE"' EXIT

if ! git rev-parse --verify "$BASE_REF" >/dev/null 2>&1; then
  echo "Base ref $BASE_REF is not available. Fetch it first." >&2
  exit 1
fi

git diff --name-only "$BASE_REF" > "$MAP_FILE"

patterns=()
while IFS= read -r file; do
  [[ -z "$file" ]] && continue
  case "$file" in
    src/api/*.ts|src/api/**/*.ts)
      patterns+=("${file}")
      ;;
    src/domain/*.ts|src/domain/**/*.ts)
      patterns+=("${file}")
      ;;
    src/utils/*.ts|src/utils/**/*.ts)
      patterns+=("${file}")
      ;;
    src/**/*.ts)
      patterns+=("${file}")
      ;;
    tests/unit/**/*.ts)
      src_file=$(echo "$file" | sed -E 's#^tests/unit/#src/#; s#([.]test|[.]spec)?\.ts$#.ts#')
      if [[ -f "$src_file" ]]; then
        patterns+=("${src_file}")
      fi
      ;;
    scripts/mutation/*.sh|stryker.config.*|stryker.conf.*)
      patterns+=("src/api/server.ts")
      ;;
  esac
done < "$MAP_FILE"

patterns+=("${INCLUDE_PATTERNS[@]}")

missing=false
if [[ ${#patterns[@]} -eq 0 ]]; then
  patterns+=("src/api/server.ts")
  missing=true
fi

unique=$(printf '%s\n' "${patterns[@]}" | sed '/^$/d' | sort -u)

if [[ -n "$OUTPUT" ]]; then
  printf '%s\n' "$unique" > "$OUTPUT"
  [[ "$SILENT" == true ]] || echo "Written mutate patterns to $OUTPUT"
else
  printf '%s\n' "$unique"
fi

if [[ "$missing" == true && "$SILENT" != true ]]; then
  echo "No TS changes detected; defaulted to src/api/server.ts" >&2
fi
