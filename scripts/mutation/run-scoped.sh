#!/usr/bin/env bash
set -euo pipefail
set -f

QUICK_MODE=false
CUSTOM_PATTERNS=()
CUSTOM_PATTERN_FILES=()
CONFIG_PATH=""
EXTRA_ARGS=()
AUTO_DIFF=false
AUTO_DIFF_REF="origin/main"
TEMP_FILES=()

cleanup() {
  local file
  for file in "${TEMP_FILES[@]}"; do
    [[ -n "$file" && -f "$file" ]] && rm -f "$file"
  done
}

trap cleanup EXIT

usage() {
  cat <<'USAGE'
Usage: run-scoped.sh [options] [-- additional-stryker-args]

Options:
  -q, --quick                Run quick mode (single-thread, short timeout)
  -m, --mutate <pattern>     Append a mutate glob pattern (repeatable)
      --mutate-file <path>   Read newline-separated patterns from file
      --auto-diff[=<ref>]    Generate mutate patterns from git diff (default: origin/main)
  -c, --config, --configFile <path>   Use a specific Stryker config file
  -h, --help                 Show this help message

Environment overrides:
  STRYKER_MUTATE, STRYKER_CONCURRENCY, STRYKER_TIMEOUT, STRYKER_TIME_LIMIT,
  STRYKER_CONFIG (fallback when --config/--configFile is not provided).
USAGE
}

while [[ ${1-} ]]; do
  case "$1" in
    -q|--quick)
      QUICK_MODE=true
      shift
      ;;
    -m|--mutate)
      shift
      [[ ${1-} ]] || { echo "--mutate requires a value" >&2; exit 1; }
      CUSTOM_PATTERNS+=("$1")
      shift
      ;;
    --mutate-file)
      shift
      [[ ${1-} ]] || { echo "--mutate-file requires a path" >&2; exit 1; }
      CUSTOM_PATTERN_FILES+=("$1")
      shift
      ;;
    --auto-diff)
      AUTO_DIFF=true
      if [[ ${2-} && ${2:0:1} != '-' ]]; then
        AUTO_DIFF_REF="$2"
        shift
      fi
      shift
      ;;
    --auto-diff=*)
      AUTO_DIFF=true
      AUTO_DIFF_REF="${1#--auto-diff=}"
      [[ -z "$AUTO_DIFF_REF" ]] && AUTO_DIFF_REF="origin/main"
      shift
      ;;
    -c|--config|--configFile)
      shift
      [[ ${1-} ]] || { echo "--config/-c/--configFile requires a path" >&2; exit 1; }
      CONFIG_PATH="$1"
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      EXTRA_ARGS+=("$@")
      break
      ;;
    *)
      EXTRA_ARGS+=("$1")
      shift
      ;;
  esac
done

if [[ "$AUTO_DIFF" == "true" ]]; then
  if [[ ! -x ./scripts/mutation/gather-mutate-patterns.sh ]]; then
    echo "gather-mutate-patterns.sh not found or not executable" >&2
    exit 1
  fi
  AUTO_DIFF_FILE=$(mktemp)
  TEMP_FILES+=("$AUTO_DIFF_FILE")
  ./scripts/mutation/gather-mutate-patterns.sh "$AUTO_DIFF_REF" --output "$AUTO_DIFF_FILE" --silent
  CUSTOM_PATTERN_FILES+=("$AUTO_DIFF_FILE")
fi

DEFAULT_PATTERNS=$'src/domain/**/*.ts
src/utils/enhanced-state-manager.ts
src/api/server.ts'
QUICK_PATTERNS=$'src/api/server.ts'

PATTERN_SOURCE=""
if [[ ${#CUSTOM_PATTERNS[@]} -gt 0 || ${#CUSTOM_PATTERN_FILES[@]} -gt 0 ]]; then
  PATTERN_SOURCE="custom"
elif [[ -n ${STRYKER_MUTATE-} ]]; then
  PATTERN_SOURCE="env"
elif [[ "$QUICK_MODE" == "true" ]]; then
  PATTERN_SOURCE="quick"
else
  PATTERN_SOURCE="default"
fi

case "$PATTERN_SOURCE" in
  custom)
    PATTERNS=""
    if [[ ${#CUSTOM_PATTERNS[@]} -gt 0 ]]; then
      PATTERNS+=$(printf '%s\n' "${CUSTOM_PATTERNS[@]}")
    fi
    for file in "${CUSTOM_PATTERN_FILES[@]}"; do
      if [[ -n "$file" ]]; then
        if [[ ! -f "$file" ]]; then
          echo "Pattern file not found: $file" >&2
          exit 1
        fi
        PATTERNS+=$(printf '%s\n' "$(<"$file")")
      fi
    done
    ;;
  env)
    PATTERNS=${STRYKER_MUTATE}
    ;;
  quick)
    PATTERNS=$QUICK_PATTERNS
    ;;
  default)
    PATTERNS=$DEFAULT_PATTERNS
    ;;
esac

if [[ -z ${PATTERNS//\s/} ]]; then
  echo "No mutate patterns specified" >&2
  exit 1
fi

if [[ "$QUICK_MODE" == "true" ]]; then
  STRYKER_CONCURRENCY=${STRYKER_CONCURRENCY:-1}
  STRYKER_TIMEOUT=${STRYKER_TIMEOUT:-10000}
  STRYKER_TIME_LIMIT=${STRYKER_TIME_LIMIT:-420}
fi

CONCURRENCY=${STRYKER_CONCURRENCY:-2}
TIMEOUT=${STRYKER_TIMEOUT:-15000}
TIME_LIMIT=${STRYKER_TIME_LIMIT:-900}
CONFIG_PATH=${CONFIG_PATH:-${STRYKER_CONFIG:-}}

args=()
while IFS= read -r pattern; do
  [[ -z "$pattern" ]] && continue
  args+=("--mutate" "$pattern")
done <<< "$PATTERNS"

printf "Running Stryker with patterns\n"
for ((i=1; i<${#args[@]}; i+=2)); do
  printf "  %s\n" "${args[i]}"
done
if [[ "$QUICK_MODE" == "true" ]]; then
  printf "Quick mode enabled: concurrency=%s, timeoutMS=%s, time-limit=%ss\n" "$CONCURRENCY" "$TIMEOUT" "$TIME_LIMIT"
fi

mkdir -p reports/mutation

CMD=(npx stryker run "${args[@]}" --concurrency "$CONCURRENCY" --timeoutMS "$TIMEOUT")
if [[ -n "$CONFIG_PATH" ]] ; then
  CMD+=("$CONFIG_PATH")
fi
if [[ ${#EXTRA_ARGS[@]} -gt 0 ]]; then
  CMD+=("${EXTRA_ARGS[@]}")
fi

if command -v timeout >/dev/null 2>&1; then
  timeout --foreground "${TIME_LIMIT}"s "${CMD[@]}"
else
  "${CMD[@]}"
fi
