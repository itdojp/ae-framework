#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd "${SCRIPT_DIR}/../.." && pwd)
PATTERN_DIR="${SCRIPT_DIR}/patterns"
RUN_SCOPED="${SCRIPT_DIR}/run-scoped.sh"
DEFAULT_CONFIG="${REPO_ROOT}/configs/stryker.config.js"

if [[ ! -x "${RUN_SCOPED}" ]]; then
  echo "run-scoped.sh not found or not executable: ${RUN_SCOPED}" >&2
  exit 1
fi

usage() {
  cat <<'USAGE'
Usage: run-enhanced-state-batches.sh [options] [-- extra-args]

Options:
  --no-quick        Disable default quick-mode flags (concurrency/timeouts stay as Stryker defaults)
  --config <path>   Override Stryker config (defaults to configs/stryker.config.js)
  -h, --help        Show this help message

Arguments after -- are forwarded directly to run-scoped.sh.
USAGE
}

USE_QUICK=true
CONFIG_PATH="${DEFAULT_CONFIG}"
PASS_THROUGH=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --no-quick)
      USE_QUICK=false
      shift
      ;;
    --config)
      shift
      if [[ $# -eq 0 ]]; then
        echo "--config requires a path" >&2
        exit 1
      fi
      CONFIG_PATH="$1"
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      PASS_THROUGH=("$@")
      break
      ;;
    *)
      PASS_THROUGH=("$@")
      break
      ;;
  esac
done

RUN_ARGS=("${CONFIG_PATH}")
if [[ "${USE_QUICK}" == true ]]; then
  RUN_ARGS=("--quick" "${RUN_ARGS[@]}")
fi

BATCHES=(
  "import"
  "snapshot"
  "failure"
)

SUCCESSFUL=()
FAILED=()

for batch in "${BATCHES[@]}"; do
  pattern_file="${PATTERN_DIR}/enhanced-state-${batch}.txt"
  if [[ ! -f "${pattern_file}" ]]; then
    echo "Pattern file missing: ${pattern_file}" >&2
    exit 1
  fi

  printf '\n=== Running enhanced state mutation batch: %s ===\n' "${batch}"
  set +e
  pnpm exec "${RUN_SCOPED}" "${RUN_ARGS[@]}" --mutate-file "${pattern_file}" "${PASS_THROUGH[@]}"
  status=$?
  set -e

  if [[ ${status} -eq 0 ]]; then
    SUCCESSFUL+=("${batch}")
  else
    FAILED+=("${batch}")
    printf 'Batch %s failed with status %s\n' "${batch}" "${status}" >&2
  fi
done

if [[ -z "${KEEP_STRYKER_TMP:-}" ]]; then
  rm -rf "${REPO_ROOT}/.stryker-tmp"
fi

if [[ ${#FAILED[@]} -gt 0 ]]; then
  printf '\nBatches failed: %s\n' "${FAILED[*]}" >&2
  exit 1
fi

printf '\nAll enhanced state mutation batches completed successfully: %s\n' "${SUCCESSFUL[*]}"
