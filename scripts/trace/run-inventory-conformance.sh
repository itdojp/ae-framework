#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
DEFAULT_OUTPUT_DIR="${PROJECT_ROOT}/hermetic-reports/trace/inventory"
DEFAULT_INPUT="${PROJECT_ROOT}/samples/trace/inventory/sample.ndjson"

INPUT="${DEFAULT_INPUT}"
OUTPUT_DIR="${DEFAULT_OUTPUT_DIR}"
ONHAND_MIN=0
DISABLE=""

usage() {
  cat <<'USAGE'
Usage: run-inventory-conformance.sh [options]
  --input <file>           Inventory NDJSON trace (default: samples/trace/inventory/sample.ndjson)
  --output-dir <dir>       Directory for generated artifacts (default: hermetic-reports/trace/inventory)
  --onhand-min <number>    Minimum allowed onHand for validation (default: 0)
  --disable <list>         Comma-separated invariant ids to disable
  --help                   Show this help message
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --input|-i)
      if [[ $# -lt 2 ]]; then
        echo "[inventory-conformance] missing value for $1" >&2
        usage
        exit 1
      fi
      INPUT="$2"
      shift 2
      ;;
    --output-dir|-o)
      if [[ $# -lt 2 ]]; then
        echo "[inventory-conformance] missing value for $1" >&2
        usage
        exit 1
      fi
      OUTPUT_DIR="$2"
      shift 2
      ;;
    --onhand-min)
      if [[ $# -lt 2 ]]; then
        echo "[inventory-conformance] missing value for $1" >&2
        usage
        exit 1
      fi
      ONHAND_MIN="$2"
      shift 2
      ;;
    --disable)
      if [[ $# -lt 2 ]]; then
        echo "[inventory-conformance] missing value for $1" >&2
        usage
        exit 1
      fi
      DISABLE="$2"
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "[inventory-conformance] unknown argument: $1" >&2
      usage
      exit 1
      ;;
  esac
done

if [[ ! -f "${INPUT}" ]]; then
  echo "[inventory-conformance] input not found: ${INPUT}" >&2
  exit 1
fi

mkdir -p "${OUTPUT_DIR}"
NDJSON_PATH="${OUTPUT_DIR}/inventory-events.ndjson"
PROJECTION_PATH="${OUTPUT_DIR}/inventory-projection.json"
VALIDATION_PATH="${OUTPUT_DIR}/inventory-validation.json"
PROJECTED_DIR="${OUTPUT_DIR}/projected"
STATE_SEQUENCE_PATH="${PROJECTED_DIR}/inventory-state-sequence.json"

mkdir -p "${PROJECTED_DIR}"

if [[ "${INPUT}" != "${NDJSON_PATH}" ]]; then
  cp "${INPUT}" "${NDJSON_PATH}"
fi

node "${SCRIPT_DIR}/projector-inventory.mjs" \
  --input "${NDJSON_PATH}" \
  --output "${PROJECTION_PATH}" \
  --state-output "${STATE_SEQUENCE_PATH}"

VALIDATOR_ARGS=("${SCRIPT_DIR}/validate-inventory.mjs" "--input" "${PROJECTION_PATH}" "--state" "${STATE_SEQUENCE_PATH}" "--output" "${VALIDATION_PATH}")

if [[ -n "${ONHAND_MIN}" ]]; then
  VALIDATOR_ARGS+=("--onhand-min" "${ONHAND_MIN}")
fi
if [[ -n "${DISABLE}" ]]; then
  VALIDATOR_ARGS+=("--disable" "${DISABLE}")
fi

node "${VALIDATOR_ARGS[@]}"

fallback_valid="unknown"
if command -v jq >/dev/null 2>&1; then
  VALID=$(jq -r '.valid' "${VALIDATION_PATH}" 2>/dev/null || echo "${fallback_valid}")
else
  VALID=$(node "${SCRIPT_DIR}/read-validation-field.mjs" "${VALIDATION_PATH}" valid || echo "${fallback_valid}")
fi

if [[ "${VALID}" != "true" ]]; then
  echo "[inventory-conformance] validation failed (valid=${VALID}). See ${VALIDATION_PATH}" >&2
  exit 1
fi

echo "[inventory-conformance] wrote projection -> ${PROJECTION_PATH}"
echo "[inventory-conformance] wrote validation -> ${VALIDATION_PATH}"
