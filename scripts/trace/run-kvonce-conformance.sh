#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
DEFAULT_TRACE_DIR="${PROJECT_ROOT}/hermetic-reports/trace"
DEFAULT_OTLP_PAYLOAD="${DEFAULT_TRACE_DIR}/collected-kvonce-otlp.json"

usage() {
  cat <<'USAGE'
Usage: run-kvonce-conformance.sh [--input <file>] [--output-dir <dir>] [--format ndjson|otlp]
  --input       Path to KvOnce trace (NDJSON or OTLP JSON). Omit to use prepared payload.
  --output-dir  Directory where projection/validation outputs are written (default: hermetic-reports/trace).
  --format      Explicit input format. If omitted, inferred from file extension (.ndjson => ndjson).
USAGE
}

INPUT=""
OUTPUT_DIR="${DEFAULT_TRACE_DIR}"
FORMAT="auto"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --input|-i)
      if [[ $# -lt 2 ]]; then
        echo "[kvonce-conformance] missing value for $1" >&2
        usage
        exit 1
      fi
      INPUT="$2"
      shift 2
      ;;
    --output-dir|-o)
      if [[ $# -lt 2 ]]; then
        echo "[kvonce-conformance] missing value for $1" >&2
        usage
        exit 1
      fi
      OUTPUT_DIR="$2"
      shift 2
      ;;
    --format|-f)
      if [[ $# -lt 2 ]]; then
        echo "[kvonce-conformance] missing value for $1" >&2
        usage
        exit 1
      fi
      FORMAT="$2"
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "[kvonce-conformance] unknown argument: $1" >&2
      usage
      exit 1
      ;;
  esac
done

if [[ -z "${INPUT}" ]]; then
  INPUT="${DEFAULT_OTLP_PAYLOAD}"
  node "${SCRIPT_DIR}/prepare-otlp-trace.mjs"
fi

if [[ "${FORMAT}" == "auto" ]]; then
  if [[ "${INPUT}" == *.ndjson ]]; then
    FORMAT="ndjson"
  else
    FORMAT="otlp"
  fi
fi

mkdir -p "${OUTPUT_DIR}"
NDJSON_PATH="${OUTPUT_DIR}/kvonce-events.ndjson"
PROJECTION_PATH="${OUTPUT_DIR}/kvonce-projection.json"
VALIDATION_PATH="${OUTPUT_DIR}/kvonce-validation.json"

echo "[kvonce-conformance] input=${INPUT} format=${FORMAT} output_dir=${OUTPUT_DIR}"

TEMP_FILE=""
cleanup() {
  if [[ -n "${TEMP_FILE}" && -f "${TEMP_FILE}" ]]; then
    rm -f "${TEMP_FILE}"
  fi
}
trap cleanup EXIT

SOURCE_NDJSON="${INPUT}"

if [[ "${FORMAT}" == "otlp" ]]; then
  TMP_ROOT="${TMPDIR:-${PROJECT_ROOT}/.kvonce-tmp}"
  mkdir -p "${TMP_ROOT}"
  chmod 700 "${TMP_ROOT}"
  TEMP_FILE="$(mktemp -p "${TMP_ROOT}" kvonce-events-XXXXXX.ndjson)"
  if ! node "${SCRIPT_DIR}/convert-otlp-kvonce.mjs" --input "${INPUT}" --output "${TEMP_FILE}"; then
    status=$?
    if [[ ${status} -eq 2 ]]; then
      echo "[kvonce-conformance] no kvonce events found in OTLP payload" >&2
    fi
    exit ${status}
  fi
  cp "${TEMP_FILE}" "${NDJSON_PATH}"
  SOURCE_NDJSON="${NDJSON_PATH}"
elif [[ "${FORMAT}" == "ndjson" ]]; then
  # Skip the copy when the caller already pointed us at the destination path to avoid unnecessary I/O.
  if [[ "${INPUT}" != "${NDJSON_PATH}" ]]; then
    cp "${INPUT}" "${NDJSON_PATH}"
    SOURCE_NDJSON="${NDJSON_PATH}"
  fi
else
  echo "[kvonce-conformance] unsupported format: ${FORMAT}" >&2
  exit 1
fi

node "${SCRIPT_DIR}/projector-kvonce.mjs" --input "${SOURCE_NDJSON}" --output "${PROJECTION_PATH}"
node "${SCRIPT_DIR}/validate-kvonce.mjs" --input "${PROJECTION_PATH}" --output "${VALIDATION_PATH}"

if command -v jq >/dev/null 2>&1; then
  VALID=$(jq -r '.valid' "${VALIDATION_PATH}" 2>/dev/null || echo unknown)
else
  VALID=$(node "${SCRIPT_DIR}/read-validation-field.mjs" "${VALIDATION_PATH}" valid || echo unknown)
fi

if [[ "${VALID}" != "true" ]]; then
  echo "[kvonce-conformance] validation failed (valid=${VALID}). See ${VALIDATION_PATH}" >&2
  exit 1
fi

echo "[kvonce-conformance] projection -> ${PROJECTION_PATH}"
echo "[kvonce-conformance] validation -> ${VALIDATION_PATH}"
