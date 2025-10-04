#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
TRACE_DIR="${REPO_ROOT}/hermetic-reports/trace"
OTLP_PAYLOAD="${TRACE_DIR}/collected-kvonce-otlp.json"
NDJSON_EVENTS="${TRACE_DIR}/kvonce-events.ndjson"
PROJECTION_JSON="${TRACE_DIR}/kvonce-projection.json"
VALIDATION_JSON="${TRACE_DIR}/kvonce-validation.json"

mkdir -p "${TRACE_DIR}"

log() {
  printf '[trace-conformance] %s\n' "$1"
}

log "preparing OTLP payload"
node "${SCRIPT_DIR}/prepare-otlp-trace.mjs"

log "converting OTLP to NDJSON events"
set +e
node "${SCRIPT_DIR}/convert-otlp-kvonce.mjs" --input "${OTLP_PAYLOAD}" --output "${NDJSON_EVENTS}"
status=$?
set -e
if [[ ${status} -ne 0 ]]; then
  if [[ ${status} -eq 2 ]]; then
    log "no kvonce events found in OTLP payload"
  fi
  exit ${status}
fi

log "projecting NDJSON events"
node "${SCRIPT_DIR}/projector-kvonce.mjs" --input "${NDJSON_EVENTS}" --output "${PROJECTION_JSON}"

log "validating projection"
node "${SCRIPT_DIR}/validate-kvonce.mjs" --input "${PROJECTION_JSON}" --output "${VALIDATION_JSON}"

log "validation complete -> ${VALIDATION_JSON}"
