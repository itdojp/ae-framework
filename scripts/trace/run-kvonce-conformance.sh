#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<USAGE
Usage: run-kvonce-conformance.sh [--input <file>] [--output-dir <dir>] [--format ndjson|otlp]
  --input       Path to KvOnce trace (NDJSON or OTLP JSON). Default: samples/trace/kvonce-sample.ndjson
  --output-dir  Directory to place projection/validation outputs (default: hermetic-reports/trace)
  --format      Explicit trace format. If omitted, inferred from file extension (.ndjson -> ndjson, otherwise otlp)
USAGE
}

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
INPUT="$PROJECT_ROOT/samples/trace/kvonce-sample.ndjson"
OUTPUT_DIR="$PROJECT_ROOT/hermetic-reports/trace"
FORMAT="auto"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --input|-i)
      INPUT="$2"
      shift 2
      ;;
    --output-dir|-o)
      OUTPUT_DIR="$2"
      shift 2
      ;;
    --format|-f)
      FORMAT="$2"
      shift 2
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      usage
      exit 1
      ;;
  esac
done

if [[ ! -f "$INPUT" ]]; then
  echo "[kvonce-conformance] input file not found: $INPUT" >&2
  exit 1
fi

if [[ "$FORMAT" == "auto" ]]; then
  if [[ "$INPUT" == *.ndjson ]]; then
    FORMAT="ndjson"
  else
    FORMAT="otlp"
  fi
fi

mkdir -p "$OUTPUT_DIR"
PROJECTION="$OUTPUT_DIR/kvonce-projection.json"
REPORT="$OUTPUT_DIR/kvonce-validation.json"
TEMP_INPUT="$INPUT"
TEMP_FILE=""

cleanup() {
  if [[ -n "$TEMP_FILE" && -f "$TEMP_FILE" ]]; then
    rm -f "$TEMP_FILE"
  fi
}
trap cleanup EXIT

if [[ "$FORMAT" == "otlp" ]]; then
  if [[ ! -f "$INPUT" ]]; then
    echo "[kvonce-conformance] OTLP JSON not found: $INPUT" >&2
    exit 1
  fi
  TEMP_FILE="$(mktemp "${TMPDIR:-/tmp}/kvonce-otlp-XXXXXX.ndjson")"
  node "$PROJECT_ROOT/scripts/trace/convert-otlp-kvonce.mjs" --input "$INPUT" --output "$TEMP_FILE"
  TEMP_INPUT="$TEMP_FILE"
elif [[ "$FORMAT" != "ndjson" ]]; then
  echo "[kvonce-conformance] unknown format: $FORMAT" >&2
  exit 1
fi

node "$PROJECT_ROOT/scripts/trace/projector-kvonce.mjs" --input "$TEMP_INPUT" --output "$PROJECTION"
node "$PROJECT_ROOT/scripts/trace/validate-kvonce.mjs" --input "$PROJECTION" --output "$REPORT"

if command -v jq >/dev/null 2>&1; then
  VALID="$(jq -r '.valid' "$REPORT" 2>/dev/null || echo unknown)"
else
  VALID=$(node - <<'NODE'
const fs = require('fs');
const path = process.argv[1];
try {
  const json = JSON.parse(fs.readFileSync(path, 'utf8'));
  console.log(json.valid === false ? 'false' : json.valid === true ? 'true' : 'unknown');
} catch (error) {
  console.log('unknown');
}
NODE
 "$REPORT")
fi

if [[ "$VALID" != "true" ]]; then
  echo "[kvonce-conformance] validation failed (valid=$VALID). See $REPORT" >&2
  exit 1
fi

echo "[kvonce-conformance] projection -> $PROJECTION"
echo "[kvonce-conformance] validation -> $REPORT"
