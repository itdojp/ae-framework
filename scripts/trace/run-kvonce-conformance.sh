#!/usr/bin/env bash
set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
INPUT="${1:-$PROJECT_ROOT/samples/trace/kvonce-sample.ndjson}"
OUTPUT_DIR="${2:-$PROJECT_ROOT/hermetic-reports/trace}"

if [[ ! -f "$INPUT" ]]; then
  echo "[kvonce-conformance] input NDJSON not found: $INPUT" >&2
  exit 1
fi

mkdir -p "$OUTPUT_DIR"
PROJECTION="$OUTPUT_DIR/kvonce-projection.json"
REPORT="$OUTPUT_DIR/kvonce-validation.json"

node "$PROJECT_ROOT/scripts/trace/projector-kvonce.mjs" --input "$INPUT" --output "$PROJECTION"
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
