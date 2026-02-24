#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT_DIR"

if ! command -v pnpm >/dev/null 2>&1; then
  echo "[verify-lite] pnpm is required. Install pnpm (e.g. corepack enable pnpm) before running." >&2
  exit 1
fi

export CI=${CI:-1}
INSTALL_FLAGS=(--frozen-lockfile)
if [[ "${VERIFY_LITE_NO_FROZEN:-0}" == "1" ]]; then
  INSTALL_FLAGS=(--no-frozen-lockfile)
fi
INSTALL_FLAGS_STR="${INSTALL_FLAGS[*]}"

RUN_TIMESTAMP="$(date -u "+%Y-%m-%dT%H:%M:%SZ")"
SUMMARY_PATH="${VERIFY_LITE_SUMMARY_FILE:-artifacts/verify-lite/verify-lite-run-summary.json}"
SUMMARY_EXPORT_PATH="${VERIFY_LITE_SUMMARY_EXPORT_PATH:-}"
LINT_BASELINE_PATH="${VERIFY_LITE_LINT_BASELINE:-config/verify-lite-lint-baseline.json}"
VERIFY_LITE_LINT_ENFORCE="${VERIFY_LITE_LINT_ENFORCE:-${VERIFY_LITE_ENFORCE_LINT:-0}}"
LINT_SUMMARY_TARGET="${VERIFY_LITE_LINT_SUMMARY_FILE:-artifacts/verify-lite/verify-lite-lint-summary.json}"
LINT_LOG_TARGET="${VERIFY_LITE_LINT_LOG_FILE:-artifacts/verify-lite/verify-lite-lint.log}"

INSTALL_STATUS="success"
INSTALL_NOTES="flags=${INSTALL_FLAGS_STR}"
INSTALL_RETRIED=0
SPEC_COMPILER_STATUS="skipped"
TYPECHECK_STATUS="pending"
LINT_STATUS="skipped"
BUILD_STATUS="pending"
BDD_LINT_STATUS="skipped"
STATE_MACHINE_STATUS="pending"
STATE_MACHINE_RENDER_STATUS="pending"
CONTEXT_PACK_STATUS="pending"
CONTEXT_PACK_NOTES=""
CONTEXT_PACK_FUNCTOR_STATUS="pending"
CONTEXT_PACK_FUNCTOR_NOTES=""
CONTEXT_PACK_NATURAL_TRANSFORMATION_STATUS="pending"
CONTEXT_PACK_NATURAL_TRANSFORMATION_NOTES=""
CONTEXT_PACK_PRODUCT_COPRODUCT_STATUS="pending"
CONTEXT_PACK_PRODUCT_COPRODUCT_NOTES=""
MUTATION_STATUS="skipped"
MUTATION_NOTES=""
LINT_LOG_EXPORT=""
LINT_SUMMARY_PATH=""
MUTATION_SUMMARY_PATH=""
MUTATION_SURVIVORS_PATH=""
CONTEXT_PACK_REPORT_JSON_PATH="${VERIFY_LITE_CONTEXT_PACK_REPORT_JSON:-artifacts/context-pack/context-pack-validate-report.json}"
CONTEXT_PACK_REPORT_MD_PATH="${VERIFY_LITE_CONTEXT_PACK_REPORT_MD:-artifacts/context-pack/context-pack-validate-report.md}"
CONTEXT_PACK_FUNCTOR_MAP_PATH="${VERIFY_LITE_CONTEXT_PACK_FUNCTOR_MAP:-spec/context-pack/functor-map.json}"
CONTEXT_PACK_FUNCTOR_SCHEMA_PATH="${VERIFY_LITE_CONTEXT_PACK_FUNCTOR_SCHEMA:-schema/context-pack-functor-map.schema.json}"
CONTEXT_PACK_FUNCTOR_REPORT_JSON_PATH="${VERIFY_LITE_CONTEXT_PACK_FUNCTOR_REPORT_JSON:-artifacts/context-pack/context-pack-functor-report.json}"
CONTEXT_PACK_FUNCTOR_REPORT_MD_PATH="${VERIFY_LITE_CONTEXT_PACK_FUNCTOR_REPORT_MD:-artifacts/context-pack/context-pack-functor-report.md}"
CONTEXT_PACK_NATURAL_TRANSFORMATION_MAP_PATH="${VERIFY_LITE_CONTEXT_PACK_NATURAL_TRANSFORMATION_MAP:-spec/context-pack/natural-transformations.json}"
CONTEXT_PACK_NATURAL_TRANSFORMATION_SCHEMA_PATH="${VERIFY_LITE_CONTEXT_PACK_NATURAL_TRANSFORMATION_SCHEMA:-schema/context-pack-natural-transformation.schema.json}"
CONTEXT_PACK_NATURAL_TRANSFORMATION_REPORT_JSON_PATH="${VERIFY_LITE_CONTEXT_PACK_NATURAL_TRANSFORMATION_REPORT_JSON:-artifacts/context-pack/context-pack-natural-transformation-report.json}"
CONTEXT_PACK_NATURAL_TRANSFORMATION_REPORT_MD_PATH="${VERIFY_LITE_CONTEXT_PACK_NATURAL_TRANSFORMATION_REPORT_MD:-artifacts/context-pack/context-pack-natural-transformation-report.md}"
CONTEXT_PACK_PRODUCT_COPRODUCT_MAP_PATH="${VERIFY_LITE_CONTEXT_PACK_PRODUCT_COPRODUCT_MAP:-spec/context-pack/product-coproduct-map.json}"
CONTEXT_PACK_PRODUCT_COPRODUCT_SCHEMA_PATH="${VERIFY_LITE_CONTEXT_PACK_PRODUCT_COPRODUCT_SCHEMA:-schema/context-pack-product-coproduct.schema.json}"
CONTEXT_PACK_PRODUCT_COPRODUCT_REPORT_JSON_PATH="${VERIFY_LITE_CONTEXT_PACK_PRODUCT_COPRODUCT_REPORT_JSON:-artifacts/context-pack/context-pack-product-coproduct-report.json}"
CONTEXT_PACK_PRODUCT_COPRODUCT_REPORT_MD_PATH="${VERIFY_LITE_CONTEXT_PACK_PRODUCT_COPRODUCT_REPORT_MD:-artifacts/context-pack/context-pack-product-coproduct-report.md}"
TRACEABILITY_MATRIX_PATH="${VERIFY_LITE_TRACEABILITY_MATRIX:-docs/specs/ISSUE-TRACEABILITY-MATRIX.json}"
TRACEABILITY_STATUS="skipped"
TRACEABILITY_NOTES="matrix_not_found"
TRACEABILITY_MISSING_COUNT=0
CONFORMANCE_STATUS="skipped"
CONFORMANCE_NOTES="not_run"
CONFORMANCE_SUMMARY_PATH="${VERIFY_LITE_CONFORMANCE_SUMMARY_FILE:-reports/conformance/verify-lite-summary.json}"
CONFORMANCE_SUMMARY_MARKDOWN_PATH="${VERIFY_LITE_CONFORMANCE_MARKDOWN_FILE:-reports/conformance/verify-lite-summary.md}"

run_root_safe_cleanup() {
  local phase="${1:-post-run}"
  echo "[verify-lite] root safe cleanup (${phase})"
  if pnpm -s run clean:root-safe >/dev/null 2>&1; then
    echo "[verify-lite] root safe cleanup completed (${phase})"
  else
    echo "[verify-lite] root safe cleanup failed (${phase})" >&2
  fi
}

if [[ "${VERIFY_LITE_SKIP_INSTALL:-0}" == "1" ]]; then
  INSTALL_STATUS="skipped"
  INSTALL_NOTES="skipped (preinstalled)"
  echo "[verify-lite] skipping dependency install (VERIFY_LITE_SKIP_INSTALL=1)"
else
  echo "[verify-lite] installing dependencies (${INSTALL_FLAGS[*]})"
  if ! pnpm install "${INSTALL_FLAGS[@]}"; then
    INSTALL_RETRIED=1
    INSTALL_NOTES+=";retry_with=--no-frozen-lockfile"
    echo "[verify-lite] initial pnpm install failed, retrying with --no-frozen-lockfile" >&2
    if ! pnpm install --no-frozen-lockfile; then
      INSTALL_STATUS="failure"
      INSTALL_NOTES+=";retry_status=failed"
      echo "[verify-lite] pnpm install failed after retry" >&2
      exit 1
    fi
  fi
fi

run_root_safe_cleanup "pre-run"

echo "[verify-lite] building spec-compiler types (non-blocking)"
if pnpm -F @ae-framework/spec-compiler -s run build; then
  SPEC_COMPILER_STATUS="success"
else
  SPEC_COMPILER_STATUS="failure"
fi

echo "[verify-lite] running type checks"
if pnpm types:check; then
  TYPECHECK_STATUS="success"
else
  TYPECHECK_STATUS="failure"
  echo "[verify-lite] type check failed" >&2
  exit 1
fi

echo "[verify-lite] linting"
LINT_LOG_FILE="$(mktemp)"
cleanup_lint() {
  if [[ ${VERIFY_LITE_KEEP_LINT_LOG:-0} != "1" && -f "$LINT_LOG_FILE" ]]; then
    rm -f "$LINT_LOG_FILE"
  fi
}
cleanup_on_exit() {
  cleanup_lint
  run_root_safe_cleanup "post-run"
}
trap cleanup_on_exit EXIT

if pnpm lint 2>&1 | tee "$LINT_LOG_FILE"; then
  LINT_STATUS="success"
else
  LINT_STATUS="failure"
fi
if [[ -s "$LINT_LOG_FILE" ]]; then
  mkdir -p "$(dirname "$LINT_SUMMARY_TARGET")"
  if node scripts/ci/verify-lite-lint-summary.mjs < "$LINT_LOG_FILE" > "$LINT_SUMMARY_TARGET"; then
    LINT_SUMMARY_PATH="$LINT_SUMMARY_TARGET"
  fi
  if [[ ${VERIFY_LITE_KEEP_LINT_LOG:-0} == "1" ]]; then
    mkdir -p "$(dirname "$LINT_LOG_TARGET")"
    cp "$LINT_LOG_FILE" "$LINT_LOG_TARGET"
    LINT_LOG_EXPORT="$LINT_LOG_TARGET"
  fi
fi

echo "[verify-lite] building project"
if pnpm run build; then
  BUILD_STATUS="success"
else
  BUILD_STATUS="failure"
  echo "[verify-lite] build failed" >&2
  exit 1
fi

echo "[verify-lite] state machine validation"
if node dist/src/cli/index.js sm validate spec/state-machines --format json; then
  STATE_MACHINE_STATUS="success"
else
  STATE_MACHINE_STATUS="failure"
  echo "[verify-lite] state machine validation failed" >&2
  exit 1
fi

echo "[verify-lite] state machine render"
if node dist/src/cli/index.js sm render spec/state-machines --out artifacts/state-machines; then
  if node dist/src/cli/index.js sm render spec/state-machines --out artifacts/state-machines --check; then
    STATE_MACHINE_RENDER_STATUS="success"
    true
  else
    STATE_MACHINE_RENDER_STATUS="failure"
    echo "[verify-lite] state machine render check failed" >&2
    exit 1
  fi
else
  STATE_MACHINE_RENDER_STATUS="failure"
  echo "[verify-lite] state machine render failed" >&2
  exit 1
fi

echo "[verify-lite] context-pack validation"
if [[ "${VERIFY_LITE_SKIP_CONTEXT_PACK:-0}" == "1" ]]; then
  CONTEXT_PACK_STATUS="skipped"
  CONTEXT_PACK_NOTES="skipped by VERIFY_LITE_SKIP_CONTEXT_PACK=1"
  CONTEXT_PACK_FUNCTOR_STATUS="skipped"
  CONTEXT_PACK_FUNCTOR_NOTES="skipped with context-pack validation"
  CONTEXT_PACK_NATURAL_TRANSFORMATION_STATUS="skipped"
  CONTEXT_PACK_NATURAL_TRANSFORMATION_NOTES="skipped with context-pack validation"
  CONTEXT_PACK_PRODUCT_COPRODUCT_STATUS="skipped"
  CONTEXT_PACK_PRODUCT_COPRODUCT_NOTES="skipped with context-pack validation"
elif node scripts/context-pack/validate.mjs \
  --sources 'spec/context-pack/**/*.{yml,yaml,json}' \
  --schema schema/context-pack-v1.schema.json \
  --report-json "$CONTEXT_PACK_REPORT_JSON_PATH" \
  --report-md "$CONTEXT_PACK_REPORT_MD_PATH"; then
  CONTEXT_PACK_STATUS="success"
  CONTEXT_PACK_NOTES="validated spec/context-pack"
else
  CONTEXT_PACK_EXIT_CODE=$?
  CONTEXT_PACK_STATUS="failure"
  CONTEXT_PACK_NOTES="context-pack validation failed (exit=${CONTEXT_PACK_EXIT_CODE})"
  echo "[verify-lite] context-pack validation failed (exit=${CONTEXT_PACK_EXIT_CODE})" >&2
  exit "$CONTEXT_PACK_EXIT_CODE"
fi

if [[ "$CONTEXT_PACK_STATUS" == "success" ]]; then
  echo "[verify-lite] context-pack functor validation"
  if [[ "${VERIFY_LITE_SKIP_CONTEXT_PACK_FUNCTOR:-0}" == "1" ]]; then
    CONTEXT_PACK_FUNCTOR_STATUS="skipped"
    CONTEXT_PACK_FUNCTOR_NOTES="skipped by VERIFY_LITE_SKIP_CONTEXT_PACK_FUNCTOR=1"
  elif [[ ! -f "$CONTEXT_PACK_FUNCTOR_MAP_PATH" ]]; then
    CONTEXT_PACK_FUNCTOR_STATUS="skipped"
    CONTEXT_PACK_FUNCTOR_NOTES="map_not_found:${CONTEXT_PACK_FUNCTOR_MAP_PATH}"
  elif node scripts/context-pack/verify-functor.mjs \
    --map "$CONTEXT_PACK_FUNCTOR_MAP_PATH" \
    --schema "$CONTEXT_PACK_FUNCTOR_SCHEMA_PATH" \
    --report-json "$CONTEXT_PACK_FUNCTOR_REPORT_JSON_PATH" \
    --report-md "$CONTEXT_PACK_FUNCTOR_REPORT_MD_PATH"; then
    CONTEXT_PACK_FUNCTOR_STATUS="success"
    CONTEXT_PACK_FUNCTOR_NOTES="validated context-pack functor mapping"
    if [[ -f "$CONTEXT_PACK_FUNCTOR_REPORT_JSON_PATH" ]]; then
      if FUNCTOR_VIOLATION_COUNT="$(node --input-type=module -e "import fs from 'node:fs'; let count = 0; try { const data = JSON.parse(fs.readFileSync(process.argv[1], 'utf8')); count = data?.summary?.totalViolations ?? 0; } catch {} process.stdout.write(String(count));" "$CONTEXT_PACK_FUNCTOR_REPORT_JSON_PATH")"; then
        CONTEXT_PACK_FUNCTOR_NOTES="validated context-pack functor mapping;violations=${FUNCTOR_VIOLATION_COUNT}"
      else
        CONTEXT_PACK_FUNCTOR_NOTES="validated context-pack functor mapping;violations=parse_failed"
      fi
    fi
  else
    CONTEXT_PACK_FUNCTOR_EXIT_CODE=$?
    CONTEXT_PACK_FUNCTOR_STATUS="failure"
    CONTEXT_PACK_FUNCTOR_NOTES="context-pack functor validation failed (exit=${CONTEXT_PACK_FUNCTOR_EXIT_CODE})"
    echo "[verify-lite] context-pack functor validation failed (exit=${CONTEXT_PACK_FUNCTOR_EXIT_CODE})" >&2
    exit "$CONTEXT_PACK_FUNCTOR_EXIT_CODE"
  fi
fi

if [[ "$CONTEXT_PACK_STATUS" == "success" ]]; then
  echo "[verify-lite] context-pack natural transformation validation"
  if [[ "${VERIFY_LITE_SKIP_CONTEXT_PACK_NATURAL_TRANSFORMATION:-0}" == "1" ]]; then
    CONTEXT_PACK_NATURAL_TRANSFORMATION_STATUS="skipped"
    CONTEXT_PACK_NATURAL_TRANSFORMATION_NOTES="skipped by VERIFY_LITE_SKIP_CONTEXT_PACK_NATURAL_TRANSFORMATION=1"
  elif [[ ! -f "$CONTEXT_PACK_NATURAL_TRANSFORMATION_MAP_PATH" ]]; then
    CONTEXT_PACK_NATURAL_TRANSFORMATION_STATUS="skipped"
    CONTEXT_PACK_NATURAL_TRANSFORMATION_NOTES="map_not_found:${CONTEXT_PACK_NATURAL_TRANSFORMATION_MAP_PATH}"
  elif node scripts/context-pack/verify-natural-transformation.mjs \
    --map "$CONTEXT_PACK_NATURAL_TRANSFORMATION_MAP_PATH" \
    --schema "$CONTEXT_PACK_NATURAL_TRANSFORMATION_SCHEMA_PATH" \
    --report-json "$CONTEXT_PACK_NATURAL_TRANSFORMATION_REPORT_JSON_PATH" \
    --report-md "$CONTEXT_PACK_NATURAL_TRANSFORMATION_REPORT_MD_PATH"; then
    CONTEXT_PACK_NATURAL_TRANSFORMATION_STATUS="success"
    CONTEXT_PACK_NATURAL_TRANSFORMATION_NOTES="validated context-pack natural transformation mapping"
    if [[ -f "$CONTEXT_PACK_NATURAL_TRANSFORMATION_REPORT_JSON_PATH" ]]; then
      if NATURAL_TRANSFORMATION_VIOLATION_COUNT="$(node --input-type=module -e "import fs from 'node:fs'; let count = 0; try { const data = JSON.parse(fs.readFileSync(process.argv[1], 'utf8')); count = data?.summary?.totalViolations ?? 0; } catch {} process.stdout.write(String(count));" "$CONTEXT_PACK_NATURAL_TRANSFORMATION_REPORT_JSON_PATH")"; then
        CONTEXT_PACK_NATURAL_TRANSFORMATION_NOTES="validated context-pack natural transformation mapping;violations=${NATURAL_TRANSFORMATION_VIOLATION_COUNT}"
      else
        CONTEXT_PACK_NATURAL_TRANSFORMATION_NOTES="validated context-pack natural transformation mapping;violations=parse_failed"
      fi
    fi
  else
    CONTEXT_PACK_NATURAL_TRANSFORMATION_EXIT_CODE=$?
    CONTEXT_PACK_NATURAL_TRANSFORMATION_STATUS="failure"
    CONTEXT_PACK_NATURAL_TRANSFORMATION_NOTES="context-pack natural transformation validation failed (exit=${CONTEXT_PACK_NATURAL_TRANSFORMATION_EXIT_CODE})"
    echo "[verify-lite] context-pack natural transformation validation failed (exit=${CONTEXT_PACK_NATURAL_TRANSFORMATION_EXIT_CODE})" >&2
    exit "$CONTEXT_PACK_NATURAL_TRANSFORMATION_EXIT_CODE"
  fi
fi

if [[ "$CONTEXT_PACK_STATUS" == "success" ]]; then
  echo "[verify-lite] context-pack product/coproduct validation"
  if [[ "${VERIFY_LITE_SKIP_CONTEXT_PACK_PRODUCT_COPRODUCT:-0}" == "1" ]]; then
    CONTEXT_PACK_PRODUCT_COPRODUCT_STATUS="skipped"
    CONTEXT_PACK_PRODUCT_COPRODUCT_NOTES="skipped by VERIFY_LITE_SKIP_CONTEXT_PACK_PRODUCT_COPRODUCT=1"
  elif [[ ! -f "$CONTEXT_PACK_PRODUCT_COPRODUCT_MAP_PATH" ]]; then
    CONTEXT_PACK_PRODUCT_COPRODUCT_STATUS="skipped"
    CONTEXT_PACK_PRODUCT_COPRODUCT_NOTES="map_not_found:${CONTEXT_PACK_PRODUCT_COPRODUCT_MAP_PATH}"
  elif node scripts/context-pack/verify-product-coproduct.mjs \
    --map "$CONTEXT_PACK_PRODUCT_COPRODUCT_MAP_PATH" \
    --schema "$CONTEXT_PACK_PRODUCT_COPRODUCT_SCHEMA_PATH" \
    --report-json "$CONTEXT_PACK_PRODUCT_COPRODUCT_REPORT_JSON_PATH" \
    --report-md "$CONTEXT_PACK_PRODUCT_COPRODUCT_REPORT_MD_PATH"; then
    CONTEXT_PACK_PRODUCT_COPRODUCT_STATUS="success"
    CONTEXT_PACK_PRODUCT_COPRODUCT_NOTES="validated context-pack product/coproduct mapping"
    if [[ -f "$CONTEXT_PACK_PRODUCT_COPRODUCT_REPORT_JSON_PATH" ]]; then
      if PRODUCT_COPRODUCT_GAP_COUNT="$(node --input-type=module -e "import fs from 'node:fs'; let count = 0; try { const data = JSON.parse(fs.readFileSync(process.argv[1], 'utf8')); count = data?.uncoveredFailureVariants ?? 0; } catch {} process.stdout.write(String(count));" "$CONTEXT_PACK_PRODUCT_COPRODUCT_REPORT_JSON_PATH")"; then
        CONTEXT_PACK_PRODUCT_COPRODUCT_NOTES="validated context-pack product/coproduct mapping;uncovered_variants=${PRODUCT_COPRODUCT_GAP_COUNT}"
      else
        CONTEXT_PACK_PRODUCT_COPRODUCT_NOTES="validated context-pack product/coproduct mapping;uncovered_variants=parse_failed"
      fi
    fi
  else
    CONTEXT_PACK_PRODUCT_COPRODUCT_EXIT_CODE=$?
    CONTEXT_PACK_PRODUCT_COPRODUCT_STATUS="failure"
    CONTEXT_PACK_PRODUCT_COPRODUCT_NOTES="context-pack product/coproduct validation failed (exit=${CONTEXT_PACK_PRODUCT_COPRODUCT_EXIT_CODE})"
    echo "[verify-lite] context-pack product/coproduct validation failed (exit=${CONTEXT_PACK_PRODUCT_COPRODUCT_EXIT_CODE})" >&2
    exit "$CONTEXT_PACK_PRODUCT_COPRODUCT_EXIT_CODE"
  fi
fi

echo "[verify-lite] traceability matrix summary"
if [[ -f "$TRACEABILITY_MATRIX_PATH" ]]; then
  if TRACEABILITY_MISSING_COUNT="$(node --input-type=module -e "
import fs from 'node:fs';
const path = process.argv[1];
const raw = fs.readFileSync(path, 'utf8');
const payload = JSON.parse(raw);
const toArray = (value) => Array.isArray(value) ? value.filter((item) => typeof item === 'string') : [];
const hasContextColumns = (row) => Object.prototype.hasOwnProperty.call(row ?? {}, 'diagramId')
  || Object.prototype.hasOwnProperty.call(row ?? {}, 'diagramIds')
  || Object.prototype.hasOwnProperty.call(row ?? {}, 'morphismId')
  || Object.prototype.hasOwnProperty.call(row ?? {}, 'morphismIds')
  || Object.prototype.hasOwnProperty.call(row ?? {}, 'acceptanceTestId')
  || Object.prototype.hasOwnProperty.call(row ?? {}, 'acceptanceTestIds');
const rows = Array.isArray(payload?.rows) ? payload.rows : [];
const missingRows = rows.filter((row) => {
  const tests = toArray(row?.tests);
  const code = toArray(row?.code);
  const baseMissing = tests.length === 0 || code.length === 0;
  if (!hasContextColumns(row)) {
    return baseMissing;
  }
  const diagram = toArray(row?.diagramId ?? row?.diagramIds);
  const morphism = toArray(row?.morphismId ?? row?.morphismIds);
  const acceptance = toArray(row?.acceptanceTestId ?? row?.acceptanceTestIds);
  const contextMissing = diagram.length === 0 || morphism.length === 0 || acceptance.length === 0;
  return baseMissing || contextMissing;
});
process.stdout.write(String(missingRows.length));
" "$TRACEABILITY_MATRIX_PATH")"; then
    TRACEABILITY_STATUS="success"
    TRACEABILITY_NOTES="matrix=$(realpath --relative-to=\"$ROOT_DIR\" \"$TRACEABILITY_MATRIX_PATH\");missing=${TRACEABILITY_MISSING_COUNT}"
  else
    TRACEABILITY_STATUS="failure"
    TRACEABILITY_NOTES="matrix_parse_failed"
    TRACEABILITY_MISSING_COUNT=0
  fi
else
  TRACEABILITY_STATUS="skipped"
  TRACEABILITY_NOTES="matrix_not_found"
fi

echo "[verify-lite] optional BDD lint"
if [[ -f scripts/bdd/lint.mjs ]]; then
  if node scripts/bdd/lint.mjs; then
    BDD_LINT_STATUS="success"
  else
    BDD_LINT_STATUS="failure"
  fi
fi

echo "[verify-lite] mutation quick (non-blocking)"
if [[ ${VERIFY_LITE_RUN_MUTATION:-0} == "1" && -x scripts/mutation/run-scoped.sh ]]; then
  if ./scripts/mutation/run-scoped.sh --quick --auto-diff; then
    MUTATION_STATUS="success"
  else
    MUTATION_STATUS="failure"
    MUTATION_NOTES="run-scoped.sh exit != 0"
  fi
else
  echo "[verify-lite] skipping mutation quick"
fi

echo "[verify-lite] summarising mutation results"
if [[ -f reports/mutation/mutation.json || -f reports/mutation/mutation.html || -f reports/mutation/index.html ]]; then
  if [[ ${VERIFY_LITE_RUN_MUTATION:-0} != "1" && "$MUTATION_STATUS" == "skipped" ]]; then
    MUTATION_STATUS="success"
    if [[ -z "$MUTATION_NOTES" ]]; then
      MUTATION_NOTES="external (composite action)"
    fi
  fi
  if node scripts/mutation/mutation-report.mjs; then
    if [[ -f reports/mutation/summary.json ]]; then
      MUTATION_SUMMARY_PATH="reports/mutation/summary.json"
    fi
  else
    echo "[verify-lite] mutation summary generation failed" >&2
  fi
  if node scripts/mutation/list-survivors.mjs --limit 25 > reports/mutation/survivors.json; then
    MUTATION_SURVIVORS_PATH="reports/mutation/survivors.json"
  fi
fi

echo "[verify-lite] conformance report"
if pnpm -s tsx src/cli/index.ts conformance report \
  --format both \
  --output "$CONFORMANCE_SUMMARY_PATH" \
  --markdown-output "$CONFORMANCE_SUMMARY_MARKDOWN_PATH"; then
  if [[ -f "$CONFORMANCE_SUMMARY_PATH" ]]; then
    if ! CONFORMANCE_STATUS="$(node --input-type=module -e "import fs from 'node:fs'; let status = 'unknown'; try { const data = JSON.parse(fs.readFileSync(process.argv[1], 'utf8')); status = data?.status ?? 'unknown'; } catch {} process.stdout.write(status);" "$CONFORMANCE_SUMMARY_PATH")"; then
      CONFORMANCE_STATUS="failure"
    fi
    if ! CONFORMANCE_NOTES="$(node --input-type=module -e "import fs from 'node:fs'; let note = 'summary_parse_failed'; try { const data = JSON.parse(fs.readFileSync(process.argv[1], 'utf8')); const runs = data?.runsAnalyzed ?? 0; const violations = data?.totals?.totalViolations ?? 0; note = \`runs=\${runs};violations=\${violations}\`; } catch {} process.stdout.write(note);" "$CONFORMANCE_SUMMARY_PATH")"; then
      CONFORMANCE_NOTES="summary_parse_failed"
    fi
  else
    CONFORMANCE_STATUS="failure"
    CONFORMANCE_NOTES="summary_missing"
  fi
else
  CONFORMANCE_STATUS="failure"
  CONFORMANCE_NOTES="command_failed"
fi

export RUN_TIMESTAMP
export SUMMARY_PATH
export INSTALL_STATUS INSTALL_NOTES INSTALL_RETRIED
export SPEC_COMPILER_STATUS TYPECHECK_STATUS LINT_STATUS BUILD_STATUS BDD_LINT_STATUS STATE_MACHINE_STATUS STATE_MACHINE_RENDER_STATUS
export MUTATION_STATUS MUTATION_NOTES
export CONTEXT_PACK_STATUS CONTEXT_PACK_NOTES CONTEXT_PACK_REPORT_JSON_PATH CONTEXT_PACK_REPORT_MD_PATH
export CONTEXT_PACK_FUNCTOR_STATUS CONTEXT_PACK_FUNCTOR_NOTES
export CONTEXT_PACK_FUNCTOR_REPORT_JSON_PATH CONTEXT_PACK_FUNCTOR_REPORT_MD_PATH
export CONTEXT_PACK_NATURAL_TRANSFORMATION_STATUS CONTEXT_PACK_NATURAL_TRANSFORMATION_NOTES
export CONTEXT_PACK_NATURAL_TRANSFORMATION_REPORT_JSON_PATH CONTEXT_PACK_NATURAL_TRANSFORMATION_REPORT_MD_PATH
export CONTEXT_PACK_PRODUCT_COPRODUCT_STATUS CONTEXT_PACK_PRODUCT_COPRODUCT_NOTES
export CONTEXT_PACK_PRODUCT_COPRODUCT_REPORT_JSON_PATH CONTEXT_PACK_PRODUCT_COPRODUCT_REPORT_MD_PATH
export TRACEABILITY_STATUS TRACEABILITY_NOTES TRACEABILITY_MISSING_COUNT TRACEABILITY_MATRIX_PATH
export INSTALL_FLAGS_STR
export LINT_SUMMARY_PATH LINT_LOG_EXPORT
export MUTATION_SUMMARY_PATH MUTATION_SURVIVORS_PATH
export CONFORMANCE_STATUS CONFORMANCE_NOTES
export CONFORMANCE_SUMMARY_PATH CONFORMANCE_SUMMARY_MARKDOWN_PATH

if ! node scripts/ci/write-verify-lite-summary.mjs "$SUMMARY_PATH"; then
  echo "[verify-lite] failed to persist summary" >&2
  exit 1
fi

if [[ -n "$SUMMARY_EXPORT_PATH" ]]; then
  mkdir -p "$(dirname "$SUMMARY_EXPORT_PATH")"
  if [[ "$SUMMARY_EXPORT_PATH" != "$SUMMARY_PATH" ]]; then
    cp "$SUMMARY_PATH" "$SUMMARY_EXPORT_PATH"
  fi
fi

if [[ -n "$LINT_SUMMARY_PATH" && -f "$LINT_SUMMARY_PATH" ]]; then
  if node scripts/ci/enforce-verify-lite-lint.mjs "$LINT_SUMMARY_PATH" "$LINT_BASELINE_PATH"; then
    true
  else
    status=$?
    if [[ ${VERIFY_LITE_LINT_ENFORCE:-0} == "1" ]]; then
      exit "$status"
    fi
  fi
fi

echo "[verify-lite] local run complete"
