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
SUMMARY_PATH="${VERIFY_LITE_SUMMARY_FILE:-verify-lite-run-summary.json}"
SUMMARY_EXPORT_PATH="${VERIFY_LITE_SUMMARY_EXPORT_PATH:-artifacts/verify-lite/verify-lite-run-summary.json}"
LINT_BASELINE_PATH="${VERIFY_LITE_LINT_BASELINE:-config/verify-lite-lint-baseline.json}"
VERIFY_LITE_LINT_ENFORCE="${VERIFY_LITE_LINT_ENFORCE:-${VERIFY_LITE_ENFORCE_LINT:-0}}"

INSTALL_STATUS="success"
INSTALL_NOTES="flags=${INSTALL_FLAGS_STR}"
INSTALL_RETRIED=0
SPEC_COMPILER_STATUS="skipped"
TYPECHECK_STATUS="pending"
LINT_STATUS="skipped"
BUILD_STATUS="pending"
BDD_LINT_STATUS="skipped"
STATE_MACHINE_STATUS="pending"
MUTATION_STATUS="skipped"
MUTATION_NOTES=""
LINT_LOG_EXPORT=""
LINT_SUMMARY_PATH=""
MUTATION_SUMMARY_PATH=""
MUTATION_SURVIVORS_PATH=""
CONFORMANCE_STATUS="skipped"
CONFORMANCE_NOTES="not_run"
CONFORMANCE_SUMMARY_PATH="${VERIFY_LITE_CONFORMANCE_SUMMARY_FILE:-reports/conformance/verify-lite-summary.json}"
CONFORMANCE_SUMMARY_MARKDOWN_PATH="${VERIFY_LITE_CONFORMANCE_MARKDOWN_FILE:-reports/conformance/verify-lite-summary.md}"

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
trap cleanup_lint EXIT

if pnpm lint 2>&1 | tee "$LINT_LOG_FILE"; then
  LINT_STATUS="success"
else
  LINT_STATUS="failure"
fi
if [[ -s "$LINT_LOG_FILE" ]]; then
  if node scripts/ci/verify-lite-lint-summary.mjs < "$LINT_LOG_FILE" > verify-lite-lint-summary.json; then
    LINT_SUMMARY_PATH="verify-lite-lint-summary.json"
  fi
  if [[ ${VERIFY_LITE_KEEP_LINT_LOG:-0} == "1" ]]; then
    cp "$LINT_LOG_FILE" verify-lite-lint.log
    LINT_LOG_EXPORT="verify-lite-lint.log"
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
if node dist/src/cli/index.js sm validate specs/state-machines --format json; then
  STATE_MACHINE_STATUS="success"
else
  STATE_MACHINE_STATUS="failure"
  echo "[verify-lite] state machine validation failed" >&2
  exit 1
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
export SPEC_COMPILER_STATUS TYPECHECK_STATUS LINT_STATUS BUILD_STATUS BDD_LINT_STATUS STATE_MACHINE_STATUS
export MUTATION_STATUS MUTATION_NOTES
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
  cp "$SUMMARY_PATH" "$SUMMARY_EXPORT_PATH"
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
