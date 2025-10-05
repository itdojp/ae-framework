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

echo "[verify-lite] installing dependencies (${INSTALL_FLAGS[*]})"
if ! pnpm install "${INSTALL_FLAGS[@]}"; then
  echo "[verify-lite] initial pnpm install failed, retrying with --no-frozen-lockfile" >&2
  pnpm install --no-frozen-lockfile
fi

echo "[verify-lite] building spec-compiler types (non-blocking)"
pnpm -F @ae-framework/spec-compiler -s run build || true

echo "[verify-lite] running type checks"
pnpm types:check

echo "[verify-lite] linting"
LINT_LOG_FILE="$(mktemp)"
cleanup_lint() {
  if [[ ${VERIFY_LITE_KEEP_LINT_LOG:-0} != "1" && -f "$LINT_LOG_FILE" ]]; then
    rm -f "$LINT_LOG_FILE"
  fi
}
trap cleanup_lint EXIT

pnpm lint 2>&1 | tee "$LINT_LOG_FILE" || true
if [[ -s "$LINT_LOG_FILE" ]]; then
  node scripts/ci/verify-lite-lint-summary.mjs < "$LINT_LOG_FILE" > verify-lite-lint-summary.json || true
  if [[ ${VERIFY_LITE_KEEP_LINT_LOG:-0} == "1" ]]; then
    cp "$LINT_LOG_FILE" verify-lite-lint.log
  fi
fi

echo "[verify-lite] building project"
pnpm run build

echo "[verify-lite] optional BDD lint"
if [[ -f scripts/bdd/lint.mjs ]]; then
  node scripts/bdd/lint.mjs || true
fi

echo "[verify-lite] mutation quick (non-blocking)"
if [[ ${VERIFY_LITE_RUN_MUTATION:-0} == "1" && -x scripts/mutation/run-scoped.sh ]]; then
  ./scripts/mutation/run-scoped.sh --quick --auto-diff || true
else
  echo "[verify-lite] skipping mutation quick"
fi

echo "[verify-lite] summarising mutation survivors"
if [[ -f reports/mutation/mutation.json ]]; then
  node scripts/mutation/post-quick-summary.mjs | tee mutation-summary.md || true
  node scripts/mutation/list-survivors.mjs --limit 25 > reports/mutation/survivors.json || true
fi

echo "[verify-lite] local run complete"
