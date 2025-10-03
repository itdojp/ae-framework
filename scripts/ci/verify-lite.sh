#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")"/../.. && pwd)"
cd "$ROOT_DIR"

echo "[verify-lite] repo root: $ROOT_DIR"

if ! command -v pnpm >/dev/null 2>&1; then
  echo "[verify-lite] pnpm not found" >&2
  exit 1
fi

# Clean up temporary mutation directories that can break linting (e.g. .stryker-tmp)
for tmp_dir in .stryker-tmp .stryker-tmp-*; do
  if [[ -e "$tmp_dir" ]]; then
    echo "[verify-lite] removing temp directory $tmp_dir"
    rm -rf "$tmp_dir"
  fi
done

echo "[verify-lite] preparing spec-compiler (non-blocking)"
pnpm -F @ae-framework/spec-compiler -s run build || echo "[verify-lite] spec-compiler build failed (ignored)"

echo "[verify-lite] types:check"
pnpm types:check

echo "[verify-lite] lint (non-blocking)"
if [[ "${VERIFY_LITE_ENFORCE_LINT:-0}" == "1" ]]; then
  pnpm lint
else
  pnpm lint || echo "[verify-lite] lint failed (ignored)"
fi

echo "[verify-lite] build"
pnpm run build

echo "[verify-lite] BDD lint (non-blocking)"
if [[ -f scripts/bdd/lint.mjs ]]; then
  if [[ "${VERIFY_LITE_ENFORCE_BDD:-0}" == "1" ]]; then
    node scripts/bdd/lint.mjs
  else
    node scripts/bdd/lint.mjs || echo "[verify-lite] BDD lint failed (ignored)"
  fi
else
  echo "[verify-lite] no scripts/bdd/lint.mjs"
fi

echo "[verify-lite] step lint (non-blocking)"
if [[ -f scripts/bdd/step-lint.mjs ]]; then
  if [[ "${VERIFY_LITE_ENFORCE_BDD:-0}" == "1" ]]; then
    node scripts/bdd/step-lint.mjs
  else
    node scripts/bdd/step-lint.mjs || echo "[verify-lite] step lint failed (ignored)"
  fi
else
  echo "[verify-lite] no scripts/bdd/step-lint.mjs"
fi

echo "[verify-lite] mutation quick (optional)"
if [[ "${VERIFY_LITE_RUN_MUTATION:-0}" == "1" && -x scripts/mutation/run-scoped.sh ]]; then
  STRYKER_TIME_LIMIT=${STRYKER_TIME_LIMIT:-600} scripts/mutation/run-scoped.sh --quick --auto-diff || echo "[verify-lite] mutation quick failed (ignored)"
else
  echo "[verify-lite] skipping mutation quick"
fi

echo "[verify-lite] completed"
