#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  scripts/ci/automation-rollback.sh <mode> [repo]

Modes:
  merge     Stop merge automation only (AE_AUTO_MERGE, AE_CODEX_AUTOPILOT_ENABLED)
  write     Stop all write-side automation (merge + AE_COPILOT_AUTO_FIX + AE_SELF_HEAL_ENABLED)
  freeze    Global freeze (write + AE_AUTOMATION_GLOBAL_DISABLE=1)
  unfreeze  Disable global kill-switch only (AE_AUTOMATION_GLOBAL_DISABLE=0)
  status    Show effective rollback-related repository variables

Repository:
  1) second argument
  2) GH_REPO
  3) GITHUB_REPOSITORY

Examples:
  scripts/ci/automation-rollback.sh merge itdojp/ae-framework
  GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh freeze
  scripts/ci/automation-rollback.sh status

Dry-run:
  AE_ROLLBACK_DRY_RUN=1 scripts/ci/automation-rollback.sh freeze
EOF
}

MODE="${1:-}"
REPO="${2:-${GH_REPO:-${GITHUB_REPOSITORY:-}}}"
DRY_RUN="${AE_ROLLBACK_DRY_RUN:-0}"

if [[ -z "${MODE}" ]]; then
  usage
  exit 1
fi

if [[ "${MODE}" == "--help" || "${MODE}" == "-h" ]]; then
  usage
  exit 0
fi

if [[ -z "${REPO}" ]]; then
  echo "error: repository is required (arg2 or GH_REPO/GITHUB_REPOSITORY)." >&2
  exit 1
fi

if ! command -v gh >/dev/null 2>&1; then
  echo "error: gh CLI is required." >&2
  exit 1
fi

if [[ ! "${REPO}" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]]; then
  echo "error: invalid repo format: ${REPO}" >&2
  exit 1
fi

set_var() {
  local key="$1"
  local value="$2"
  if [[ "${DRY_RUN}" == "1" ]]; then
    echo "[dry-run] gh variable set ${key} --repo ${REPO} --body ${value}"
    return 0
  fi
  gh variable set "${key}" --repo "${REPO}" --body "${value}" >/dev/null
  echo "[set] ${key}=${value}"
}

print_var() {
  local key="$1"
  local value
  if value="$(gh variable get "${key}" --repo "${REPO}" 2>/dev/null)"; then
    echo "${key}=${value}"
    return 0
  fi
  echo "${key}=<unset>"
}

apply_merge_stop() {
  set_var "AE_AUTO_MERGE" "0"
  set_var "AE_CODEX_AUTOPILOT_ENABLED" "0"
}

apply_write_stop() {
  apply_merge_stop
  set_var "AE_COPILOT_AUTO_FIX" "0"
  set_var "AE_SELF_HEAL_ENABLED" "0"
}

case "${MODE}" in
  merge)
    apply_merge_stop
    ;;
  write)
    apply_write_stop
    ;;
  freeze)
    apply_write_stop
    set_var "AE_AUTOMATION_GLOBAL_DISABLE" "1"
    ;;
  unfreeze)
    set_var "AE_AUTOMATION_GLOBAL_DISABLE" "0"
    ;;
  status)
    echo "# repo: ${REPO}"
    print_var "AE_AUTOMATION_GLOBAL_DISABLE"
    print_var "AE_AUTO_MERGE"
    print_var "AE_CODEX_AUTOPILOT_ENABLED"
    print_var "AE_COPILOT_AUTO_FIX"
    print_var "AE_SELF_HEAL_ENABLED"
    ;;
  *)
    echo "error: unknown mode: ${MODE}" >&2
    usage
    exit 1
    ;;
esac

