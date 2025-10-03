#!/usr/bin/env bash
set -euo pipefail

export PODMAN_COMPOSE_PROVIDER="${PODMAN_COMPOSE_PROVIDER:-podman-compose}"
unset DOCKER_HOST DOCKER_CONTEXT

# Strip Windows paths so podman does not delegate to docker-compose.exe
if printf '%s' "$PATH" | grep -q '/mnt/c/'; then
  CLEAN_PATH="$(printf '%s' "$PATH" | tr ':' '\n' | grep -v '^/mnt/c/' | paste -sd: -)"
  if [[ -n "${CLEAN_PATH:-}" ]]; then
    export PATH="$CLEAN_PATH"
  fi
fi

# Ensure Podman runtime dir points to a writable location inside WSL
if [[ -z "${XDG_RUNTIME_DIR:-}" ]] || [[ $XDG_RUNTIME_DIR == /mnt/wslg* ]]; then
  uid="$(id -u)"
  if [[ -d "/run/user/$uid" ]]; then
    export XDG_RUNTIME_DIR="/run/user/$uid"
  else
    export XDG_RUNTIME_DIR="/tmp/run-user-$uid"
    mkdir -p "$XDG_RUNTIME_DIR" 2>/dev/null || true
    chmod 700 "$XDG_RUNTIME_DIR" 2>/dev/null || true
  fi
fi

export TMPDIR="${TMPDIR:-/tmp/podman-$(id -u)}"
mkdir -p "$TMPDIR" 2>/dev/null || true
chmod 700 "$TMPDIR" 2>/dev/null || true

COMPOSE_FILE="infra/podman/unit-compose.yml"
PROJECT_NAME="ae-unit"
PROJECT_DIR="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"

SELECTED_PROVIDER=""
cleanup() {
  if [[ -n "$SELECTED_PROVIDER" ]]; then
    case "$SELECTED_PROVIDER" in
      podman)
        (cd "$PROJECT_DIR" && podman compose -f "$COMPOSE_FILE" down --remove-orphans >/dev/null 2>&1) || true
        ;;
      podman-compose)
        (cd "$PROJECT_DIR" && podman-compose -f "$COMPOSE_FILE" down --remove-orphans >/dev/null 2>&1) || true
        ;;
    esac
  fi
}
trap cleanup EXIT INT TERM

fallback_local() {
  local reason="${1:-falling back to local vitest}"
  echo "[run-unit] $reason"
  pnpm exec vitest run tests/unit --reporter dot
  exit $?
}

if [[ ! -f "$COMPOSE_FILE" ]]; then
  fallback_local "compose file $COMPOSE_FILE not found"
fi

if ! command -v podman >/dev/null 2>&1; then
  fallback_local "podman not available"
fi

if ! timeout 30s podman ps >/dev/null 2>&1; then
  fallback_local "podman ps failed (check rootless runtime)"
fi

if ! timeout 30s podman system info >/dev/null 2>&1; then
  fallback_local "podman system info failed"
fi

STORE_DIR="${AE_HOST_STORE:-$PROJECT_DIR/.pnpm-store}"
mkdir -p "$STORE_DIR" 2>/dev/null || true

export PNPM_HOME="${PNPM_HOME:-$HOME/.local/share/pnpm}"
export PNPM_STORE_PATH="$STORE_DIR"
export AE_HOST_STORE="$STORE_DIR"

if command -v pnpm >/dev/null 2>&1; then
  (cd "$PROJECT_DIR" && pnpm fetch --prefer-offline) || echo "[run-unit] pnpm fetch failed; continuing"
fi

echo "[run-unit] provider=$PODMAN_COMPOSE_PROVIDER project_dir=$PROJECT_DIR"
export COMPOSE_PROJECT_NAME="$PROJECT_NAME"

run_with_provider() {
  local provider="$1"
  SELECTED_PROVIDER="$provider"
  case "$provider" in
    podman)
      (cd "$PROJECT_DIR" && timeout 600s podman compose -f "$COMPOSE_FILE" run --rm unit-tests)
      ;;
    podman-compose)
      (cd "$PROJECT_DIR" && timeout 600s podman-compose -f "$COMPOSE_FILE" run --rm unit-tests)
      ;;
    *)
      return 1
      ;;
  esac
}

if run_with_provider "$PODMAN_COMPOSE_PROVIDER"; then
  exit 0
fi

echo "[run-unit] provider=$PODMAN_COMPOSE_PROVIDER failed; trying podman-compose" >&2
if [[ "$PODMAN_COMPOSE_PROVIDER" != "podman-compose" ]] && run_with_provider podman-compose; then
  exit 0
fi

fallback_local "compose execution failed"
