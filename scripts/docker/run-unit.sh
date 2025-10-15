#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/../lib/container.sh"

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

cleanup() {
  if [[ -f "$COMPOSE_FILE" ]] && [[ ${#CONTAINER_COMPOSE_CMD[@]} -gt 0 ]]; then
    local -a compose_cmd=("${CONTAINER_COMPOSE_CMD[@]}")
    (cd "$PROJECT_DIR" && "${compose_cmd[@]}" -f "$COMPOSE_FILE" down --remove-orphans >/dev/null 2>&1) || true
  fi
}
trap cleanup EXIT INT TERM

fallback_local() {
  local reason="${1:-falling back to local vitest}"
  echo "[run-unit][info] $reason"
  pnpm exec vitest run tests/unit --reporter dot
  exit $?
}

if [[ ! -f "$COMPOSE_FILE" ]]; then
  fallback_local "compose file $COMPOSE_FILE not found"
fi

if ! container::select_engine; then
  fallback_local "no supported container engine found"
fi

if ! timeout 30s "$CONTAINER_ENGINE_BIN" ps >/dev/null 2>&1; then
  fallback_local "$CONTAINER_ENGINE_BIN ps failed (check rootless runtime)"
fi

if ! timeout 30s "$CONTAINER_ENGINE_BIN" system info >/dev/null 2>&1; then
  fallback_local "$CONTAINER_ENGINE_BIN system info failed"
fi

select_compose() {
  local preference="${1:-}"
  if [[ -n "$preference" ]]; then
    if container::select_compose_command "$CONTAINER_ENGINE_BIN" "$preference"; then
      return 0
    fi
    echo "[run-unit] provider=$preference unavailable; attempting auto-detect" >&2
  fi
  container::select_compose_command "$CONTAINER_ENGINE_BIN"
}

if ! select_compose "$PODMAN_COMPOSE_PROVIDER"; then
  fallback_local "compose command not available for $CONTAINER_ENGINE_BIN"
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

run_compose_tests() {
  local -a compose_cmd=("${CONTAINER_COMPOSE_CMD[@]}")
  (cd "$PROJECT_DIR" && timeout 600s "${compose_cmd[@]}" -f "$COMPOSE_FILE" run --rm unit-tests)
}

if run_compose_tests; then
  exit 0
fi

if [[ "$PODMAN_COMPOSE_PROVIDER" != "podman-compose" ]]; then
  if select_compose "podman-compose" && run_compose_tests; then
    exit 0
  fi
fi

fallback_local "compose execution failed"
