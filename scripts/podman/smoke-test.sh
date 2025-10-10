#!/usr/bin/env bash
#
# Podman smoke test helper
#  - Builds runtime / test images defined under podman/
#  - Validates compose manifests via `podman compose config`
#  - Optional lightweight container boot check
#
# This script prefers Podman but can fallback to an alternative container
# engine by exporting CONTAINER_ENGINE.

set -euo pipefail

ROOT_DIR="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT_DIR"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/../lib/container.sh"

CLI_ENGINE_OVERRIDE=""
COMPOSE_FILES=(
  "podman/compose.dev.yaml"
  "podman/compose.prod.yaml"
  "podman/compose.test.yaml"
)
RUNTIME_TAG="${PODMAN_SMOKE_RUNTIME_TAG:-ae-framework/podman-smoke:runtime}"
TEST_TAG="${PODMAN_SMOKE_TEST_TAG:-ae-framework/podman-smoke:test}"
DO_COMPOSE_UP=false
KEEP_IMAGES=false
SKIP_BUILD=false
SKIP_COMPOSE=false

log() {
  printf '\033[36m[podman-smoke]\033[0m %s\n' "$*"
}

warn() {
  printf '\033[33m[podman-smoke][warn]\033[0m %s\n' "$*" >&2
}

fail() {
  printf '\033[31m[podman-smoke][error]\033[0m %s\n' "$*" >&2
  exit 1
}

usage() {
  cat <<'USAGE'
Usage: scripts/podman/smoke-test.sh [options]

Options:
  --engine <bin>        Container engine command (default: podman)
  --skip-build          Skip image build stage
  --skip-compose        Skip compose validation
  --up                  Run compose test stack (compose.test) and tear down
  --keep-images         Do not remove smoke-test images afterwards
  -h, --help            Show this help message

Environment overrides:
  CONTAINER_ENGINE                  Override container engine binary
  PODMAN_SMOKE_RUNTIME_TAG          Custom tag for runtime image build
  PODMAN_SMOKE_TEST_TAG             Custom tag for test image build
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --engine)
      shift
      CLI_ENGINE_OVERRIDE="${1:-}"
      [[ -n "$CLI_ENGINE_OVERRIDE" ]] || fail "--engine requires a value"
      ;;
    --skip-build)
      SKIP_BUILD=true
      ;;
    --skip-compose)
      SKIP_COMPOSE=true
      ;;
    --up)
      DO_COMPOSE_UP=true
      ;;
    --keep-images)
      KEEP_IMAGES=true
      ;;
    --)
      shift
      continue
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      fail "Unknown option: $1"
      ;;
  esac
  shift || true
done

if [[ -n "$CLI_ENGINE_OVERRIDE" ]]; then
  export CONTAINER_ENGINE="$CLI_ENGINE_OVERRIDE"
fi

if ! container::select_engine; then
  fail "No supported container engine found (install podman or docker)"
fi

if ! container::select_compose_command "$CONTAINER_ENGINE_BIN"; then
  fail "Compose support not available for '$CONTAINER_ENGINE_BIN'"
fi

ENGINE_BIN="$CONTAINER_ENGINE_BIN"

compose_run() {
  container::compose "$@"
}

cleanup() {
  local status=$?
  if [[ "$DO_COMPOSE_UP" == true ]]; then
    for file in "${COMPOSE_FILES[@]}"; do
      [[ -f "$file" ]] || continue
      if [[ "$file" == *compose.test.yaml ]]; then
        compose_run -f "$file" down --remove-orphans >/dev/null 2>&1 || true
      fi
    done
  fi

  if [[ "$KEEP_IMAGES" == false ]]; then
    "$ENGINE_BIN" image rm -f "$RUNTIME_TAG" >/dev/null 2>&1 || true
    "$ENGINE_BIN" image rm -f "$TEST_TAG" >/dev/null 2>&1 || true
  fi
  return $status
}
trap cleanup EXIT

log "using engine: $ENGINE_BIN"
"$ENGINE_BIN" version || warn "Failed to retrieve engine version information; continuing"

if [[ "$SKIP_BUILD" == false ]]; then
  log "building runtime image ($RUNTIME_TAG)"
  "$ENGINE_BIN" build \
    --file podman/Dockerfile \
    --tag "$RUNTIME_TAG" \
    podman/.. || fail "Runtime image build failed"

  log "building test image ($TEST_TAG)"
  "$ENGINE_BIN" build \
    --file podman/Dockerfile.test \
    --target test-base \
    --tag "$TEST_TAG" \
    podman/.. || fail "Test image build failed"
else
  log "skipping image build stage (--skip-build)"
fi

if [[ "$SKIP_COMPOSE" == false ]]; then
  for file in "${COMPOSE_FILES[@]}"; do
    if [[ ! -f "$file" ]]; then
      warn "Compose file not found: $file"
      continue
    fi
    log "validating compose file: $file"
    compose_run -f "$file" config >/dev/null || fail "Compose validation failed for $file"
  done
else
  log "skipping compose validation (--skip-compose)"
fi

if [[ "$DO_COMPOSE_UP" == true ]]; then
  test_compose="podman/compose.test.yaml"
  if [[ -f "$test_compose" ]]; then
    log "bringing up compose stack for smoke test ($test_compose)"
    compose_run -f "$test_compose" up --build --abort-on-container-exit || fail "Compose smoke run failed"
  else
    warn "Compose test file not found; skipping --up: $test_compose"
  fi
fi

log "Podman smoke test completed successfully"
