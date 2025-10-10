#!/bin/bash
#
# Container image analysis helper (Podman/Docker compatible)
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}" )" && pwd)"
source "$SCRIPT_DIR/../lib/container.sh"

if ! container::select_engine; then
  echo "[analyze-image] no supported container engine found (install podman or docker)" >&2
  exit 1
fi

ENGINE_BIN="$CONTAINER_ENGINE_BIN"
IMAGE_NAME=${IMAGE_NAME:-ae-framework}
TAG="${1:-latest}"
FULL_IMAGE_NAME="${IMAGE_NAME}:${TAG}"
DOCKERFILE_PATH="podman/Dockerfile"

log_section() {
  printf '
===========================================
%s
===========================================
' "$1"
}

check_engine() {
  if ! "$ENGINE_BIN" info >/dev/null 2>&1; then
    echo "[analyze-image] '$ENGINE_BIN info' failed; ensure the engine daemon is running" >&2
    return 1
  fi
  echo "[analyze-image] using container engine: $ENGINE_BIN"
}

ensure_image_exists() {
  if ! "$ENGINE_BIN" image inspect "$FULL_IMAGE_NAME" >/dev/null 2>&1; then
    echo "[analyze-image] building $FULL_IMAGE_NAME from $DOCKERFILE_PATH"
    "$ENGINE_BIN" build -t "$FULL_IMAGE_NAME" -f "$DOCKERFILE_PATH" .
  else
    echo "[analyze-image] image $FULL_IMAGE_NAME already exists"
  fi
}

analyze_size() {
  log_section "Image Size"
  local image_size size_mb
  image_size=$("$ENGINE_BIN" image inspect "$FULL_IMAGE_NAME" --format='{{.Size}}')
  size_mb=$((image_size / 1024 / 1024))
  echo "Image size: ${size_mb} MB"
  "$ENGINE_BIN" history "$FULL_IMAGE_NAME" --format "table {{.CreatedBy}}\t{{.Size}}" | head -12
}

analyze_layers() {
  log_section "Layer Count"
  local layer_count
  layer_count=$("$ENGINE_BIN" history "$FULL_IMAGE_NAME" --quiet | wc -l)
  echo "Layer count: $layer_count"
}

test_security() {
  log_section "Runtime Security"
  local user_check shell_check
  user_check=$("$ENGINE_BIN" run --rm "$FULL_IMAGE_NAME" whoami 2>/dev/null || echo "root")
  echo "Runtime user: $user_check"
  shell_check=$("$ENGINE_BIN" run --rm "$FULL_IMAGE_NAME" which sh 2>/dev/null || echo "not present")
  echo "Shell availability: $shell_check"
}

test_runtime() {
  log_section "Runtime Smoke Test"
  local host_port container_id
  host_port=$(python3 -c "import socket; s=socket.socket(); s.bind(('', 0)); print(s.getsockname()[1]); s.close()" 2>/dev/null || echo "3001")
  container_id=$("$ENGINE_BIN" run -d --rm -p "${host_port}:3000" "$FULL_IMAGE_NAME" 2>/dev/null || echo "failed")
  if [[ "$container_id" == "failed" ]]; then
    echo "[analyze-image] failed to start container"
    return 1
  fi
  echo "Container ID: $container_id"
  sleep 5
  if curl -fsS "http://localhost:${host_port}/health" >/dev/null; then
    echo "Health check succeeded"
  else
    echo "Health endpoint did not respond successfully"
  fi
  "$ENGINE_BIN" stop "$container_id" >/dev/null 2>&1 || true
}

analyze_fs() {
  log_section "Filesystem Snapshot"
  local node_modules_count src_count
  node_modules_count=$("$ENGINE_BIN" run --rm "$FULL_IMAGE_NAME" sh -c "find /app/node_modules -name package.json 2>/dev/null | wc -l" || echo "0")
  echo "Production node_modules packages: $node_modules_count"
  src_count=$("$ENGINE_BIN" run --rm "$FULL_IMAGE_NAME" sh -c "find /app -name '*.ts' 2>/dev/null | wc -l" || echo "0")
  echo "TypeScript files inside image: $src_count"
}

main() {
  echo "[analyze-image] analyzing $FULL_IMAGE_NAME"
  check_engine
  ensure_image_exists
  analyze_size
  analyze_layers
  test_security
  test_runtime
  analyze_fs
  log_section "Analysis complete"
}

trap 'echo "[analyze-image] error occurred (line $LINENO)" >&2' ERR
main "$@"
