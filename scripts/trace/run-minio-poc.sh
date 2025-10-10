#!/usr/bin/env bash
set -euo pipefail

COMPOSE_FILE="$(dirname "$0")/../../docker/trace-s3/docker-compose.yml"
PROJECT_DIR="$(cd "$(dirname "$0")/../../" && pwd)"

ENGINE_BIN="${CONTAINER_ENGINE:-}"
if [[ -n "$ENGINE_BIN" ]]; then
  if ! command -v "$ENGINE_BIN" >/dev/null 2>&1; then
    echo "[trace-minio] specified container engine '$ENGINE_BIN' not found" >&2
    exit 1
  fi
else
  if command -v podman >/dev/null 2>&1; then
    ENGINE_BIN="podman"
  elif command -v docker >/dev/null 2>&1; then
    ENGINE_BIN="docker"
  else
    echo "[trace-minio] neither podman nor docker is available" >&2
    exit 1
  fi
fi

if [[ "$ENGINE_BIN" == "docker" ]]; then
  if docker compose version >/dev/null 2>&1; then
    COMPOSE_CMD=(docker compose)
  elif command -v docker-compose >/dev/null 2>&1; then
    COMPOSE_CMD=(docker-compose)
  else
    echo "[trace-minio] docker compose plugin or docker-compose binary not found" >&2
    exit 1
  fi
else
  COMPOSE_CMD=("$ENGINE_BIN" compose)
fi

export COMPOSE_PROJECT_NAME="kvonce-trace"

compose_run() {
  "${COMPOSE_CMD[@]}" "$@"
}

cleanup() {
  compose_run -f "$COMPOSE_FILE" down --remove-orphans >/dev/null 2>&1 || true
}

if [[ "${1:-}" == "down" ]]; then
  cleanup
  exit 0
fi

trap cleanup EXIT

echo "[trace-minio] starting minio..."
compose_run -f "$COMPOSE_FILE" up -d minio

echo "[trace-minio] provisioning payload..."
compose_run -f "$COMPOSE_FILE" run --rm setup >/dev/null

echo
cat <<MSG
MinIO mock is ready.

Export the following variables before running trace workflows:

  export AWS_ACCESS_KEY_ID=kvonce
  export AWS_SECRET_ACCESS_KEY=kvonce-secret
  export KVONCE_OTLP_S3_ENDPOINT=http://127.0.0.1:9000
  export KVONCE_OTLP_S3_URI=s3://kvonce-trace/kvonce-stage2/payload.json
  export KVONCE_OTLP_S3_USE_SSL=false
  export KVONCE_OTLP_S3_FORCE_PATH_STYLE=true

Open http://localhost:9001 with user 'kvonce' and password 'kvonce-secret' to inspect objects.

Run './scripts/trace/run-minio-poc.sh down' to stop and clean up containers once finished.
MSG

compose_run -f "$COMPOSE_FILE" logs -f minio
