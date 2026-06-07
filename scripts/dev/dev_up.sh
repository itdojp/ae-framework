#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../lib/container.sh
source "$SCRIPT_DIR/../lib/container.sh"

require_dev_secret_env() {
  local missing=()
  for name in AE_DEV_POSTGRES_USER AE_DEV_POSTGRES_PASSWORD AE_DEV_POSTGRES_DB; do
    if [[ -z "${!name:-}" ]]; then
      missing+=("$name")
    fi
  done
  if [[ ${#missing[@]} -gt 0 ]]; then
    printf 'Error: set development compose secret environment variables: %s\n' "${missing[*]}" >&2
    return 1
  fi
}

COMPOSE_FILE="${AE_DEV_COMPOSE_FILE:-podman/compose.dev.yaml}"

echo "Starting development environment..."
require_dev_secret_env

if ! container::select_engine; then
  echo "Error: Neither podman nor docker found!" >&2
  exit 1
fi
if ! container::select_compose_command "$CONTAINER_ENGINE_BIN"; then
  echo "Error: compose command unavailable for $CONTAINER_ENGINE_BIN" >&2
  exit 1
fi

container::compose --project-name ae-framework-dev -f "$COMPOSE_FILE" up -d --build

echo "Development environment started"
echo "API: http://localhost:3000"
echo "Database: postgres://localhost:5432/${AE_DEV_POSTGRES_DB}"
echo "OpenTelemetry Collector: http://localhost:4317"
