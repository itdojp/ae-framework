#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../lib/container.sh
source "$SCRIPT_DIR/../lib/container.sh"

COMPOSE_FILE="${AE_DEV_COMPOSE_FILE:-podman/compose.dev.yaml}"

echo "Stopping development environment..."

if ! container::select_engine; then
  echo "Error: Neither podman nor docker found!" >&2
  exit 1
fi
if ! container::select_compose_command "$CONTAINER_ENGINE_BIN"; then
  echo "Error: compose command unavailable for $CONTAINER_ENGINE_BIN" >&2
  exit 1
fi

container::compose --project-name ae-framework-dev -f "$COMPOSE_FILE" down -v --remove-orphans

echo "Development environment stopped"
