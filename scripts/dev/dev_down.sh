#!/usr/bin/env bash
set -euo pipefail

echo "Stopping development environment..."

# Check if podman is available, fallback to docker
if command -v podman &> /dev/null; then
    COMPOSE_CMD="podman compose"
elif command -v docker &> /dev/null; then
    COMPOSE_CMD="docker compose"
else
    echo "Error: Neither podman nor docker found!"
    exit 1
fi

# Stop and remove containers
$COMPOSE_CMD down -v

echo "Development environment stopped"