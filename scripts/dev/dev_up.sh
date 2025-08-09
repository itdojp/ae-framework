#!/usr/bin/env bash
set -euo pipefail

echo "Starting development environment..."

# Check if podman is available, fallback to docker
if command -v podman &> /dev/null; then
    COMPOSE_CMD="podman compose"
elif command -v docker &> /dev/null; then
    COMPOSE_CMD="docker compose"
else
    echo "Error: Neither podman nor docker found!"
    exit 1
fi

# Build and start services
$COMPOSE_CMD up -d --build

echo "Development environment started!"
echo "API: http://localhost:3000"
echo "Database: postgres://localhost:5432/app"
echo "OpenTelemetry Collector: http://localhost:4317"