#!/usr/bin/env bash

# Shared helpers for selecting container engines (Podman/Docker) and compose commands.
# Intended to be sourced from other scripts. Functions return non-zero on failure
# so callers can decide how to handle errors (fallback, exit, etc.).

# Selected engine binary (podman or docker)
declare -g CONTAINER_ENGINE_BIN=""
# Selected compose command as array (e.g. ("podman" "compose") or ("docker-compose"))
declare -ag CONTAINER_COMPOSE_CMD=()

container::warn() {
  printf '[container] %s\n' "$*" >&2
}

container::select_engine() {
  local requested="${CONTAINER_ENGINE:-}"
  local selected=""

  if [[ -n "$requested" ]]; then
    case "$requested" in
      podman|docker)
        if ! command -v "$requested" >/dev/null 2>&1; then
          container::warn "specified container engine '$requested' not found in PATH"
          return 1
        fi
        selected="$requested"
        ;;
      *)
        container::warn "unsupported CONTAINER_ENGINE value '$requested' (expected 'podman' or 'docker')"
        return 1
        ;;
    esac
  else
    if command -v podman >/dev/null 2>&1; then
      selected="podman"
    elif command -v docker >/dev/null 2>&1; then
      selected="docker"
    else
      container::warn "neither podman nor docker is available in PATH"
      return 1
    fi
  fi

  CONTAINER_ENGINE_BIN="$selected"
  export CONTAINER_ENGINE_BIN
  return 0
}

container::select_compose_command() {
  local engine="${1:-${CONTAINER_ENGINE_BIN:-}}"
  local preferred="${2:-}"

  if [[ -z "$engine" ]]; then
    container::warn "container engine not selected before compose detection"
    return 1
  fi

  CONTAINER_COMPOSE_CMD=()

  case "$engine" in
    docker)
      if [[ "$preferred" == "docker-compose" ]]; then
        if command -v docker-compose >/dev/null 2>&1; then
          CONTAINER_COMPOSE_CMD=(docker-compose)
          return 0
        fi
        container::warn "docker-compose binary not found"
        return 1
      fi
      if docker compose version >/dev/null 2>&1; then
        CONTAINER_COMPOSE_CMD=(docker compose)
        return 0
      fi
      if command -v docker-compose >/dev/null 2>&1; then
        CONTAINER_COMPOSE_CMD=(docker-compose)
        return 0
      fi
      container::warn "docker compose plugin and docker-compose binary are both unavailable"
      return 1
      ;;
    podman)
      if [[ "$preferred" == "podman-compose" ]]; then
        if command -v podman-compose >/dev/null 2>&1; then
          CONTAINER_COMPOSE_CMD=(podman-compose)
          return 0
        fi
        container::warn "podman-compose binary not found"
        return 1
      fi
      if "$engine" compose version >/dev/null 2>&1; then
        CONTAINER_COMPOSE_CMD=("$engine" compose)
        return 0
      fi
      if command -v podman-compose >/dev/null 2>&1; then
        CONTAINER_COMPOSE_CMD=(podman-compose)
        return 0
      fi
      container::warn "podman compose plugin and podman-compose binary are both unavailable"
      return 1
      ;;
    *)
      container::warn "compose detection not implemented for engine '$engine'"
      return 1
      ;;
  esac
}

container::compose() {
  if [[ ${#CONTAINER_COMPOSE_CMD[@]} -eq 0 ]]; then
    container::warn "compose command not initialised"
    return 1
  fi
  "${CONTAINER_COMPOSE_CMD[@]}" "$@"
}
