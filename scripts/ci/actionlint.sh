#!/usr/bin/env bash
set -euo pipefail

# actionlint をローカルで実行するユーティリティ
# 優先: ローカルバイナリ → Podman/Docker コンテナ

ENGINE_BIN="${CONTAINER_ENGINE:-}"
ACTIONLINT_BIN_OVERRIDE="${ACTIONLINT_BIN:-}"
ACTIONLINT_IMAGE="${ACTIONLINT_IMAGE:-ghcr.io/rhysd/actionlint:latest}"
ACTIONLINT_ARGS=("-color")

run_local_actionlint() {
  local bin="$1"
  printf "%s\n" "Running actionlint via local binary: $bin"
  "$bin" "${ACTIONLINT_ARGS[@]}"
}

detect_engine() {
  if [[ -n "$ENGINE_BIN" ]]; then
    if ! command -v "$ENGINE_BIN" >/dev/null 2>&1; then
      printf "%s\n" "CONTAINER_ENGINE=$ENGINE_BIN が見つかりません" >&2
      exit 1
    fi
    return 0
  fi

  if command -v podman >/dev/null 2>&1; then
    ENGINE_BIN="podman"
    return 0
  fi

  if command -v docker >/dev/null 2>&1; then
    ENGINE_BIN="docker"
    return 0
  fi

  return 1
}

if [[ -n "$ACTIONLINT_BIN_OVERRIDE" ]]; then
  if ! command -v "$ACTIONLINT_BIN_OVERRIDE" >/dev/null 2>&1; then
    printf "%s\n" "ACTIONLINT_BIN=$ACTIONLINT_BIN_OVERRIDE が見つかりません" >&2
    exit 1
  fi
  run_local_actionlint "$ACTIONLINT_BIN_OVERRIDE"
  exit 0
fi

if command -v actionlint >/dev/null 2>&1; then
  run_local_actionlint "actionlint"
  exit 0
fi

if detect_engine; then
  printf "%s\n" "Running actionlint via $ENGINE_BIN image: $ACTIONLINT_IMAGE"
  set +e
  "$ENGINE_BIN" run --rm -t \
    -v "$(pwd)":/repo \
    -w /repo \
    "$ACTIONLINT_IMAGE" \
    "${ACTIONLINT_ARGS[@]}"
  rc=$?
  set -e

  if [[ "$rc" -eq 0 ]]; then
    exit 0
  fi

  printf "%s\n" "Container execution failed (exit=$rc)." >&2
  printf "%s\n" "If the image pull is denied (e.g. ghcr 403), set ACTIONLINT_BIN or install local 'actionlint'." >&2
  printf "%s\n" "Example: ACTIONLINT_BIN=/usr/local/bin/actionlint pnpm run lint:actions" >&2
  if command -v actionlint >/dev/null 2>&1; then
    printf "%s\n" "Fallback: running local actionlint from PATH." >&2
    run_local_actionlint "actionlint"
    exit 0
  fi
  exit "$rc"
else
  printf "%s\n" "Podman/Docker が見つかりません。コンテナ版 actionlint の利用を推奨します。" >&2
  printf "%s\n" "CI 上では rhysd/actionlint@v1 が実行されます。Podman もしくは Docker をインストールしてください。" >&2
  exit 1
fi
