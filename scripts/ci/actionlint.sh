#!/usr/bin/env bash
set -euo pipefail

# actionlint をローカルで実行するユーティリティ
# 優先: Podman → Docker → エラー

ENGINE_BIN="${CONTAINER_ENGINE:-}"

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

if detect_engine; then
  printf "%s\n" "Running actionlint via $ENGINE_BIN..."
  "$ENGINE_BIN" run --rm -t \
    -v "$(pwd)":/repo \
    -w /repo \
    ghcr.io/rhysd/actionlint:latest \
    -color
else
  printf "%s\n" "Podman/Docker が見つかりません。コンテナ版 actionlint の利用を推奨します。" >&2
  printf "%s\n" "CI 上では rhysd/actionlint@v1 が実行されます。Podman もしくは Docker をインストールしてください。" >&2
  exit 1
fi
