#!/usr/bin/env bash
set -euo pipefail

# actionlint をローカルで実行するユーティリティ
# 優先: Docker 版 → バイナリ直実行（未対応）

if command -v docker >/dev/null 2>&1; then
  echo "Running actionlint via Docker..."
  docker run --rm -t \
    -v "$(pwd)":/repo \
    -w /repo \
    ghcr.io/rhysd/actionlint:latest \
    -color
else
  echo "Docker が見つかりません。Docker 版 actionlint の利用を推奨します。"
  echo "CI 上では rhysd/actionlint@v1 が実行されます。ローカル実行には Docker をインストールしてください。"
  exit 1
fi

