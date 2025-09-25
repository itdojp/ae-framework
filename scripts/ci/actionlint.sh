#!/usr/bin/env bash
set -euo pipefail

# actionlint をローカルで実行するユーティリティ
# 優先: Docker 版 → バイナリ直実行（未対応）

# Always run the printf/quoting guard first
bash scripts/ci/guard-github-outputs.sh

if command -v docker >/dev/null 2>&1; then
  printf "%s\n" "Running actionlint via Docker..."
  docker run --rm -t \
    -v "$(pwd)":/repo \
    -w /repo \
    ghcr.io/rhysd/actionlint:latest \
    -color
else
  printf "%s\n" "(info) Docker が見つかりません。ローカルでは guard のみ実行しました。" >&2
  printf "%s\n" "(info) CI 上では rhysd/actionlint@v1 が実行されます。Docker をインストールするとローカルでも actionlint 実行可。" >&2
fi
