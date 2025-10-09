#!/bin/bash
#
# Podman Image Analysis and Optimization Validator
#

set -euo pipefail

ENGINE_BIN="${CONTAINER_ENGINE:-}"
if [[ -z "$ENGINE_BIN" ]]; then
  if command -v podman >/dev/null 2>&1; then
    ENGINE_BIN="podman"
  elif command -v docker >/dev/null 2>&1; then
    ENGINE_BIN="docker"
  else
    echo "❌ Podman/Docker が利用できません"
    exit 1
  fi
fi

IMAGE_NAME=${IMAGE_NAME:-ae-framework}
TAG="${1:-latest}"
FULL_IMAGE_NAME="${IMAGE_NAME}:${TAG}"
DOCKERFILE_PATH="podman/Dockerfile"

log_section() {
  echo
  echo "==========================================="
  echo "$1"
  echo "==========================================="
}

check_engine() {
  if ! command -v "$ENGINE_BIN" >/dev/null 2>&1; then
    echo "❌ $ENGINE_BIN が PATH にありません"
    exit 1
  fi
  if ! "$ENGINE_BIN" info >/dev/null 2>&1; then
    echo "❌ $ENGINE_BIN デーモンが起動していません"
    exit 1
  fi
  echo "✅ $ENGINE_BIN を使用します"
}

ensure_image_exists() {
  if ! "$ENGINE_BIN" image inspect "$FULL_IMAGE_NAME" >/dev/null 2>&1; then
    echo "🔨 $FULL_IMAGE_NAME が存在しないためビルドします"
    "$ENGINE_BIN" build -t "$FULL_IMAGE_NAME" -f "$DOCKERFILE_PATH" .
  else
    echo "✅ $FULL_IMAGE_NAME が既に存在します"
  fi
}

analyze_size() {
  log_section "📏 イメージサイズ分析"
  local image_size size_mb
  image_size=$("$ENGINE_BIN" image inspect "$FULL_IMAGE_NAME" --format='{{.Size}}')
  size_mb=$((image_size / 1024 / 1024))
  echo "イメージサイズ: ${size_mb}MB"
  "$ENGINE_BIN" history "$FULL_IMAGE_NAME" --format "table {{.CreatedBy}}\t{{.Size}}" | head -12
}

analyze_layers() {
  log_section "🔍 レイヤー分析"
  local layer_count
  layer_count=$("$ENGINE_BIN" history "$FULL_IMAGE_NAME" --quiet | wc -l)
  echo "レイヤー数: $layer_count"
}

test_security() {
  log_section "🔒 セキュリティチェック"
  local user_check shell_check
  user_check=$("$ENGINE_BIN" run --rm "$FULL_IMAGE_NAME" whoami 2>/dev/null || echo "root")
  echo "実行ユーザー: $user_check"
  shell_check=$("$ENGINE_BIN" run --rm "$FULL_IMAGE_NAME" which sh 2>/dev/null || echo "なし")
  echo "シェル有無: $shell_check"
}

test_runtime() {
  log_section "🚀 起動確認"
  local host_port container_id
  host_port=$(python3 -c "import socket; s=socket.socket(); s.bind(('', 0)); print(s.getsockname()[1]); s.close()" 2>/dev/null || echo "3001")
  container_id=$("$ENGINE_BIN" run -d --rm -p "${host_port}:3000" "$FULL_IMAGE_NAME" 2>/dev/null || echo "failed")
  if [[ "$container_id" == "failed" ]]; then
    echo "❌ 起動に失敗しました"
    return 1
  fi
  echo "コンテナID: $container_id"
  sleep 5
  if curl -f "http://localhost:${host_port}/health" >/dev/null 2>&1; then
    echo "✅ ヘルスチェック成功"
  else
    echo "ℹ️ ヘルスエンドポイントが応答しません"
  fi
  "$ENGINE_BIN" stop "$container_id" >/dev/null 2>&1 || true
}

analyze_fs() {
  log_section "📦 依存関係/ファイル確認"
  local node_modules_count src_count
  node_modules_count=$("$ENGINE_BIN" run --rm "$FULL_IMAGE_NAME" sh -c "find /app/node_modules -name package.json 2>/dev/null | wc -l" || echo "0")
  echo "node_modules (prod): $node_modules_count"
  src_count=$("$ENGINE_BIN" run --rm "$FULL_IMAGE_NAME" sh -c "find /app -name '*.ts' 2>/dev/null | wc -l" || echo "0")
  echo "TypeScript ファイル数: $src_count"
}

main() {
  echo "🐳 Podman Image Analysis for ae-framework"
  check_engine
  ensure_image_exists
  analyze_size
  analyze_layers
  test_security
  test_runtime
  analyze_fs
  log_section "✅ 分析完了"
}

trap 'echo "❌ 実行中にエラーが発生しました (line $LINENO)"' ERR
main "$@"
