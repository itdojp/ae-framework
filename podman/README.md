# Podman Assets

Podman で `ae-framework` を起動／検証するためのコンテナ定義です。

## ファイル構成

- `Dockerfile` : ランタイム用マルチステージビルド
- `Dockerfile.test` : CI / テスト実行用の依存入りイメージ
- `compose.dev.yaml` : 開発環境用 Podman Compose
- `compose.prod.yaml` : セキュリティ強化済みの本番想定 Compose
- `compose.test.yaml` : テストジョブ向け Compose

## 使い方

```bash
# 開発（ホットリロード）
podman compose -f podman/compose.dev.yaml up --build

# 本番シミュレーション
podman compose -f podman/compose.prod.yaml up --build -d

# テスト用
podman compose -f podman/compose.test.yaml run --rm tests

# スモークテスト（ビルドと Compose 検証）
pnpm podman:smoke
```

必要に応じて `CONTAINER_ENGINE=podman` を指定することで、
`scripts/docker/analyze-optimization.sh` からも Podman を利用できます。
