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

## 本番シークレットと内部ポート

`podman/compose.prod.yaml` は本番相当の実行を想定しており、サンプルのデータベース認証情報を含めません。スタック起動前に、PostgreSQL の値を外部シークレットソースから設定してください。

```bash
export POSTGRES_USER='ae_framework_app'
export POSTGRES_PASSWORD="$(cat /path/to/secret/postgres-password)"
export POSTGRES_DB='ae_framework'
podman compose -f podman/compose.prod.yaml up --build -d
```

推奨運用:

- シークレットファイルはリポジトリ外に配置し、`0600` など所有者のみが読める権限にする。
- デプロイホストまたは運用者認証情報の露出が疑われる場合は `POSTGRES_PASSWORD` をローテーションする。
- サンプル認証情報は `compose.dev.yaml` のみに置く。
- `db` と `otel` は Compose 内部ネットワークに留める。診断目的でホストからのアクセスが必要な場合は、`127.0.0.1` に bind する明示的な operator override を別途用意し、firewall / authentication control を文書化する。
