# #2409 Local Stack Foundation PoC 手順

## 目的

`#2409 second slice (owner: local stack foundation)` の担当範囲として、NATS + PostgreSQL + S3互換ストレージ(MinIO)の最小ローカル検証環境を提供する。

## スコープ

- 対象: ローカル開発端末での起動確認、停止確認、基本疎通確認
- 非対象: 本番相当の耐障害設定、負荷計測、長期運用パラメータ最適化  
  （詳細な比較分析は `#2414` 側 PoC docs のスコープ）

## 構成ファイル

- Compose定義: `infra/poc/stack/docker-compose.yml`
- 環境変数サンプル: `infra/poc/stack/.env.example`
- 比較記録テンプレート: `docs/infra/local-stack-foundation-measurement-template.md`
- 比較記録の配置先ガイド: `docs/infra/poc-records/local-stack/README.md`

## 前提条件

- Docker Engine / Docker Desktop が利用可能
- Docker Compose v2 (`docker compose`) が利用可能
- 疎通確認用に `curl` が利用可能

## ポートと永続ボリューム

| Service | Container Port | Host Port (default) | Persistent Volume |
| --- | --- | --- | --- |
| NATS | 4222 (client), 8222 (monitor) | 14222, 18222 | `nats-data` |
| PostgreSQL | 5432 | 15432 | `postgres-data` |
| MinIO | 9000 (API), 9001 (console) | 19000, 19001 | `minio-data` |

> 既存ローカル環境との衝突を避けるため、デフォルトは高番ポートを採用している。必要に応じて `infra/poc/stack/.env` で変更する。

## 起動手順

```bash
cd infra/poc/stack
cp .env.example .env
docker compose up -d
docker compose ps
```

`minio-init` は one-shot 初期化コンテナで、指定バケットを作成後に終了する。

## 疎通確認手順

```bash
cd infra/poc/stack
set -a; . ./.env; set +a

# NATS monitor endpoint
curl -fsS "http://localhost:${NATS_MONITOR_PORT}/healthz" && echo

# PostgreSQL query
docker compose exec -T postgres \
  psql -U "${POSTGRES_USER}" -d "${POSTGRES_DB}" -c "select now();"

# MinIO live endpoint
curl -fsS "http://localhost:${MINIO_API_PORT}/minio/health/live" && echo

# MinIO bootstrap log (bucket作成確認)
docker compose logs --no-color minio-init
```

## 停止・クリーンアップ

```bash
cd infra/poc/stack

# コンテナ/ネットワークのみ停止
docker compose down

# 永続ボリュームも含めて削除
docker compose down --volumes --remove-orphans
```

## 静的確認（Compose解決結果）

```bash
# Docker Compose が使える環境
docker compose -f infra/poc/stack/docker-compose.yml config

# Docker が使えない環境での代替（Podman Compose）
podman-compose -f infra/poc/stack/docker-compose.yml config
```

`config` が成功すれば、環境変数展開後の Compose 定義が構文的に解決できていることを確認できる。

## 注意点

- 認証情報はPoC向け固定値（`ae_local` 系）であり、開発専用。
- CI用途や共有環境へのそのまま適用は想定していない。
- `minio-init` は再実行可能だが、運用用途のアクセス制御・暗号化設定は未実装。

## 比較計測の最小導線

1. `docs/infra/local-stack-foundation-measurement-template.md` をコピー
2. `docs/infra/poc-records/local-stack/YYYYMMDD-<owner>.md` に保存
3. 同一条件での再計測時は同ファイルに追記して差分比較

本導線は「起動時間・疎通可否・基本メトリクス記録」の最小範囲に限定する。高度な計測設計や評価軸の拡張は `#2414` のPoC docs側で管理する。
