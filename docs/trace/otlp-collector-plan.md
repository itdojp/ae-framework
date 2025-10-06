# OTLP Collector Integration Plan (Draft)

Issue: #1011 / #1012

## 背景
- KvOnce の trace-conformance ジョブは現在 `prepare-otlp-trace.mjs` を通じてサンプルまたはモック生成した OTLP payload を利用している。
- 実サービスの OTLP Exporter から収集したログを CI に取り込むため、Collector 構成とシークレット管理・アーティファクト受け渡し設計が必要。

## 想定アーキテクチャ
1. **Agent / Application** — OTLP HTTP/GRPC exporter で Collector に送信。Exporter 側では `kvonce.event.*` 属性を必ず付与する。
2. **Collector** — 受信した span を KvOnce 用の pipeline にルーティングし、フィルタリング後に専用ストレージへ保存。PoC 用の Docker Compose は `docker/otlp-tempo/` に配置。
3. **CI (trace-conformance job)** — `KVONCE_OTLP_PAYLOAD` で指定した payload をダウンロードし `prepare-otlp-trace.mjs` → `run-kvonce-conformance.sh` で projection / validation を実行。

## 方針と TODO

### Collector 出力先
- [x] **Stage 0 (現状)**: GitHub Actions でサンプル/モック payload を生成し `run-kvonce-conformance.sh` に直接渡す。
- [x] **Stage 1 (PoC)**: GitHub Actions Artifacts に Collector からアップロード → `actions/download-artifact` で取得（`kvonce_otlp_artifact` 入力でコンシューム可能）。
- [x] **Stage 2 (本番)**: S3 (又は GCS) バケットに保存し、CI では presigned URL または OIDC 経由で取得。
  - `scripts/trace/fetch-otlp-payload.mjs` が `KVONCE_OTLP_S3_URI`（例: `s3://bucket/key`）を受け取り、`@aws-sdk/client-s3` で取得する経路を追加。
  - MinIO / ローカル検証用に `KVONCE_OTLP_S3_MOCK_DIR` を指定すると、`<mockDir>/<bucket>/<key>` を直接読み込んでメタデータを生成。
  - 実S3接続時の構成変数：`KVONCE_OTLP_S3_REGION`、`KVONCE_OTLP_S3_ENDPOINT`、`KVONCE_OTLP_S3_FORCE_PATH_STYLE=true`、`KVONCE_OTLP_S3_USE_SSL=false`（任意）。
  - 残タスク: GitHub OIDC を利用した一時クレデンシャル取得、MinIO コンテナの docker-compose 化、失敗時フォールバックの再整理。

### 認証・シークレット管理
- [ ] GitHub OIDC → AWS STS AssumeRole / GCP Workload Identity を採用し、個人 PAT に依存しない構成を提案。
- [ ] 失敗時フォールバックとして presigned URL / GitHub Artifact token を文書化。

### payload 仕様
- [x] フォーマット: OTLP JSON（`ResourceSpans`）→ `run-kvonce-conformance.sh` で NDJSON に変換。
- [ ] サイズ上限: 10 MB 以下を推奨。Collector 側でバッチ圧縮 (gzip) を行い、CI で展開するフローを設計。
- [ ] 保持期間: Stage1 は 14 日（Artifacts の既定値）、Stage2 は S3 Lifecycle (30 日) を想定。

### ダウンロードコマンド
- [x] `scripts/trace/fetch-otlp-payload.mjs` を追加し、`KVONCE_OTLP_PAYLOAD_FILE` / `KVONCE_OTLP_PAYLOAD_URL` が指定された場合に payload を取得して `KVONCE_OTLP_PAYLOAD` を再設定する。
- [x] 取得後に SHA256 を記録し、`hermetic-reports/trace/kvonce-payload-metadata.json` を出力。
- [x] `KVONCE_OTLP_S3_URI` / `KVONCE_OTLP_S3_MOCK_DIR` 経由で S3/MinIO バケットを参照できるようにした（CI 実行時は OIDC 資格情報を使用、ローカル検証はモックディレクトリで代替）。

### プライバシー / PII
- [ ] Collector で `kvonce.event.value` などに含まれるユーザデータをフィルタ/マスクする正規化パイプラインを整備。
- [ ] マスキング方針を `docs/policies/trace-governance.md` (新規) にまとめ、Issue #1011 Step5 へリンク。

## 次ステップ
1. PoC: Collector → GitHub Artifacts へアップロード → `trace-conformance` ジョブで `actions/download-artifact` を利用して検証。（S3 URI 取得経路は実装済み、Artifacts 連携は継続）
2. RFC 作成: 実環境導入フロー（Collector 設計、マスキング、Secrets 運用、失敗時ハンドリング）を 2025-10-W2 を目標にまとめる。
3. ロードマップ: 本ドキュメントの TODO を Issue #1011 Step3 と Issue #1012 Phase C のチェックリストに取り込み、フェーズ移行時に進捗を同期する。

### Stage2 環境変数早見表

| 変数 | 役割 | 備考 |
| --- | --- | --- |
| `KVONCE_OTLP_S3_URI` | 取得対象の S3/MinIO URI (`s3://bucket/key`) | 省略時は CLI オプション `--s3-uri` を利用 |
| `KVONCE_OTLP_S3_REGION` | S3 クライアントのリージョン | 既定: `us-east-1` |
| `KVONCE_OTLP_S3_ENDPOINT` | MinIO などのカスタムエンドポイント | `https://` or `http://` を指定 |
| `KVONCE_OTLP_S3_FORCE_PATH_STYLE` | `true` でパススタイルを強制 | MinIO では `true` 推奨 |
| `KVONCE_OTLP_S3_USE_SSL` | `false` で TLS を無効化 | ローカル MinIO 用 |
| `KVONCE_OTLP_S3_MOCK_DIR` | ローカル検証/テスト用のモックディレクトリ | `<dir>/<bucket>/<key>` を直接読み込み |
| `KVONCE_OTLP_PAYLOAD_URL` | 事前署名 URL など HTTP 経由の取得 | Stage1/Artifacts 経路と互換 |


### Local MinIO PoC

- `./scripts/trace/run-minio-poc.sh` で `docker/trace-s3/docker-compose.yml` を起動し、MinIO に `samples/trace/kvonce-otlp.json` を投入できる。
- 実行後は以下の環境変数を設定すれば、CI と同じ S3 経路をローカルで検証できる。
  ```bash
  export AWS_ACCESS_KEY_ID=kvonce
  export AWS_SECRET_ACCESS_KEY=kvonce-secret
  export KVONCE_OTLP_S3_ENDPOINT=http://127.0.0.1:9000
  export KVONCE_OTLP_S3_URI=s3://kvonce-trace/kvonce-stage2/payload.json
  export KVONCE_OTLP_S3_USE_SSL=false
  export KVONCE_OTLP_S3_FORCE_PATH_STYLE=true
  ```
- コンテナ停止は `./scripts/trace/run-minio-poc.sh down`。MinIO コンソール (http://localhost:9001) では `kvonce` / `kvonce-secret` で確認できる。
