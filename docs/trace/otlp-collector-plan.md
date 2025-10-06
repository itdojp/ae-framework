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
- [ ] **Stage 2 (本番)**: S3 (又は GCS) バケットに保存し、CI では presigned URL または OIDC 経由で取得。

### 認証・シークレット管理
- [ ] GitHub OIDC → AWS STS AssumeRole / GCP Workload Identity を採用し、個人 PAT に依存しない構成を提案。
- [ ] 失敗時フォールバックとして presigned URL / GitHub Artifact token を文書化。

### payload 仕様
- [x] フォーマット: OTLP JSON（`ResourceSpans`）→ `run-kvonce-conformance.sh` で NDJSON に変換。
- [ ] サイズ上限: 10 MB 以下を推奨。Collector 側でバッチ圧縮 (gzip) を行い、CI で展開するフローを設計。
- [ ] 保持期間: Stage1 は 14 日（Artifacts の既定値）、Stage2 は S3 Lifecycle (30 日) を想定。

### ダウンロードコマンド
- [x] `scripts/trace/fetch-otlp-payload.mjs` を追加し、`KVONCE_OTLP_PAYLOAD_FILE` / `KVONCE_OTLP_PAYLOAD_URL` が指定された場合に payload を取得して `KVONCE_OTLP_PAYLOAD` を再設定する。
- [ ] 取得後に SHA256 を記録し、`hermetic-reports/trace/kvonce-payload-metadata.json` を出力。

### プライバシー / PII
- [ ] Collector で `kvonce.event.value` などに含まれるユーザデータをフィルタ/マスクする正規化パイプラインを整備。
- [ ] マスキング方針を `docs/policies/trace-governance.md` (新規) にまとめ、Issue #1011 Step5 へリンク。

## 次ステップ
1. PoC: Collector → GitHub Artifacts へアップロード → `trace-conformance` ジョブで `actions/download-artifact` を利用して検証。
2. RFC 作成: 実環境導入フロー（Collector 設計、マスキング、Secrets 運用、失敗時ハンドリング）を 2025-10-W2 を目標にまとめる。
3. ロードマップ: 本ドキュメントの TODO を Issue #1011 Step3 と Issue #1012 Phase C のチェックリストに取り込み、フェーズ移行時に進捗を同期する。
