# OTLP Collector Integration Plan (Draft)

Issue: #1011 / #1012

## 背景
- KvOnce の trace-conformance ジョブは現状 `prepare-otlp-trace.mjs` でサンプル/モック payload を生成し、`run-kvonce-conformance.sh` に流し込む構成になっている。
- 実サービスの OTLP Exporter から収集したログを CI に取り込むため、Collector 側での保存形式、Secrets 管理、CI 側でのダウンロード/検証フローを整理する必要がある。
- 2025-W40 までに Stage1 (Artifacts 経由の PoC) を完成させ、Stage2 以降でクラウドストレージ連携に移行する計画。

## 想定アーキテクチャ
1. **Agent / Application** — OTLP HTTP/gRPC exporter を用いて Collector へ span を送信。`kvonce.event.*` 属性を必須化。
2. **Collector** — フィルタリング後、KvOnce 専用 sink (GitHub Artifact / S3 / GCS) に JSON を保存。`kvonce.event.context` には `{attempts: number, region: string, ...}` を格納し retry 検証に活用する。
3. **CI (trace-conformance job)** — `KVONCE_OTLP_PAYLOAD` で指定したファイルを `prepare-otlp-trace.mjs` が展開し、`run-kvonce-conformance.sh` で OTLP / NDJSON の両モードを検証する。Step Summary/PR コメント/Check Run に結果を掲示。

## ステージング計画
| Stage | 目的 | 保存先 | 取得方法 |
|-------|------|--------|----------|
| 0 (現状) | サンプル/モックで pipeline を固定 | repo 内 sample/モック | `prepare-otlp-trace.mjs` が自動生成 |
| 1 (PoC) | Collector → GitHub Artifacts → CI | GitHub Actions Artifact (`kvonce-otlp-payload.json`) | `actions/download-artifact` → `KVONCE_OTLP_PAYLOAD` |
| 2 (本番) | クラウドストレージ経由で安定運用 | S3 or GCS (`kvonce-trace/YYYY/MM/DD/span.json.gz`) | OIDC AssumeRole / Workload Identity + presigned URL fallback |

## シークレットと環境変数
- `KVONCE_PAYLOAD_ARTIFACT`: Stage1 で利用する artifact 名 (例: `kvonce-collector-export`).
- `KVONCE_OTLP_PAYLOAD`: 展開先ローカルパス。trace-conformance ジョブでは同変数を `prepare-otlp-trace.mjs` が参照。
- `KVONCE_OTLP_PAYLOAD_URL`: Stage2 で presigned URL / S3 URL を渡す場合に利用。
- OIDC ロール候補: `ae-framework-kvonce-ci-reader` (S3) / `ae-framework-kvonce-ci-wi` (GCS)。Terraform で権限スコープを限定し、PII を含む payload にはアクセス制御ログを残す。

## payload 仕様
- フォーマット: OTLP JSON (ResourceSpans)。Collector 側で gzip 圧縮し、CI で展開する。
- サイズ上限: 10 MB 以下。上限を超える場合は Collector でバッチ分割し、CI 実行時間を 5 分以内に抑える。
- コンテキスト: retry を検証するため `kvonce.event.context` に `attempts` を必須とし、成功イベントは `attempts = retries + 1` を保証。
- メタデータ: 取得時に SHA256 / 取得元 URL / 生成時刻を `hermetic-reports/trace/kvonce-payload-metadata.json` に書き出し、Step Summary と PR コメントへ反映する。

## ダウンロード/展開フロー (案)
1. Stage1: `actions/download-artifact` で payload を取得 → `KVONCE_OTLP_PAYLOAD` に保存。
2. Stage2: 新規スクリプト `scripts/trace/fetch-otlp-payload.mjs` を追加し、`KVONCE_PAYLOAD_ARTIFACT` が未指定かつ `KVONCE_OTLP_PAYLOAD_URL` が指定されている場合に HTTP/S3/GCS からダウンロードする。
3. 展開後に `scripts/trace/run-kvonce-conformance.sh` を OTLP/NDJSON 両方で実行し、検証結果を Check Run へ投稿。

## プライバシー/PII 対応
- Collector で `kvonce.event.value` に個人情報が含まれる場合、マスキング/ハッシュ化を実施し、復号キーは保持しない。
- マスキングポリシーは新規ドキュメント `docs/policies/trace-governance.md` で管理し、Issue #1011 Step5 へリンク。
- CI にはマスク済みデータのみ渡し、原本は 30 日以内に自動削除。

## 残タスク
- [ ] Artifact 経由の PoC を実装し、`trace-conformance` ジョブの引数 (artifact 名・出力先) をワークフロー入力に追加する。
- [ ] `scripts/trace/fetch-otlp-payload.mjs` の実装とテスト。
- [ ] payload メタデータ出力と Step Summary への反映。
- [ ] retry context 仕様を README / schema に記載し、Collector 側でバリデーションする。
- [ ] Stage2 のインフラ設計 (S3/GCS、OIDC、Terraform) をまとめた RFC を 2025-10-W2 に提出。

## 次ステップ
1. PoC: Collector → GitHub Artifact → trace-conformance job (OTLP/NDJSON 両実行) の自動テストを構築。
2. RFC: Secrets 運用・マスキング・失敗時ハンドリング・監査ログ取得方針を整理し、レビューを依頼。
3. ロードマップ: 本ドキュメントのチェックボックスを Issue #1011 Step3 / Issue #1012 Phase C に取り込み、進捗を定期的に同期する。
