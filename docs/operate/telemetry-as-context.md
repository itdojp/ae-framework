# Telemetry-as-Context（Trace Bundle v1）

運用テレメトリを `ae conformance verify` の入力へ接続するために、まず Trace Bundle を生成します。  
本ドキュメントは Issue #2287 の初期実装（ingest 基盤）を対象とします。

## 1. 目的

- ランタイムイベントを共通フォーマット `ae-trace-bundle/v1` に正規化する
- `traceId` 単位での集計情報を持つ
- 機微情報を redaction した状態で成果物を保存する

## 2. 入力フォーマット

`ae conformance ingest` は次のいずれかを受け付けます。

- NDJSON（1行1イベント）
- JSON配列（`[{...}, {...}]`）
- JSONオブジェクト（`{ "events": [...] }`）

各イベントは最低限、次のフィールドが必要です。

- `traceId`（string）
- `timestamp`（ISO-8601 date-time）
- `actor`（string）
- `event`（string）

## 3. 実行方法

```bash
ae-framework conformance ingest \
  --input artifacts/observability/runtime.ndjson \
  --output artifacts/observability/trace-bundle.json \
  --summary-output artifacts/observability/trace-bundle-summary.json \
  --source-env production \
  --source-service checkout-api \
  --sample-rate 1 \
  --redact '$.details.email:mask' \
  --redact '$.details.token:hash'
```

### redaction ルール

- 形式: `<jsonPath>:<action>`
- action: `remove | mask | hash`
- 対応パス: `$.a.b.c` のみ（配列ワイルドカードは未対応）

## 4. 生成物

- `artifacts/observability/trace-bundle.json`
  - スキーマ: `schema/trace-bundle.schema.json`
  - バージョン: `schemaVersion = ae-trace-bundle/v1`
- `artifacts/observability/trace-bundle-summary.json`
  - 取り込み件数、無効イベント件数、サンプリング件数、redaction件数を記録

## 5. 次段の利用

現状は以下の流れを推奨します。

1. `ae conformance ingest` で Trace Bundle を作成
2. 必要に応じて bundle 内の `events` を `ae conformance verify --input` に渡して検証
3. conformance 結果を CI artifacts として保存し、運用判断に利用
