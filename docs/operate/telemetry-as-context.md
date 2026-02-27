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
  - スキーマ: `schema/trace-bundle-summary.schema.json`
  - 取り込み後にイベントが 0 件の場合、`source.timeWindow` の未指定側は Unix epoch（`1970-01-01T00:00:00.000Z`）で補完

## 5. 次段の利用

現状は以下の流れを推奨します。

1. `ae conformance ingest` で Trace Bundle を作成
2. `ae conformance verify --trace-bundle artifacts/observability/trace-bundle.json` で検証
3. `ae fix from-conformance --input artifacts/conformance/conformance-results.json --output artifacts/fix/failures.json` で CEGIS failure artifact へ変換
4. `ae fix analyze/apply` に接続して修復レーンを実行
5. conformance / fix の成果物を CI artifacts として保存し、運用判断に利用

## 6. GitHub Actions（Self-Heal レーン）

`.github/workflows/runtime-conformance-self-heal.yml` は、以下の順で閉ループを実行します。

1. Trace Bundle 準備（`trace_bundle` 指定時は ingest をスキップ）
2. `ae conformance verify --trace-bundle ...`
3. `ae fix from-conformance ...`
4. `ae fix apply ...`（`apply_fixes=true` のときのみ）
5. 差分があれば自動PRを作成（`apply_fixes=true` かつ `dry_run=false`）

### 手動実行例

```bash
gh workflow run runtime-conformance-self-heal.yml \
  -f trace_input=samples/conformance/sample-traces.json \
  -f apply_fixes=true \
  -f dry_run=false
```

### 主な入力

- `trace_input`: ingest 元の NDJSON/JSON パス
- `trace_bundle`: 既存 trace bundle パス（指定時は ingest を省略）
- `conformance_rules`: 任意の custom rules JSON
- `apply_fixes`: `true` の場合のみ `ae fix apply` を実行
- `dry_run`: `true` の場合は `ae fix apply --dry-run`

### 出力

- `artifacts/observability/runtime-self-heal-trace-bundle.json`
- `artifacts/conformance/runtime-self-heal-results.json`
- `artifacts/fix/runtime-self-heal-failures.json`
- `artifacts/automation/runtime-conformance-self-heal-report.json`（`ae-automation-report/v1`）
