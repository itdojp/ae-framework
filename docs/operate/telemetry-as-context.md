---
docRole: ssot
lastVerified: '2026-03-23'
owner: observability-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# Telemetry-as-Context（Trace Bundle v1）

運用テレメトリを `ae conformance verify` の入力へ接続するために、まず Trace Bundle を生成します。  
本ドキュメントは Issue #2287 の初期実装（ingest 基盤）を対象とします。


## English

Telemetry is first normalized into a Trace Bundle before it is connected to `ae conformance verify`. This runbook documents the initial ingest foundation introduced for Issue #2287.

### 1. Purpose

- Normalize runtime events into the shared `ae-trace-bundle/v1` format
- Preserve trace-level aggregation keyed by `traceId`
- Store artifacts after redaction so sensitive fields do not leak into downstream evidence

### 2. Accepted input formats

`ae conformance ingest` accepts any of the following:

- NDJSON (one event per line)
- JSON array (`[{...}, {...}]`)
- JSON object (`{ "events": [...] }`)

Each event must provide at least the following fields:

- `traceId` (string)
- `timestamp` (ISO-8601 date-time)
- `actor` (string)
- `event` (string)

### 3. Ingest command

```bash
ae-framework conformance ingest   --input artifacts/observability/runtime.ndjson   --output artifacts/observability/trace-bundle.json   --summary-output artifacts/observability/trace-bundle-summary.json   --source-env production   --source-service checkout-api   --sample-rate 1   --redact '$.details.email:mask'   --redact '$.details.token:hash'
```

#### Redaction rules

- Format: `<jsonPath>:<action>`
- Supported actions: `remove | mask | hash`
- Supported path shape: `$.a.b.c` only; array wildcards are not supported

### 4. Generated artifacts

- `artifacts/observability/trace-bundle.json`
  - Schema: `schema/trace-bundle.schema.json`
  - Version: `schemaVersion = ae-trace-bundle/v1`
- `artifacts/observability/trace-bundle-summary.json`
  - Records ingest count, invalid event count, sampled event count, and redaction count
  - Schema: `schema/trace-bundle-summary.schema.json`
  - When zero events survive ingest, the unspecified side of `source.timeWindow` is backfilled with Unix epoch (`1970-01-01T00:00:00.000Z`)

### 5. Recommended downstream flow

Use the following sequence as the current baseline:

1. Run `ae conformance ingest` to build the Trace Bundle
2. Run `ae conformance verify --trace-bundle artifacts/observability/trace-bundle.json`
3. Convert failures into a CEGIS failure artifact with `ae fix from-conformance --input artifacts/conformance/conformance-results.json --output artifacts/fix/failures.json`
4. Continue with `ae fix analyze` / `ae fix apply` for the repair lane
5. Store conformance and fix artifacts as CI artifacts for operational review

### 6. GitHub Actions (self-heal lane)

`.github/workflows/runtime-conformance-self-heal.yml` executes the closed loop in the following order:

1. Prepare the Trace Bundle (skip ingest when `trace_bundle` is supplied)
2. Run `ae conformance verify --trace-bundle ...`
3. Run `ae fix from-conformance ...`
4. Run `ae fix apply ...` only when `apply_fixes=true`
5. Create an automatic PR when changes exist and `apply_fixes=true` with `dry_run=false`

#### Manual dispatch example

```bash
gh workflow run runtime-conformance-self-heal.yml   -f trace_input=samples/conformance/sample-traces.json   -f apply_fixes=true   -f dry_run=false
```

#### Main inputs

- `trace_input`: NDJSON/JSON path used for ingest
- `trace_bundle`: existing Trace Bundle path; skips ingest when supplied
- `conformance_rules`: optional custom rules JSON
- `apply_fixes`: run `ae fix apply` only when `true`
- `dry_run`: run `ae fix apply --dry-run` when `true`

#### Main outputs

- `artifacts/observability/runtime-self-heal-trace-bundle.json`
- `artifacts/conformance/runtime-self-heal-results.json`
- `artifacts/fix/runtime-self-heal-failures.json`
- `artifacts/automation/runtime-conformance-self-heal-report.json` (`ae-automation-report/v1`)

### 7. Security / PII handling

- Always pass `--redact` before ingesting traces so sensitive fields such as email, token, or session identifiers are removed.
- When production data is involved, store the Trace Bundle in encrypted storage and do not paste raw events into the PR body.
- During incident analysis, review `runtime-conformance-self-heal-report.json` and `runtime-self-heal-results.json` first, and only share the minimum necessary event excerpts.
- `artifacts/ci/harness-health.json` aggregates the `runtimeConformance` gate. When the status is `fail` or `warn`, rerun with `run-trace` (legacy name: `run-conformance`) and only enable `autopilot:on` when continuous operation is justified.

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

## 7. セキュリティ / PII 運用

- Trace取り込み前に `--redact` を必ず指定し、機微情報（例: email/token/sessionId）を除去する。
- 本番データを扱う場合、trace bundle は暗号化ストレージへ保管し、PR本文へ生データを貼り付けない。
- 失敗調査時は `runtime-conformance-self-heal-report.json` と `runtime-self-heal-results.json` を優先参照し、必要最小限の event 抜粋のみ共有する。
- `artifacts/ci/harness-health.json` に `runtimeConformance` ゲートが集約されるため、fail/warn 時は `run-trace`（旧表記: `run-conformance`）で再実行し、継続運用時のみ `autopilot:on` を付与する。
