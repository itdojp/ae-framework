---
docRole: ssot
lastVerified: '2026-03-26'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Flake Retry Dispatch (Phase 3)

> Language / 言語: English | 日本語

---

## English

A minimal dispatcher that runs `rerun-failed-jobs` only for flakes whose retry eligibility is `true` in `flake-detect`. The implementation is currently integrated into `flake-detect.yml` with `mode=retry`.

### Prerequisites

- Target only failed runs with `run_attempt=1` from the workflow specified by `workflow_file`.
- Retry eligibility is recorded in the JSON designated by `eligibility_path` (default: `reports/flake-retry-eligibility.json`).
- Required checks are out of scope for automatic retry.

### Manual execution (`workflow_dispatch`)

Run `Flake Stability Schedule` from Actions and set `mode=retry`.

Inputs:

- `workflow_file`
  - default: `flake-detect.yml`
  - examples: `verify-lite.yml` for Verify Lite, `pr-verify.yml` for PR Verify
- `eligibility_artifact`
  - default: `flake-detection-report`
  - examples: `verify-lite-report` for Verify Lite, `ae-artifacts` for PR Verify
- `eligibility_path`
  - default: `reports/flake-retry-eligibility.json`
  - examples: `artifacts/verify-lite/verify-lite-retry-eligibility.json` for Verify Lite, `artifacts/pr-verify/pr-verify-retry-eligibility.json` for PR Verify
  - restriction: rejects a leading `-` and wildcard characters (`*` / `?` / `[]`)
- `dry_run`
  - default: `false`
  - when `true`, `rerun-failed-jobs` is not executed

### Usage examples

- To inspect the result without rerunning:
  - set `mode=retry` and `dry_run=true`
- To use Verify Lite retry eligibility:
  - `mode=retry`
  - `workflow_file=verify-lite.yml`
  - `eligibility_artifact=verify-lite-report`
  - `eligibility_path=artifacts/verify-lite/verify-lite-retry-eligibility.json`
- To use PR Verify retry eligibility:
  - `mode=retry`
  - `workflow_file=pr-verify.yml`
  - `eligibility_artifact=ae-artifacts`
  - `eligibility_path=artifacts/pr-verify/pr-verify-retry-eligibility.json`

### Outputs

The Step Summary includes:

- `workflow_file`
- `eligibility_artifact`
- `eligibility_path`
- `dry_run`
- `run_id`
- `retriable`
- `reason`

### Representative failure reasons

- missing eligibility artifact (`reason=no_artifact`)
- zip extraction failed (`reason=unzip_failed`)
- eligibility JSON file exists but is empty (`reason=missing_file`)
- `eligibility_path` contains invalid characters (`reason=invalid_path`)
- failed to parse the eligibility JSON (`reason=parse_failed`)
- no retry performed because `retriable=false`

## 日本語

flake-detect で検知したフレークのうち、再試行可否が `true` のものだけを対象に `rerun-failed-jobs` を実行する最小ディスパッチャ。現在は `flake-detect.yml` の `mode=retry` に統合されている。

### 前提

- 対象は `workflow_file` で指定したワークフローの `run_attempt=1` の失敗ランのみ
- 再試行可否は `eligibility_path` で指定する JSON に記録される（既定: `reports/flake-retry-eligibility.json`）
- required check は自動再試行対象外

### 手動実行（`workflow_dispatch`）

Actions から `Flake Stability Schedule` を起動し、`mode=retry` を指定する。

入力:

- `workflow_file`
  - 既定: `flake-detect.yml`
  - 例: Verify Lite は `verify-lite.yml`、PR Verify は `pr-verify.yml`
- `eligibility_artifact`
  - 既定: `flake-detection-report`
  - 例: Verify Lite は `verify-lite-report`、PR Verify は `ae-artifacts`
- `eligibility_path`
  - 既定: `reports/flake-retry-eligibility.json`
  - 例: Verify Lite は `artifacts/verify-lite/verify-lite-retry-eligibility.json`、PR Verify は `artifacts/pr-verify/pr-verify-retry-eligibility.json`
  - 制約: 先頭 `-` とワイルドカード文字（`*` / `?` / `[]`）は拒否される
- `dry_run`
  - 既定: `false`
  - `true` の場合は `rerun-failed-jobs` を実行しない

### 使い方（例）

- rerun せず結果だけ確認する場合:
  - `mode=retry` と `dry_run=true` を指定する
- Verify Lite の retry eligibility を使う場合:
  - `mode=retry`
  - `workflow_file=verify-lite.yml`
  - `eligibility_artifact=verify-lite-report`
  - `eligibility_path=artifacts/verify-lite/verify-lite-retry-eligibility.json`
- PR Verify の retry eligibility を使う場合:
  - `mode=retry`
  - `workflow_file=pr-verify.yml`
  - `eligibility_artifact=ae-artifacts`
  - `eligibility_path=artifacts/pr-verify/pr-verify-retry-eligibility.json`

### 出力

Step Summary に以下が出力される。

- `workflow_file`
- `eligibility_artifact`
- `eligibility_path`
- `dry_run`
- `run_id`
- `retriable`
- `reason`

### 失敗時の代表的な原因

- eligibility artifact が存在しない（`reason=no_artifact`）
- zip 展開に失敗（`reason=unzip_failed`）
- eligibility JSON file が存在するが中身が空（`reason=missing_file`）
- `eligibility_path` に不正な文字が含まれる（`reason=invalid_path`）
- eligibility JSON の解析に失敗（`reason=parse_failed`）
- `retriable=false` のため再試行を実施しない
