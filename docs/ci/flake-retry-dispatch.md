# Flake Retry Dispatch（Phase 3）

## 目的
flake-detect で検知したフレークのうち、**再試行可否が true** のものだけを対象に
`rerun-failed-jobs` を実行する最小ディスパッチャ。

## 前提
- 対象は `workflow_file` で指定したワークフローの **run_attempt=1** の失敗ランのみ
- 再試行可否は `eligibility_path` で指定する JSON に記録される（既定: `reports/flake-retry-eligibility.json`）
- required check は自動再試行対象外

## 手動実行（workflow_dispatch）
Actions から `Flake Retry Dispatch (Phase 3)` を起動し、必要に応じて以下を指定する。

- `workflow_file`  
  既定: `flake-detect.yml`（例: verify-lite は `verify-lite.yml` / pr-verify は `pr-verify.yml`）
- `eligibility_artifact`  
  既定: `flake-detection-report`（例: verify-lite は `verify-lite-report` / pr-verify は `ae-artifacts`）
- `eligibility_path`  
  既定: `reports/flake-retry-eligibility.json`  
  例: verify-lite は `artifacts/verify-lite/verify-lite-retry-eligibility.json` / pr-verify は `artifacts/pr-verify/pr-verify-retry-eligibility.json`
  制約: 先頭 `-` やワイルドカード（`*`/`?`/`[]`）は拒否される
- `dry_run`  
  既定: `false`（true の場合は rerun-failed-jobs を実行しない）

## 使い方（例）
- dry-run で結果だけ確認する場合:
  - `dry_run=true` にして実行
- verify-lite の retry eligibility を使う場合:
  - `workflow_file=verify-lite.yml`
  - `eligibility_artifact=verify-lite-report`
  - `eligibility_path=artifacts/verify-lite/verify-lite-retry-eligibility.json`
- pr-verify の retry eligibility を使う場合:
  - `workflow_file=pr-verify.yml`
  - `eligibility_artifact=ae-artifacts`
  - `eligibility_path=artifacts/pr-verify/pr-verify-retry-eligibility.json`

## 出力
Step Summary に以下が出力される。
- `workflow_file`
- `eligibility_artifact`
- `eligibility_path`
- `dry_run`
- `run_id`
- `retriable`
- `reason`

## 失敗時の代表的な原因
- eligibility アーティファクトが存在しない（`reason=no_artifact`）
- zip 展開に失敗（`reason=unzip_failed`）
- eligibility JSON ファイルが存在するが中身が空（`reason=missing_file`）
- `eligibility_path` に不正な文字が含まれる（`reason=invalid_path`）
- eligibility JSON の解析に失敗（`reason=parse_failed`）
- `retriable=false` のため再試行を実施しない
