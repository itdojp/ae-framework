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
  既定: `flake-detect.yml`（例: verify-lite の場合は `verify-lite.yml`）
- `eligibility_artifact`  
  既定: `flake-detection-report`（例: verify-lite の場合は `verify-lite-report`）
- `eligibility_path`  
  既定: `reports/flake-retry-eligibility.json`  
  例: verify-lite の場合は `artifacts/verify-lite/verify-lite-retry-eligibility.json`
- `dry_run`  
  既定: `false`（true の場合は rerun-failed-jobs を実行しない）

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
- `retriable=false` のため再試行を実施しない
