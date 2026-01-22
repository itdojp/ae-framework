# Flake Retry Dispatch（Phase 3）

## 目的
flake-detect で検知したフレークのうち、**再試行可否が true** のものだけを対象に
`rerun-failed-jobs` を実行する最小ディスパッチャ。

## 前提
- 対象は flake-detect の **run_attempt=1** の失敗ランのみ
- 再試行可否は `reports/flake-retry-eligibility.json` に記録される
- required check は自動再試行対象外

## 手動実行（workflow_dispatch）
Actions から `Flake Retry Dispatch (Phase 3)` を起動し、必要に応じて以下を指定する。

- `workflow_file`  
  既定: `flake-detect.yml`
- `eligibility_artifact`  
  既定: `flake-detection-report`

## 出力
Step Summary に以下が出力される。
- `workflow_file`
- `eligibility_artifact`
- `run_id`
- `retriable`
- `reason`

## 失敗時の代表的な原因
- eligibility アーティファクトが存在しない（`reason=no_artifact`）
- zip 展開に失敗（`reason=unzip_failed`）
- `retriable=false` のため再試行を実施しない
