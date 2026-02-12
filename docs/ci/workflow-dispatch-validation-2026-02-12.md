# Workflow Dispatch Validation Report (2026-02-12)

## 1. 概要

- 目的: `workflow_dispatch` 経路で主要自動化Workflowが正常に実行できることを確認
- 実施日: 2026-02-12 (UTC)
- 実施リビジョン: `main@8bfd307d070e3d3e30a94595f1ea23790926c30e`
- 実施環境:
  - `gh version 2.45.0`
  - `node v22.19.0`
  - `pnpm 10.0.0`

## 2. 実行結果サマリ

| Workflow | Run ID | Inputs | Conclusion | URL |
| --- | ---: | --- | --- | --- |
| Copilot Review Gate (`copilot-review-gate.yml`) | `21966733776` | なし | `success` | https://github.com/itdojp/ae-framework/actions/runs/21966733776 |
| PR Self-Heal (`pr-self-heal.yml`) | `21966754908` | `dry_run=true`, `max_rounds=1` | `success` | https://github.com/itdojp/ae-framework/actions/runs/21966754908 |
| PR Maintenance (`pr-ci-status-comment.yml`) | `21966769997` | `mode=status` | `success` | https://github.com/itdojp/ae-framework/actions/runs/21966769997 |
| Codex Autopilot Lane (`codex-autopilot-lane.yml`) | `21966787351` | `pr_number=1953`, `dry_run=true`, `max_rounds=1` | `success` | https://github.com/itdojp/ae-framework/actions/runs/21966787351 |

## 3. ジョブレベル結果（抜粋）

### 3.1 Copilot Review Gate (`21966733776`)

- `gate`: `success`
- `dispatch`: `skipped`（`workflow_dispatch` 実行のため想定どおり）

### 3.2 PR Self-Heal (`21966754908`)

- `self-heal`: `success`（`dry_run=true` で副作用なし）

### 3.3 PR Maintenance (`21966769997`)

- `post-status`: `success`
- `enable-auto-merge` / `check-auto-merge` / `update-branch` / `label` / `summarize`: `skipped`（`mode=status` 指定のため想定どおり）

### 3.4 Codex Autopilot Lane (`21966787351`)

- `autopilot`: `success`（`dry_run=true` で副作用なし）

## 4. 判定

- `workflow_dispatch` 経路での主要4Workflowは、指定入力で正常終了した。
- `dry_run` 実行（Self-Heal / Autopilot）により、運用検証時の副作用を抑制できることを確認した。

## 5. 再実行コマンド

```bash
# Copilot Review Gate
gh workflow run copilot-review-gate.yml --repo itdojp/ae-framework --ref main

# PR Self-Heal (dry-run)
gh workflow run pr-self-heal.yml --repo itdojp/ae-framework --ref main -f dry_run=true -f max_rounds=1

# PR Maintenance (status mode)
gh workflow run pr-ci-status-comment.yml --repo itdojp/ae-framework --ref main -f mode=status

# Codex Autopilot Lane (dry-run)
gh workflow run codex-autopilot-lane.yml --repo itdojp/ae-framework --ref main -f pr_number=1953 -f dry_run=true -f max_rounds=1
```

