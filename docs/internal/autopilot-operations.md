# Autopilot Operations Runbook

## 目的

`Codex Autopilot Lane` を中心とした PR 自動化を、安全に停止・復帰するための運用手順を定義する。

対象 workflow:
- `.github/workflows/codex-autopilot-lane.yml`
- `.github/workflows/pr-self-heal.yml`
- `.github/workflows/pr-ci-status-comment.yml`
- `.github/workflows/copilot-auto-fix.yml`

## 運用原則

- fail-closed を基本とし、未収束PRは `status:blocked` で明示停止する
- 停止/復帰は Repository Variables を一次制御面として扱う
- 復旧時は必ず marker 付きコメントと run URL を証跡として残す

## 段階停止（推奨）

`scripts/ci/automation-rollback.sh` を使用する。

```bash
GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh <merge|write|freeze>
```

- `merge`: auto-merge 系のみ停止
- `write`: bot の書き込み系を停止
- `freeze`: `AE_AUTOMATION_GLOBAL_DISABLE=1` で全自動化を停止

状態確認:

```bash
GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh status
```

## 復帰手順

1. `unfreeze` で global kill-switch を解除
2. 収束済みPRから段階的にラベル巻き戻し（`status:blocked` 除去）
3. `Copilot Review Gate` / `PR Maintenance` / `Codex Autopilot Lane` のrunを監視
4. 再発があれば直ちに `write` へ戻す

```bash
GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh unfreeze
```

## ラベル運用（最小）

- 主要制御:
  - `autopilot:on`（lane opt-in）
  - `status:blocked`（未収束停止）
  - `ci-stability`（CI復旧対象）
- 手動巻き戻し:

```bash
gh issue edit <pr-number> --repo itdojp/ae-framework --remove-label status:blocked --remove-label ci-stability
```

## 監視観点

- `ae-automation-report/v1` の `status` / `reason` を最優先で確認
- 代表障害:
  - 429 / secondary rate limit
  - review gate mismatch
  - behind loop
- 詳細 runbook は `docs/ci/automation-rollback-runbook.md` を参照

## 参照

- `docs/ci/pr-automation.md`
- `docs/ci/automation-rollback-runbook.md`
