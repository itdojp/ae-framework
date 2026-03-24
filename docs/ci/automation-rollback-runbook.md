---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Automation Rollback Runbook

This runbook explains how to return PR automation to safe manual operation. / この runbook は、PR 自動化を安全な手動運用へ戻す手順を定義します。

Primary sources / 一次情報:
- `scripts/ci/automation-rollback.sh`
- `scripts/ci/copilot-auto-fix.mjs`
- `scripts/ci/auto-merge-enabler.mjs`
- `scripts/ci/pr-self-heal.mjs`
- `scripts/ci/codex-autopilot-lane.mjs`

> Language / 言語: English | 日本語

---

## English

### 1. Scope and prerequisites

This runbook covers these automation lanes:
- `Copilot Auto Fix`
- `PR Maintenance`
- `PR Self-Heal`
- `Codex Autopilot Lane`

Prerequisites:
- `gh` CLI is available
- the operator can update repository variables for the target repository
- examples assume `itdojp/ae-framework`

### 2. One-command staged rollback

Use `scripts/ci/automation-rollback.sh` for staged rollback.

```bash
GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh '<mode>'
```

| mode | Purpose | Variables set |
| --- | --- | --- |
| `merge` | stop auto-merge related lanes only | `AE_AUTO_MERGE=0`, `AE_CODEX_AUTOPILOT_ENABLED=0` |
| `write` | temporarily stop bot write paths | `AE_AUTOMATION_GLOBAL_DISABLE=1` |
| `freeze` | keep all automation disabled until operators explicitly restore it | `write` + `AE_AUTO_MERGE=0`, `AE_CODEX_AUTOPILOT_ENABLED=0`, `AE_COPILOT_AUTO_FIX=0`, `AE_SELF_HEAL_ENABLED=0` |
| `unfreeze` | clear only the global kill-switch | `AE_AUTOMATION_GLOBAL_DISABLE=0` |

State check:

```bash
GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh status
```

Dry run:

```bash
AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh freeze
```

### 3. Standard label/comment rollback procedure

#### 3.1 Return a non-converging PR to manual mode

1. Inspect the `status:blocked` reason in the marker comment.
2. Repair conflicts or failed checks manually if needed.
3. Roll back labels.

```bash
gh issue edit <pr-number> --repo itdojp/ae-framework --remove-label status:blocked --remove-label ci-stability
```

4. Leave an operator record comment.

```md
<!-- AE-ROLLBACK-ACTION v1 -->
## Automation Rollback Action (<ISO8601>)
- PR: #<number>
- operator: <user>
- stage: <merge|write|freeze>
- reason: <why rollback was required>
- next: manual operation enabled
```

Keep rollback comments as continuity evidence instead of deleting them. Operators should treat `status:blocked` as an explicit signal that the automation path did not self-recover.

### 4. Representative incident recovery

#### 4.1 429 / secondary rate limit

1. Re-run failed jobs (`gh run rerun <runId> --failed` or GitHub UI `Re-run failed jobs`).
2. If the error repeats, tighten throttling variables:
   - `AE_GH_THROTTLE_MS`
   - `AE_GH_RETRY_MAX_ATTEMPTS`
   - `AE_GH_RETRY_INITIAL_DELAY_MS`
   - `AE_GH_RETRY_MAX_DELAY_MS`
   - `AE_GH_RETRY_MULTIPLIER`
   - `AE_GH_RETRY_JITTER_MS`
3. If the lane still does not converge, move to `write` or stronger rollback and continue in manual mode.

#### 4.2 review gate mismatch

1. Re-run the failed `Copilot Review Gate / gate` run for the affected SHA.
2. If necessary, trigger `workflow_dispatch` with `pr_number`.
3. Resolve remaining review threads before rerunning again.

#### 4.3 behind loop

1. Stop the update loop temporarily with `merge`.
2. Rebase or merge the PR branch manually.
3. Re-evaluate required checks, then restore automation only after the branch is stable.

#### 4.4 autopilot non-convergence

1. Inspect the latest `<!-- AE-CODEX-AUTOPILOT v1 -->` comment.
2. Confirm there is no in-flight `Copilot Review Gate` or `PR Maintenance` run.
3. Re-run `/autopilot run` after checks settle.
4. If the same symptom repeats, move to `write` and classify the cause with `docs/ci/codex-autopilot-lane.md`.

#### 4.5 trace required rollback

1. Review automation observability metrics and compare them with `docs/ci/trace-required-criteria.md`.
2. Temporarily switch branch protection to `branch-protection.main.verify-lite-noreview.json`.
3. Repair the failing `Spec Generate & Model Tests` cause.
4. Re-promote to `branch-protection.main.verify-lite-trace-noreview.json` only after the 28-day Go criteria are satisfied again.

#### 4.6 SLO / MTTR breach alert

1. Inspect `weekly-alert-summary.json` to confirm that the alert is not a false positive.
2. Verify thresholds and issue destination.
3. Use `weekly-failure-summary.json` to identify the dominant failure reasons.
4. If self-recovery still fails repeatedly, switch to `write` and continue manually.
5. After recovery, rerun the weekly workflow and confirm that `slo_breach` / `mttr_breach` clears.

### 5. Re-enable policy

- Use `unfreeze` first to clear the emergency stop.
- `write` can be reverted immediately by `unfreeze` because it only controls the global kill-switch.
- `freeze` keeps individual toggles at `0`, so operators must restore those variables explicitly after `unfreeze`.
- If rollback used the `merge` stage, explicitly restore `AE_AUTO_MERGE` and `AE_CODEX_AUTOPILOT_ENABLED` to the intended operating values before unattended operation resumes.
- Before re-enabling, confirm MTTR and current observability metrics in `docs/ci/automation-slo-mttr.md`.
- In trace-required operation, re-promote presets only when `docs/ci/trace-required-criteria.md` says Go.
- Restore variables in stages according to project policy, covering every toggle that rollback forced to `0`.
  - example: restore `AE_AUTOMATION_PROFILE=conservative` first, then re-enable `AE_AUTO_MERGE`, then restore `AE_CODEX_AUTOPILOT_ENABLED` and other per-lane toggles
- Immediately after recovery, watch `PR Maintenance` and `Copilot Review Gate`; if the same failure recurs, return to `write`.

### 6. Related documents

- `docs/ci/pr-automation.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/automation-alerting.md`
- `docs/ci/automation-slo-mttr.md`
- `docs/ci/trace-required-criteria.md`
- `docs/ci/automation-rollback-validation-2026-02-14.md`
- `docs/internal/autopilot-operations.md`

## 日本語

### 1. 前提

対象は以下の自動化レーンです。
- `Copilot Auto Fix`
- `PR Maintenance`
- `PR Self-Heal`
- `Codex Autopilot Lane`

前提条件:
- `gh` CLI が利用可能であること
- 対象リポジトリの Variables を更新できること
- 例では `itdojp/ae-framework` を対象とします

### 2. 1コマンド段階停止

`scripts/ci/automation-rollback.sh` で段階停止できます。

```bash
GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh '<mode>'
```

| mode | 目的 | 設定される Variables |
| --- | --- | --- |
| `merge` | 自動マージ系のみ停止 | `AE_AUTO_MERGE=0`, `AE_CODEX_AUTOPILOT_ENABLED=0` |
| `write` | bot 書き込み系を一時停止 | `AE_AUTOMATION_GLOBAL_DISABLE=1` |
| `freeze` | 全自動化を持続停止し、明示的な復帰操作まで無効を維持 | `write` + `AE_AUTO_MERGE=0`, `AE_CODEX_AUTOPILOT_ENABLED=0`, `AE_COPILOT_AUTO_FIX=0`, `AE_SELF_HEAL_ENABLED=0` |
| `unfreeze` | global kill-switch のみ解除 | `AE_AUTOMATION_GLOBAL_DISABLE=0` |

状態確認:

```bash
GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh status
```

dry-run:

```bash
AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh freeze
```

### 3. ラベル / コメント巻き戻し（標準手順）

#### 3.1 収束不能 PR を手動モードへ戻す

1. marker comment で `status:blocked` の原因を確認
2. 必要なら競合や failed checks を手動で修復
3. ラベルを巻き戻す

```bash
gh issue edit <pr-number> --repo itdojp/ae-framework --remove-label status:blocked --remove-label ci-stability
```

4. 運用記録 comment を残す

```md
<!-- AE-ROLLBACK-ACTION v1 -->
## Automation Rollback Action (<ISO8601>)
- PR: #<number>
- operator: <user>
- stage: <merge|write|freeze>
- reason: <why rollback was required>
- next: manual operation enabled
```

rollback comment は削除せず、連続した証跡として残します。`status:blocked` は「自動復旧不能」の明示信号として扱います。

### 4. 代表インシデントの復旧

#### 4.1 429 / secondary rate limit

1. failed jobs を rerun（`gh run rerun <runId> --failed` または GitHub UI の `Re-run failed jobs`）
2. 再発する場合は throttling 変数を強化
   - `AE_GH_THROTTLE_MS`
   - `AE_GH_RETRY_MAX_ATTEMPTS`
   - `AE_GH_RETRY_INITIAL_DELAY_MS`
   - `AE_GH_RETRY_MAX_DELAY_MS`
   - `AE_GH_RETRY_MULTIPLIER`
   - `AE_GH_RETRY_JITTER_MS`
3. それでも収束しない場合は `write` 以上で段階停止し、手動運用へ移行

#### 4.2 review gate mismatch

1. 該当 SHA の `Copilot Review Gate / gate` の failed run を rerun
2. 必要なら `workflow_dispatch` で `pr_number` を指定して再評価
3. unresolved thread が残る場合は resolve 後に再実行

#### 4.3 behind loop

1. `merge` で update loop を一時停止
2. PR ブランチを手動 rebase / merge で整合
3. required checks を再評価し、安定後に段階復帰

#### 4.4 autopilot non-convergence

1. `<!-- AE-CODEX-AUTOPILOT v1 -->` comment で最新 reason を確認
2. `Copilot Review Gate` / `PR Maintenance` の in-flight run が残っていないか確認
3. checks が落ち着いた後に `/autopilot run` を再実行
4. 同症状が連続する場合は `write` で一時停止し、`docs/ci/codex-autopilot-lane.md` で原因を切り分け

#### 4.5 trace required rollback

1. automation observability の集計値を確認し、`docs/ci/trace-required-criteria.md` と照合
2. branch protection を `branch-protection.main.verify-lite-noreview.json` へ一時切り戻し
3. `Spec Generate & Model Tests` の失敗要因を修正
4. 28 日観測の Go 基準を再充足した後に `branch-protection.main.verify-lite-trace-noreview.json` を再適用

#### 4.6 SLO / MTTR breach alert

1. `weekly-alert-summary.json` を確認し、誤検知でないことを判定
2. しきい値と通知先を確認
3. `weekly-failure-summary.json` から主要 failure reason を特定
4. 自動復旧が効かない場合は `write` で段階停止し、手動運用へ移行
5. 復旧後に週次 workflow を再実行し、`slo_breach` / `mttr_breach` の解消を確認

### 5. 復帰方針

- 緊急停止解除は `unfreeze` を先に実行
- `write` は global kill-switch だけを制御するため `unfreeze` で即時復帰可能
- `freeze` は `unfreeze` 後も個別 toggle が `0` のままなので、明示的に戻す必要がある
- `merge` 段階停止を使った場合は、無人運用へ戻す前に `AE_AUTO_MERGE` / `AE_CODEX_AUTOPILOT_ENABLED` を意図した運用値へ明示的に戻す
- 復帰前に `docs/ci/automation-slo-mttr.md` の MTTR 目標と最新 observability 指標を確認
- trace required 運用では `docs/ci/trace-required-criteria.md` が Go を示す場合のみ preset を再昇格
- project 方針に沿って、rollback で `0` にした変数を段階復帰
  - 例: `AE_AUTOMATION_PROFILE=conservative` を先に戻し、その後 `AE_AUTO_MERGE`、`AE_CODEX_AUTOPILOT_ENABLED`、他の lane 個別 toggle を順次再有効化
- 復帰直後は `PR Maintenance` / `Copilot Review Gate` を監視し、再発時は `write` へ戻す

### 6. 関連ドキュメント

- `docs/ci/pr-automation.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/automation-alerting.md`
- `docs/ci/automation-slo-mttr.md`
- `docs/ci/trace-required-criteria.md`
- `docs/ci/automation-rollback-validation-2026-02-14.md`
- `docs/internal/autopilot-operations.md`
