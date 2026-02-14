# Automation Rollback Runbook

PR 自動化を手動運用へ安全に戻すための runbook です。  
対象は `Copilot Auto Fix` / `PR Maintenance` / `PR Self-Heal` / `Codex Autopilot Lane` です。

一次情報:
- `scripts/ci/automation-rollback.sh`
- `scripts/ci/copilot-auto-fix.mjs`
- `scripts/ci/auto-merge-enabler.mjs`
- `scripts/ci/pr-self-heal.mjs`
- `scripts/ci/codex-autopilot-lane.mjs`

## 1. 前提

- `gh` CLI が利用可能で、対象リポジトリに Variables 更新権限があること
- 例ではリポジトリを `itdojp/ae-framework` とする

## 2. 1コマンド段階停止

`scripts/ci/automation-rollback.sh` で段階停止できます。

```bash
GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh <mode>
```

| mode | 目的 | 設定される Variables |
| --- | --- | --- |
| `merge` | 自動マージ系のみ停止 | `AE_AUTO_MERGE=0`, `AE_CODEX_AUTOPILOT_ENABLED=0` |
| `write` | bot書き込み系を一時停止 | `AE_AUTOMATION_GLOBAL_DISABLE=1` |
| `freeze` | 全自動化を持続停止（復帰後も無効を維持） | `write` + `AE_AUTO_MERGE=0`, `AE_CODEX_AUTOPILOT_ENABLED=0`, `AE_COPILOT_AUTO_FIX=0`, `AE_SELF_HEAL_ENABLED=0` |
| `unfreeze` | kill-switch解除のみ | `AE_AUTOMATION_GLOBAL_DISABLE=0` |

状態確認:

```bash
GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh status
```

dry-run:

```bash
AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh freeze
```

## 3. ラベル/コメント巻き戻し（標準手順）

### 3.1 収束不能PRを手動モードへ戻す

1. `status:blocked` の原因を PR コメント（marker）で確認
2. 必要なら競合/失敗チェックを手動で修復
3. ラベルを巻き戻す

```bash
gh issue edit <pr-number> --repo itdojp/ae-framework --remove-label status:blocked --remove-label ci-stability
```

4. 運用コメントを残す（テンプレ）

```md
<!-- AE-ROLLBACK-ACTION v1 -->
## Automation Rollback Action (<ISO8601>)
- PR: #<number>
- operator: <user>
- stage: <merge|write|freeze>
- reason: <why rollback was required>
- next: manual operation enabled
```

## 4. 代表インシデントの復旧

### 4.1 429 / secondary rate limit

1. 失敗runを `Re-run failed jobs`（または `gh run rerun <runId> --failed`）
2. 再発する場合はスロットリング変数を強化
   - `AE_GH_THROTTLE_MS`
   - `AE_GH_RETRY_MAX_ATTEMPTS`
   - `AE_GH_RETRY_INITIAL_DELAY_MS`
   - `AE_GH_RETRY_MAX_DELAY_MS`
3. それでも収束しない場合は `write` 以上で段階停止し、手動運用へ移行

### 4.2 review gate mismatch（同一SHAで gate が success/failure 混在）

1. 該当 SHA の `Copilot Review Gate / gate` の失敗runを rerun
2. 必要時は `workflow_dispatch`（`pr_number` 指定）で gate を再評価
3. unresolved thread が残る場合は Resolve 後に再実行

### 4.3 behind loop（update-branch が繰り返される）

1. 一時的に `merge` で自動更新ループを停止
2. PRブランチを手動 rebase/merge で整合
3. required checks を再評価し、安定後に段階復帰

## 5. 復帰方針

- 緊急停止解除は `unfreeze` を先に実行
- `write` は `unfreeze` で即時復帰可能（個別トグルは変更しない）
- `freeze` は `unfreeze` 後も個別トグルが `0` のため、必要変数を明示的に戻して復帰する
- その後、プロジェクト方針に沿って個別Variablesを段階復帰
  - 例: `AE_AUTOMATION_PROFILE=conservative` を基準に再設定
- 復帰直後は `PR Maintenance` / `Copilot Review Gate` の run を監視し、再発時は `write` へ戻す

## 6. 関連ドキュメント

- `docs/ci/pr-automation.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/automation-rollback-validation-2026-02-14.md`
- `docs/internal/autopilot-operations.md`
