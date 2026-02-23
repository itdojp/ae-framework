# CI Troubleshooting Guide (Quick)

Purpose: Provide a short, deterministic path to diagnose common CI failures.

## 1) Identify the failing job
- Link the job in the PR or CI run summary
- Record the exact command and environment variables

## 2) Classify the failure
- **Lint/Type**: check `verify-lite` summary
- **Tests**: use `docs/testing/flaky-test-triage.md`
- **Artifacts/Codegen**: confirm `generate-artifacts` output
- **Security**: check label gating (`run-security`) and fork limitations

## 3) Reproduce locally (minimal)
- `pnpm run verify:lite`
- `pnpm run test:ci:lite`

## 4) Mitigate safely
- Prefer label-gated heavy suites (`docs/ci/label-gating.md`)
- Use stable profile for baseline (`docs/ci/stable-profile.md`)
- Document the fix and add a follow-up issue if needed

## 5) Automation notes
- Failed job は `ci-auto-rerun-failed` が **1回だけ**自動再実行します（再実行ログを確認）。
- `PR Self-Heal`（`pr-self-heal.yml`）を有効化している場合、review gate failure / 429起因失敗 / behind PR は自動復旧を試行します。収束しない場合は `status:blocked` + PRコメントで理由を残します。
- `pr-ci-status-comment`（PR Maintenance）が behind の PR を自動更新します。競合時は手動解決が必要です。
- `gateExpected` / `verify-liteExpected` が "Waiting for status to be reported" の場合、auto update で作られたマージコミットにチェックが載っていない可能性があります。対処: PRブランチに空コミットを追加してPRイベントを再発火、またはPR画面から再実行します。恒久策として `AE_AUTO_UPDATE_TOKEN` をSecretsに設定し、auto update の更新コミットから required checks が走るようにします。
- `Copilot Review Gate` の `pull_request_review` 実行が `action_required` でも、PR head SHA 上の `Copilot Review Gate / gate` が green ならマージ判定としては問題ありません。必要時は `workflow_dispatch`（`pr_number` 指定）で再実行します。
- `Copilot Review Gate / gate` が success/failure 混在のまま残る場合は、失敗した `Copilot Review Gate` ランを rerun します（`gh run rerun <runId> --failed`）。
- `Copilot Auto Fix` 後の gate 再評価は `agent-commands` が `issue_comment(created)` で `copilot-review-gate.yml` を dispatch します。再評価が起動しない場合は `agent-commands` の実行ログとコメント作成イベント（edited ではなく created）を確認してください。
- GitHub API の 429 / secondary rate limit が出る場合、Actions の rerun を優先します。`AE_GH_THROTTLE_MS` の既定は `250`（`0` で無効化）で、必要に応じて `AE_GH_RETRY_*` と合わせて調整します（詳細: `docs/ci/pr-automation.md` / 実装: `scripts/ci/lib/gh-exec.mjs`）。
- `pnpm run lint:actions` で `ghcr.io/rhysd/actionlint` pull が 403 の場合、`ACTIONLINT_BIN` でローカルバイナリを指定できます（例: `ACTIONLINT_BIN=/usr/local/bin/actionlint pnpm run lint:actions`）。
- `automation-observability-weekly` の通知判定は `weekly-alert-summary.json` に保存されます。通知が来ない場合は `suppressed` / `suppressedReason` を確認します。
- SLO/MTTR の判定基準は `docs/ci/automation-slo-mttr.md` を参照し、週次 artifact（`automation-observability-weekly`）で確認します。

## 6) 症状 → runbook 対応表

| 症状 | 一次確認 | runbook |
| --- | --- | --- |
| `Copilot Review Gate / gate` fail | 未解決レビューthread数、失敗runのconclusion | thread解消 → `gh run rerun <runId> --failed` |
| `PR Self-Heal` が `blocked` | PRコメントの reason、`status:blocked` ラベル | 競合解消/失敗チェック修復後に手動rerun |
| `auto-merge` が有効化されない | `AE_AUTO_MERGE*`、required checks、reviewDecision | `docs/ci/auto-merge.md` に沿って条件修正 |
| 429 / secondary rate limit | `gh-exec` retryログ、失敗タイミング | rerun優先、必要なら `AE_GH_THROTTLE_MS` と `AE_GH_RETRY_*` を調整 |

補足:
- 自動化系の共通JSON/Step Summary出力は `docs/ci/automation-observability.md` を参照。
- 通知条件/クールダウンは `docs/ci/automation-alerting.md` を参照。

## 7) 再実行手順（標準）

### 7.1 単一runの再実行（最優先）
- 失敗runが特定できる場合は `gh run rerun <runId> --failed` を優先
- runId の取得例:
  - `gh run list --branch <head-branch> --limit 20`
  - `gh run view <runId> --log-failed`

### 7.2 PR番号指定での手動起動
```bash
gh workflow run "Copilot Review Gate" -f pr_number=<PR番号>
gh workflow run "PR Self-Heal" -f pr_number=<PR番号> -f dry_run=false
gh workflow run "Codex Autopilot Lane" -f pr_number=<PR番号> -f dry_run=false
```

### 7.3 behind / stale checks の再同期
- `mergeStateStatus=BEHIND` の場合は update-branch を先に実行
  - `gh workflow run "PR Maintenance" -f mode=update-branch -f pr_number=<PR番号>`
- required check が古いコミットに残る場合:
  1. PRブランチに空コミットをpushして `pull_request` イベントを再発火
  2. 必要なら `gate` / `verify-lite` を rerun

## 8) 失敗時の切り分け（5分版）

1. **分類**: 失敗jobが `quality` / `security` / `automation` のどれかを確定  
2. **原因粒度**: `設定不足`（label/env/permission）か `実装不具合` かを分離  
3. **再現性**: `pnpm run verify:lite` でローカル再現するか確認  
4. **API制限**: 429系なら run rerun を優先し、`AE_GH_THROTTLE_MS` を段階的に上げる  
5. **停止判断**: 同一症状が連続する場合は kill-switch で自動実行を一時停止

## 9) 緊急回避（Fail-safe）

- 即時停止:
  - Repository Variable `AE_AUTOMATION_GLOBAL_DISABLE=1`
  - 影響: PR Maintenance（update-branch / enable-auto-merge）/ auto-fix / auto-merge / self-heal / autopilot を skip
- 部分停止:
  - `AE_CODEX_AUTOPILOT_ENABLED=0`
  - `AE_SELF_HEAL_ENABLED=0`
  - `AE_COPILOT_AUTO_FIX=0`
- 復帰手順:
  1. 根本原因を修正（permission / env / workflow設定）
  2. `AE_AUTOMATION_GLOBAL_DISABLE=0` へ戻す
  3. 対象workflowを `workflow_dispatch` で段階的に再開

## 10) 変更記録（運用ルール）

- 失敗と復旧の実施内容は、PRコメントまたはIssueコメントに必ず残す
- 記録必須項目:
  - 発生時刻（UTC）
  - 失敗workflow/job名
  - 実施した rerun / dispatch / env変更
  - 再発防止策（あればPR番号）

## References
- `docs/ci/ci-baseline-checklist.md`
- `docs/ci/automation-observability.md`
- `docs/ci/automation-alerting.md`
- `docs/ci/automation-failure-policies.md`
- `docs/ci/automation-slo-mttr.md`
- `docs/testing/test-categorization.md`
- `docs/testing/flaky-test-triage.md`
