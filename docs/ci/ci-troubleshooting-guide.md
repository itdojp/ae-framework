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
- GitHub API の 429 / secondary rate limit が出る場合、Actions の rerun を優先します。`AE_GH_THROTTLE_MS` の既定は `250`（`0` で無効化）で、必要に応じて `AE_GH_RETRY_*` と合わせて調整します（詳細: `docs/ci/pr-automation.md` / 実装: `scripts/ci/lib/gh-exec.mjs`）。
- `pnpm run lint:actions` で `ghcr.io/rhysd/actionlint` pull が 403 の場合、`ACTIONLINT_BIN` でローカルバイナリを指定できます（例: `ACTIONLINT_BIN=/usr/local/bin/actionlint pnpm run lint:actions`）。

## 6) 症状 → runbook 対応表

| 症状 | 一次確認 | runbook |
| --- | --- | --- |
| `Copilot Review Gate / gate` fail | 未解決レビューthread数、失敗runのconclusion | thread解消 → `gh run rerun <runId> --failed` |
| `PR Self-Heal` が `blocked` | PRコメントの reason、`status:blocked` ラベル | 競合解消/失敗チェック修復後に手動rerun |
| `auto-merge` が有効化されない | `AE_AUTO_MERGE*`、required checks、reviewDecision | `docs/ci/auto-merge.md` に沿って条件修正 |
| 429 / secondary rate limit | `gh-exec` retryログ、失敗タイミング | rerun優先、必要なら `AE_GH_THROTTLE_MS` と `AE_GH_RETRY_*` を調整 |

補足:
- 自動化系の共通JSON/Step Summary出力は `docs/ci/automation-observability.md` を参照。

## References
- `docs/ci/ci-baseline-checklist.md`
- `docs/ci/automation-observability.md`
- `docs/testing/test-categorization.md`
- `docs/testing/flaky-test-triage.md`
