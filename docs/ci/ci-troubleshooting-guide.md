---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# CI Troubleshooting Guide (Quick)

> Language / 言語: English | 日本語

---

## English

Last updated: 2026-03-24

Purpose: provide a short, deterministic path to diagnose common CI failures and choose the correct rerun or remediation path.

### 1. Identify the failing job

- Link the failing job from the PR page or CI summary.
- Record the exact command, workflow name, job name, head SHA, and relevant environment variables.

### 2. Classify the failure

- **Lint / type**: inspect the `verify-lite` summary first.
- **Lockfile**: inspect `ERR_PNPM_LOCKFILE_CONFIG_MISMATCH` or `pnpm install --frozen-lockfile` failures, then compare `pnpm-lock.yaml` with the current pnpm install settings.
- **Tests**: use `docs/testing/flaky-test-triage.md`.
- **Artifacts / code generation**: confirm `generate-artifacts` outputs and expected report paths.
- **Security / policy**: confirm label gating such as `run-security`, fork limitations, and required-label policy in `policy/risk-policy.yml`.

### 3. Reproduce locally (minimal)

- `pnpm install --frozen-lockfile`
- `pnpm run verify:lite`
- `pnpm run test:ci:lite`

### 4. Mitigate safely

- Prefer label-gated heavy suites. See `docs/ci/label-gating.md`.
- Use the stable profile as the baseline. See `docs/ci/stable-profile.md`.
- Document the fix and create a follow-up issue when the immediate remediation is intentionally narrow.

### 5. Automation notes

- `ci-auto-rerun-failed` retries a failed job only once. Inspect the rerun log before taking further action.
- When `PR Self-Heal` (`pr-self-heal.yml`) is enabled, it attempts recovery for review gate failures, 429-triggered failures, and behind PRs. If it cannot converge, it leaves `status:blocked` and a PR comment with the reason.
- `pr-ci-status-comment` (PR Maintenance) auto-updates behind PRs. Merge conflicts still require manual resolution.
- If the review gate or `verify-lite` required check in the PR UI remains at `Waiting for status to be reported`, the auto-update merge commit may not have emitted the required checks. Standard response: push an empty commit to retrigger the PR event or rerun from the PR UI. Long-term fix: configure `AE_AUTO_UPDATE_TOKEN` so required checks run on the auto-update commit.
- A `Copilot Review Gate` run with `pull_request_review` / `action_required` is not itself a blocker if `Copilot Review Gate / gate` is green on the PR head SHA. Use `workflow_dispatch` with `pr_number` when a manual reevaluation is required.
- If `Copilot Review Gate / gate` remains with mixed success and failure runs, rerun the failed `Copilot Review Gate` run with `gh run rerun <RUN_ID> --failed`.
- After `Copilot Auto Fix`, gate reevaluation is dispatched by `agent-commands` through `issue_comment(created/edited)` into `copilot-review-gate.yml`. If reevaluation does not start, inspect the `agent-commands` execution log first.
- When GitHub API 429 or secondary rate limits occur, prefer Actions reruns first. `AE_GH_THROTTLE_MS` defaults to `250` (`0` disables throttling) and should be tuned together with `AE_GH_RETRY_*` if needed. References: `docs/ci/pr-automation.md`, implementation: `scripts/ci/lib/gh-exec.mjs`.
- If 429 repeats, tune in this order to avoid excessive retries:
  1. `AE_GH_THROTTLE_MS=500`
  2. `AE_GH_RETRY_INITIAL_DELAY_MS=1000`
  3. `AE_GH_RETRY_MAX_ATTEMPTS=10` only when needed.
- If Codex CLI reports `maximum number of unified exec processes`, stop long-running `watch` / `tail -f`, prefer session reuse, reduce parallelism, and avoid starting new parallel jobs until the warning clears.
- If `pnpm run lint:actions` hits a 403 while pulling `ghcr.io/rhysd/actionlint`, point `ACTIONLINT_BIN` to a local binary, for example `ACTIONLINT_BIN=/usr/local/bin/actionlint pnpm run lint:actions`.
- Notification decisions for `automation-observability-weekly` are persisted in `weekly-alert-summary.json`. If no notification was sent, inspect `suppressed` and `suppressedReason`.
- SLO / MTTR thresholds are defined in `docs/ci/automation-slo-mttr.md` and evaluated from the weekly `automation-observability-weekly` artifact.
- `Security Analysis / Secrets Scanning` is skipped when `GITLEAKS_LICENSE` is not configured. Add the repository secret `GITLEAKS_LICENSE` to enable the scan.
- `Container Security` skips SARIF upload and emits a warning when `trivy-results.sarif` is missing. Check the build failure log before triaging the upload step.

### 6. Symptom-to-runbook map

| Symptom | First check | Runbook |
| --- | --- | --- |
| `Copilot Review Gate / gate` fails | unresolved review thread count, failed run conclusion | resolve threads, then run `gh run rerun <RUN_ID> --failed` |
| `enforce-assurance` fails | `warningClaims`, `missingLanes`, `missingEvidenceKinds`, `counterexamples.open`, `warningCount`, `unlinkedCounterexamples`, `claimCount < 1`, `independenceWarnings`, and each claim `status` in `artifacts/assurance/assurance-summary.json` | fill missing lanes / evidence per `docs/quality/assurance-operations-runbook.md` |
| `PR Self-Heal` is `blocked` | PR comment reason, `status:blocked` label | fix conflicts or failing checks, then rerun manually |
| auto-merge is not enabled | `AE_AUTO_MERGE*`, required checks, `reviewDecision` | adjust conditions per `docs/ci/auto-merge.md` |
| `ERR_PNPM_LOCKFILE_CONFIG_MISMATCH` or frozen-lockfile failure | install step, `pnpm-lock.yaml`, `.npmrc`, workspace config drift | classify the lane into `required-lane`, `optional-pr`, or `manual-ops`; update the lockfile for `required-lane`; inspect the latest SHA run |
| `policy-gate` fails for `run-trace` / `enforce-context-pack` | required labels, `trace-conformance`, `KvOnce Trace Validation`, `context-pack-e2e` conclusions | add labels, rerun the relevant workflow in PR context, then reevaluate `policy-gate` |
| 429 / secondary rate limit | `gh-exec` retry log, failure timing | prefer rerun, then tune `AE_GH_THROTTLE_MS` and `AE_GH_RETRY_*` if needed |
| unified exec process limit warning | long-running jobs, concurrent session count | stop long-running sessions, reuse existing sessions, reduce parallelism |

Notes:
- Shared JSON and Step Summary outputs for automation are documented in `docs/ci/automation-observability.md`.
- Notification rules and cooldown logic are documented in `docs/ci/automation-alerting.md`.

### 7. Standard rerun procedure

#### 7.1 Rerun a single run first

- If the failing run is known, prefer `gh run rerun <RUN_ID> --failed`.
- Typical ways to find the `runId`:
  - `gh run list --branch <HEAD_BRANCH> --limit 20`
  - `gh run view <RUN_ID> --log-failed`

#### 7.2 Manual dispatch by PR number

```bash
gh workflow run "Copilot Review Gate" -f pr_number=12345
gh workflow run "PR Self-Heal" -f pr_number=12345 -f dry_run=false
gh workflow run "Codex Autopilot Lane" -f pr_number=12345 -f dry_run=false
```

#### 7.3 Resync behind or stale checks

- When `mergeStateStatus=BEHIND`, run update-branch first:
  - `gh workflow run "PR Maintenance" -f mode=update-branch -f pr_number=<PR_NUMBER>`
- If required checks are still attached to an older commit:
  1. Push an empty commit to retrigger the `pull_request` event.
  2. Rerun `gate` or `verify-lite` if needed.

#### 7.4 `ERR_PNPM_LOCKFILE_CONFIG_MISMATCH` or frozen-lockfile failure

1. `ERR_PNPM_LOCKFILE_CONFIG_MISMATCH` means the install settings encoded in the lockfile differ from the current install settings. Use `docs/ci-policy.md` as the source of truth: jobs shown in `gh pr checks <PR_NUMBER> --required` are `required-lane`, `workflow_dispatch` and scheduled maintenance flows are `manual-ops`, and explicitly non-required PR lanes are `optional-pr`.
2. For `required-lane`, do not switch to `--no-frozen-lockfile`; instead run `pnpm install` locally and update `pnpm-lock.yaml`.
3. After commit and push, inspect the latest `pull_request` run created for the new head SHA:
   - `gh run list --workflow "<WORKFLOW_NAME>" --branch <HEAD_BRANCH> --limit 20`
   - Use `gh run rerun <RUN_ID> --failed` only for manual workflows that do not create a new run after push, or when retrying a failed run for the latest SHA.
4. Treat `optional-pr` and `manual-ops` fallback paths as temporary operations. If the problem repeats, converge by updating the lockfile.

#### 7.5 Label-driven `policy-gate` failure

1. Confirm in `policy/risk-policy.yml` whether `run-trace` or `enforce-context-pack` is the required label.
2. Add the required label:
   - `gh pr edit <PR_NUMBER> --add-label run-trace`
   - `gh pr edit <PR_NUMBER> --add-label enforce-context-pack`
3. Rerun the relevant workflow in PR context:
   - trace: `gh run list --workflow "Spec Generate & Model Tests" --branch <HEAD_BRANCH> --limit 20`
   - context pack: `gh run list --workflow "Context Pack Quality Gate" --branch <HEAD_BRANCH> --limit 20`
   - `gh run rerun <RUN_ID> --failed`
4. Confirm `trace-conformance`, `KvOnce Trace Validation`, or `context-pack-e2e` became `success`, then reevaluate `policy-gate`:
   - `gh run list --workflow "Policy Gate" --branch <HEAD_BRANCH> --limit 20`

### 8. Five-minute triage

1. Classify the failed job as `quality`, `security`, or `automation`.
2. Separate configuration gaps (labels, environment, permissions) from implementation defects.
3. Check whether the failure reproduces locally with `pnpm run verify:lite`.
4. For 429-class failures, prefer rerun first, then raise `AE_GH_THROTTLE_MS` gradually.
5. If unified exec process warnings appear, stop new parallel jobs and reclaim existing sessions.
6. If the same symptom repeats, use the kill-switch variables and pause automation temporarily.

### 9. Emergency fallback

- Immediate stop:
  - Repository Variable `AE_AUTOMATION_GLOBAL_DISABLE=1`
  - Impact: skip PR Maintenance (`update-branch` / `enable-auto-merge`), auto-fix, auto-merge, self-heal, and autopilot.
- Partial stop:
  - `AE_CODEX_AUTOPILOT_ENABLED=0`
  - `AE_SELF_HEAL_ENABLED=0`
  - `AE_COPILOT_AUTO_FIX=0`
- Recovery:
  1. Fix the root cause.
  2. Restore the stop variables.
  3. Resume the target workflows gradually through `workflow_dispatch`.

### 10. Change-record rule

- Always leave a PR comment or issue comment that records both the failure and the recovery action.
- Record at minimum:
  - occurrence time (UTC)
  - failing workflow / job
  - log source `runId`
  - remediation applied
  - rerun result
  - recurrence prevention, when applicable

### References

- `docs/ci/ci-baseline-checklist.md`
- `docs/quality/assurance-operations-runbook.md`
- `docs/ci/automation-observability.md`
- `docs/ci/automation-alerting.md`
- `docs/ci/automation-failure-policies.md`
- `docs/ci/automation-slo-mttr.md`
- `docs/testing/test-categorization.md`
- `docs/testing/flaky-test-triage.md`

## 日本語

最終更新: 2026-03-24

目的: よくある CI 失敗を短時間で切り分け、適切な rerun と remediation に到達するための最短手順を提供する。

### 1. 失敗ジョブの特定

- PR 画面または CI summary から失敗ジョブへのリンクを確認する。
- 実行コマンド、workflow 名、job 名、head SHA、関連する環境変数を記録する。

### 2. 失敗の分類

- **Lint / Type**: まず `verify-lite` summary を確認する。
- **Lockfile**: `ERR_PNPM_LOCKFILE_CONFIG_MISMATCH` または `pnpm install --frozen-lockfile` 失敗を確認し、`pnpm-lock.yaml` と現在の pnpm install 設定を比較する。
- **Tests**: `docs/testing/flaky-test-triage.md` を参照する。
- **Artifacts / Codegen**: `generate-artifacts` の出力と期待される report path を確認する。
- **Security / Policy**: `run-security` などの label gating、fork 制約、`policy/risk-policy.yml` の required-label 条件を確認する。

### 3. ローカル再現（最小構成）

- `pnpm install --frozen-lockfile`
- `pnpm run verify:lite`
- `pnpm run test:ci:lite`

### 4. 安全な緩和策

- 重い suite は label-gated lane を優先する。`docs/ci/label-gating.md` を参照。
- baseline は stable profile を使う。`docs/ci/stable-profile.md` を参照。
- 即時修復が narrow scope の場合も、修正内容と follow-up issue を記録する。

### 5. Automation notes

- Failed job は `ci-auto-rerun-failed` が **1回だけ** 自動再実行する。追加対応の前に rerun log を確認する。
- `PR Self-Heal`（`pr-self-heal.yml`）を有効化している場合、review gate failure、429 起因失敗、behind PR の自動復旧を試行する。収束しない場合は `status:blocked` と PR comment を残す。
- `pr-ci-status-comment`（PR Maintenance）が behind の PR を自動更新する。merge conflict は手動解決が必要。
- PR UI 上で review gate または `verify-lite` の required check が `Waiting for status to be reported` のままなら、auto-update merge commit に required checks が載っていない可能性がある。標準対応は、空コミットを push して `pull_request` を再発火するか、PR UI から rerun する。恒久策は `AE_AUTO_UPDATE_TOKEN` を設定し、auto-update commit 上でも required checks を走らせること。
- `Copilot Review Gate` の `pull_request_review` / `action_required` 自体は、PR head SHA 上の `Copilot Review Gate / gate` が green なら merge blocker ではない。手動 reevaluation が必要な場合は `workflow_dispatch` と `pr_number` を使う。
- `Copilot Review Gate / gate` が success / failure 混在のまま残る場合は、失敗側の `Copilot Review Gate` run を `gh run rerun <RUN_ID> --failed` で再試行する。
- `Copilot Auto Fix` 後の gate reevaluation は `agent-commands` が `issue_comment(created/edited)` 経由で `copilot-review-gate.yml` を dispatch する。起動しない場合は `agent-commands` の実行ログを先に確認する。
- GitHub API の 429 / secondary rate limit が出る場合、まず Actions rerun を優先する。`AE_GH_THROTTLE_MS` の既定は `250`（`0` で無効化）で、必要に応じて `AE_GH_RETRY_*` と合わせて調整する。参照: `docs/ci/pr-automation.md`、実装: `scripts/ci/lib/gh-exec.mjs`。
- 429 が連続する場合は、過剰 retry を避けるため次の順で調整する:
  1. `AE_GH_THROTTLE_MS=500`
  2. `AE_GH_RETRY_INITIAL_DELAY_MS=1000`
  3. `AE_GH_RETRY_MAX_ATTEMPTS=10`（必要時のみ）
- Codex CLI で `maximum number of unified exec processes` 警告が出る場合は、長時間 `watch` / `tail -f` を停止し、session 再利用を優先し、並列度を下げ、警告が消えるまで新規並列ジョブを開始しない。
- `pnpm run lint:actions` で `ghcr.io/rhysd/actionlint` pull が 403 の場合は、`ACTIONLINT_BIN` でローカル binary を指定できる。例: `ACTIONLINT_BIN=/usr/local/bin/actionlint pnpm run lint:actions`。
- `automation-observability-weekly` の通知判定は `weekly-alert-summary.json` に保存される。通知が来ない場合は `suppressed` と `suppressedReason` を確認する。
- SLO / MTTR の判定基準は `docs/ci/automation-slo-mttr.md` にあり、週次 `automation-observability-weekly` artifact で評価される。
- `Security Analysis / Secrets Scanning` は `GITLEAKS_LICENSE` 未設定時に skip される。scan を有効化する場合は repository secret `GITLEAKS_LICENSE` を設定する。
- `Container Security` は `trivy-results.sarif` 未生成時に SARIF upload を skip して warning を出す。upload を疑う前に build 失敗ログを確認する。

### 6. 症状 → runbook 対応表

| 症状 | 一次確認 | runbook |
| --- | --- | --- |
| `Copilot Review Gate / gate` fail | unresolved review thread 数、失敗 run の conclusion | thread を解消し、`gh run rerun <RUN_ID> --failed` を実行 |
| `enforce-assurance` fail | `artifacts/assurance/assurance-summary.json` の `warningClaims` / `missingLanes` / `missingEvidenceKinds` / `counterexamples.open` / `warningCount` / `unlinkedCounterexamples` / `claimCount < 1` / `independenceWarnings` と、claim ごとの `status` | `docs/quality/assurance-operations-runbook.md` に沿って不足 lane / evidence を補完 |
| `PR Self-Heal` が `blocked` | PR comment の reason、`status:blocked` label | conflict または失敗 check を修復後に手動 rerun |
| auto-merge が有効化されない | `AE_AUTO_MERGE*`、required checks、`reviewDecision` | `docs/ci/auto-merge.md` に沿って条件修正 |
| `ERR_PNPM_LOCKFILE_CONFIG_MISMATCH` / frozen-lockfile fail | install step、`pnpm-lock.yaml`、`.npmrc`、workspace config drift | lane を `required-lane` / `optional-pr` / `manual-ops` に分類し、`required-lane` なら lockfile を更新して最新 SHA run を確認 |
| `policy-gate` fail（`run-trace` / `enforce-context-pack`） | required label、`trace-conformance` / `KvOnce Trace Validation` / `context-pack-e2e` の conclusion | label 付与後に対応 workflow を PR 文脈で rerun し、`policy-gate` を再評価 |
| 429 / secondary rate limit | `gh-exec` retry log、失敗タイミング | rerun 優先、その後 `AE_GH_THROTTLE_MS` と `AE_GH_RETRY_*` を調整 |
| unified exec process 上限警告 | 長時間 job、同時 session 数 | 長時間 session を停止し、既存 session を再利用し、並列度を抑制 |

補足:
- 自動化系の共通 JSON / Step Summary 出力は `docs/ci/automation-observability.md` を参照する。
- 通知条件と cooldown は `docs/ci/automation-alerting.md` を参照する。

### 7. 再実行手順（標準）

#### 7.1 単一 run の再実行（最優先）

- 失敗 run が特定できる場合は `gh run rerun <RUN_ID> --failed` を優先する。
- `runId` の取得例:
  - `gh run list --branch <HEAD_BRANCH> --limit 20`
  - `gh run view <RUN_ID> --log-failed`

#### 7.2 PR番号指定での手動起動

```bash
gh workflow run "Copilot Review Gate" -f pr_number=12345
gh workflow run "PR Self-Heal" -f pr_number=12345 -f dry_run=false
gh workflow run "Codex Autopilot Lane" -f pr_number=12345 -f dry_run=false
```

#### 7.3 behind / stale checks の再同期

- `mergeStateStatus=BEHIND` の場合は update-branch を先に実行する:
  - `gh workflow run "PR Maintenance" -f mode=update-branch -f pr_number=<PR番号>`
- required checks が古い commit に残る場合:
  1. 空コミットを push して `pull_request` event を再発火する。
  2. 必要に応じて `gate` または `verify-lite` を rerun する。

#### 7.4 `ERR_PNPM_LOCKFILE_CONFIG_MISMATCH` / frozen-lockfile fail

1. `ERR_PNPM_LOCKFILE_CONFIG_MISMATCH` は、lockfile に記録された install 設定と現在の install 設定の不一致を示す。`docs/ci-policy.md` を source of truth とし、`gh pr checks <PR番号> --required` に出る job を `required-lane`、`workflow_dispatch` と scheduled maintenance flow を `manual-ops`、明示的に非必須化された PR lane を `optional-pr` と扱う。
2. `required-lane` では `--no-frozen-lockfile` に切り替えず、`pnpm install` をローカルで実行して `pnpm-lock.yaml` を更新する。
3. commit / push 後は、新しい head SHA で生成された最新の `pull_request` run を確認する:
   - `gh run list --workflow "<WORKFLOW名>" --branch <HEAD_BRANCH> --limit 20`
   - `gh run rerun <RUN_ID> --failed` は、push 後に新 run が生成されない手動 workflow または最新 SHA に対する failed run の再試行時だけ使う。
4. `optional-pr` / `manual-ops` の fallback は一時運用とみなす。反復する場合も lockfile 更新で収束させる。

#### 7.5 ラベル起因の `policy-gate` fail

1. `policy/risk-policy.yml` で `run-trace` または `enforce-context-pack` が required label か確認する。
2. 必要 label を付与する:
   - `gh pr edit <PR番号> --add-label run-trace`
   - `gh pr edit <PR番号> --add-label enforce-context-pack`
3. 対応 workflow を PR 文脈で rerun する:
   - trace: `gh run list --workflow "Spec Generate & Model Tests" --branch <HEAD_BRANCH> --limit 20`
   - context pack: `gh run list --workflow "Context Pack Quality Gate" --branch <HEAD_BRANCH> --limit 20`
   - `gh run rerun <RUN_ID> --failed`
4. `trace-conformance` / `KvOnce Trace Validation` / `context-pack-e2e` が `success` になったことを確認し、`policy-gate` を再評価する:
   - `gh run list --workflow "Policy Gate" --branch <HEAD_BRANCH> --limit 20`

### 8. 失敗時の切り分け（5分版）

1. 失敗 job が `quality` / `security` / `automation` のどれかを確定する。
2. 原因粒度を `設定不足`（label / env / permission）か `実装不具合` かで分離する。
3. `pnpm run verify:lite` でローカル再現するか確認する。
4. 429 系なら rerun を優先し、必要に応じて `AE_GH_THROTTLE_MS` を段階的に上げる。
5. unified exec 警告が出る場合は、新規並列を止めて既存 session を回収する。
6. 同一症状が連続する場合は kill-switch で自動化を一時停止する。

### 9. 緊急回避（Fail-safe）

- 即時停止:
  - Repository Variable `AE_AUTOMATION_GLOBAL_DISABLE=1`
  - 影響: PR Maintenance（`update-branch` / `enable-auto-merge`）、auto-fix、auto-merge、self-heal、autopilot を skip する。
- 部分停止:
  - `AE_CODEX_AUTOPILOT_ENABLED=0`
  - `AE_SELF_HEAL_ENABLED=0`
  - `AE_COPILOT_AUTO_FIX=0`
- 復帰:
  1. 根本原因を修正する。
  2. 停止変数を戻す。
  3. 対象 workflow を `workflow_dispatch` で段階再開する。

### 10. 変更記録（運用ルール）

- 失敗と復旧の実施内容は、PR comment または issue comment に必ず残す。
- 記録必須項目:
  - 発生時刻（UTC）
  - 失敗 workflow / job
  - 取得ログ `runId`
  - 実施した修正
  - rerun 結果
  - 再発防止策（必要時）

### References

- `docs/ci/ci-baseline-checklist.md`
- `docs/quality/assurance-operations-runbook.md`
- `docs/ci/automation-observability.md`
- `docs/ci/automation-alerting.md`
- `docs/ci/automation-failure-policies.md`
- `docs/ci/automation-slo-mttr.md`
- `docs/testing/test-categorization.md`
- `docs/testing/flaky-test-triage.md`
