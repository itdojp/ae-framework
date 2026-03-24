---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Codex Autopilot Lane

This document defines the opt-in lane that drives PRs from review handling to auto-merge enablement with bounded automation. / このドキュメントは、review 対応から auto-merge 有効化までを bounded な自動化で進める opt-in レーンを定義します。

Primary sources / 一次情報:
- `.github/workflows/codex-autopilot-lane.yml`
- `scripts/ci/codex-autopilot-lane.mjs`
- `scripts/ci/copilot-auto-fix.mjs`
- `scripts/ci/auto-merge-enabler.mjs`

> Language / 言語: English | 日本語

---

## English

### 1. Overview

`Codex Autopilot Lane` is an opt-in lane for PRs labeled `autopilot:on`. It attempts to move the PR forward from review handling to auto-merge enablement while preserving fail-closed behavior when the lane cannot converge safely.

### 2. Enablement

Repository Variables:
- `AE_CODEX_AUTOPILOT_ENABLED=1` (required for automatic operation)
- `AE_AUTOPILOT_MAX_ROUNDS` (default `3`)
- `AE_AUTOPILOT_ROUND_WAIT_SECONDS` (default `8`)
- `AE_AUTOPILOT_WAIT_STRATEGY` (default `fixed`; `fixed` / `exponential`)
- `AE_AUTOPILOT_ROUND_WAIT_MAX_SECONDS` (defaults to `AE_AUTOPILOT_ROUND_WAIT_SECONDS`)
- `AE_AUTOPILOT_DRY_RUN=1` for side-effect-free validation
- `AE_AUTOPILOT_ACTIONABLE_COMMAND` (optional): command used to process actionable non-suggestion review comments
- `AE_AUTOPILOT_ACTIONABLE_DRY_RUN` (optional): overrides dry-run behavior only for actionable execution
- `AE_AUTOPILOT_AUTO_LABEL=1`: auto-apply missing labels derived from Risk Policy (default `0`)
- `AE_AUTOPILOT_RISK_POLICY_PATH` (default `policy/risk-policy.yml`)
- `AE_AUTOPILOT_WRITE_CONTRACT_ARTIFACTS=1` (optional): emit `pr-state.v1` / `execution-plan.v1`
- `AE_AUTOPILOT_PR_STATE_FILE` (default `artifacts/ci/pr-state-v1.json`)
- `AE_AUTOPILOT_EXECUTION_PLAN_FILE` (default `artifacts/ci/execution-plan-v1.json`)
- `AE_AUTOMATION_REPORT_FILE` (optional): automation report output path
- `AE_AUTOPILOT_REQUIRED_CHECKS` (default `gate`, comma-separated)

Operational notes:
- `workflow_dispatch` can run even when `AE_CODEX_AUTOPILOT_ENABLED` is unset, for manual validation.
- On PRs with `autopilot:on` and `AE_CODEX_AUTOPILOT_ENABLED=1`, `copilot-auto-fix.yml` is skipped to avoid duplicated execution; the `pull_request_review` path in `Codex Autopilot Lane` continues processing.

### 3. Trigger conditions

Triggers:
- `pull_request` (`opened`, `synchronize`, `reopened`, `labeled`, `ready_for_review`)
- `pull_request_review` (`submitted`)
- `issue_comment` (`/autopilot run`)
- `workflow_dispatch` (`pr_number` required)

Target PR conditions:
- the PR has label `autopilot:on`
- the PR is not draft
- the PR is not a fork PR
- for `pull_request_review`, the reviewer must be trusted (`MEMBER` / `OWNER` / `COLLABORATOR`) or an allowed AI review actor

### 4. Execution state machine

1. Fetch PR state (`mergeability`, labels, check rollup).
2. Derive required labels from Risk Policy (`policy/risk-policy.yml`).
   - if `AE_AUTOPILOT_AUTO_LABEL=1`, the lane applies missing labels automatically
   - otherwise it stops with a missing-label reason
3. If `mergeState=BEHIND`, dispatch `PR Maintenance` update-branch.
4. Scan unresolved AI review threads and look for actionable comments that are not `suggestion` blocks.
   - if `AE_AUTOPILOT_ACTIONABLE_COMMAND` is configured, run it and aggregate results
   - if it is not configured, stop with `actionable review tasks pending`
   - human dispositions such as `not applicable`, `fixed`, `対応不要`, `対応済み` remove the item from actionable scope
   - any `failed > 0` result is fail-closed with `status:blocked`
   - in active execution, any `skipped > 0` result is also fail-closed as `actionable execution incomplete`
5. If Copilot threads remain unresolved, or `gate` is failing / missing:
   - run `copilot-auto-fix.mjs` in force mode
   - dispatch `copilot-review-gate.yml`
6. Try to enable auto-merge through `auto-merge-enabler.mjs`.
7. If the lane still does not converge, add `status:blocked` and stop.

### 5. PR comment and artifact contracts

PR comment behavior:
- marker: `<!-- AE-CODEX-AUTOPILOT v1 -->`
- when `status=blocked`, the first two lines are deterministic:
  - `Blocked: <reason>`
  - `To unblock: <single action>`
- detailed `reason`, `actions`, and `unblock` follow after the deterministic header
- actionable execution output is also deterministic:
  - `execution-result: success|failed|skipped`
  - `actionable execution: <status> (attempted=..., succeeded=..., failed=..., skipped=...)`
  - `actionable-execution-preview:` (up to 3 items)

Artifacts when `AE_AUTOPILOT_WRITE_CONTRACT_ARTIFACTS=1`:
- `artifacts/ci/automation-report.json`
  - automation execution report (`ae-automation-report/v1`)
- `artifacts/ci/pr-state-v1.json`
  - PR state contract (`pr-state.v1`)
- `artifacts/ci/execution-plan-v1.json`
  - round task plan (`execution-plan.v1`)

### 6. `AE_AUTOPILOT_ACTIONABLE_COMMAND` I/O contract

Inputs through environment variables:
- `AE_ACTIONABLE_TASKS_JSON` (JSON file containing task array)
- `AE_ACTIONABLE_PR_NUMBER`
- `AE_ACTIONABLE_ROUND`

Expected stdout:
- JSON object in the form
  - `{ "results": [{ "commentId": <number>, "status": "success|failed|skipped", "reason": "<optional>" }] }`

Decision rules:
- any `failed > 0` result is fail-closed
- in active execution, any `skipped > 0` result is fail-closed
- the lane proceeds only when every result is `success`

### 7. Safety design

- opt-in label required: `autopilot:on`
- bounded rounds: `AE_AUTOPILOT_MAX_ROUNDS`
- dry-run available: `AE_AUTOPILOT_DRY_RUN=1`
- conflicting states (`CONFLICTING` / `DIRTY`) stop automatically with `status:blocked`

No Human Bottleneck alignment:
- every stop path must output both a reason and a minimal unblock action
- blocked comments use one-action-per-line deterministic wording
- `done` / `skip` / `blocked` meanings must match the reason rules in `scripts/ci/codex-autopilot-lane.mjs`

### 8. Operating notes

- validate the lane first with `AE_AUTOPILOT_DRY_RUN=1`
- combine with `PR Self-Heal` to reduce blocked rates
- if auto-merge is not enabled, check branch protection, required checks, and label conditions first
- when `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1` (default), confirm that `Change Package Validation` is already present in the PR summary

### 9. Stop reasons and unblock actions

| status/reason | Minimal unblock action |
| --- | --- |
| `skip` + `missing label autopilot:on` | add `autopilot:on` and run `/autopilot run` |
| `skip` + `draft PR` | mark Ready for review and run `/autopilot run` |
| `blocked` + `missing policy labels: ...` | add the missing labels and run `/autopilot run` |
| `blocked` + `actionable review tasks pending: <n>` | address the actionable comments or record a non-applicable disposition, then run `/autopilot run` |
| `blocked` + `actionable execution failed: <x>/<y> failed` | inspect the execution result, repair manually or fix `AE_AUTOPILOT_ACTIONABLE_COMMAND`, then run `/autopilot run` |
| `blocked` + `actionable execution incomplete: <x>/<y> skipped` | remove the skip cause or handle manually, then run `/autopilot run` |
| `blocked` + `actionable review task scan truncated (pagination required)` | fix the GraphQL / pagination issue, then run `/autopilot run` |
| `blocked` + `max rounds reached without convergence` | wait for in-flight checks or dispatches to settle, then run `/autopilot run` |
| `blocked` + `merge conflict` | resolve the conflict through update-branch or manual rebase, push, then run `/autopilot run` |
| `done` + `checks healthy, waiting for required checks/merge queue` | wait for the required checks or merge queue; no extra fix is needed |
| `done` + `auto-merge enabled` / `already merged` | no further action |

When `done` uses a different reason, keep watching PR checks until merge completes.

### 10. Minimum regression command

```bash
pnpm vitest run tests/unit/ci/codex-autopilot-lane.test.ts
```

For `blocked` scenarios, confirm:
- line 1 is `Blocked: ...`
- line 2 is `To unblock: ...`
- each reason maps to a deterministic unblock action

## 日本語

### 1. 有効化

Repository Variables:

- `AE_CODEX_AUTOPILOT_ENABLED=1`（必須）
- `AE_AUTOPILOT_MAX_ROUNDS`（既定 `3`）
- `AE_AUTOPILOT_ROUND_WAIT_SECONDS`（既定 `8`）
- `AE_AUTOPILOT_WAIT_STRATEGY`（既定 `fixed`。`fixed` / `exponential`）
- `AE_AUTOPILOT_ROUND_WAIT_MAX_SECONDS`（既定 `AE_AUTOPILOT_ROUND_WAIT_SECONDS` と同値）
- `AE_AUTOPILOT_DRY_RUN=1` で副作用なし検証
- `AE_AUTOPILOT_ACTIONABLE_COMMAND`（任意）: actionable non-suggestion 指摘を処理する実行コマンド
- `AE_AUTOPILOT_ACTIONABLE_DRY_RUN`（任意）: actionable 実行のみ dry-run を個別制御（未設定時は `AE_AUTOPILOT_DRY_RUN` に追従）
- `AE_AUTOPILOT_AUTO_LABEL=1` のとき、Risk Policy 由来の不足ラベルを自動付与（既定は `0`）
- `AE_AUTOPILOT_RISK_POLICY_PATH`（既定 `policy/risk-policy.yml`）
- `AE_AUTOPILOT_WRITE_CONTRACT_ARTIFACTS=1`（任意）: `pr-state.v1` / `execution-plan.v1` の成果物を出力
- `AE_AUTOPILOT_PR_STATE_FILE`（既定 `artifacts/ci/pr-state-v1.json`）
- `AE_AUTOPILOT_EXECUTION_PLAN_FILE`（既定 `artifacts/ci/execution-plan-v1.json`）
- `AE_AUTOMATION_REPORT_FILE`（任意）: 自動化レポートJSON出力先（例: `artifacts/ci/automation-report.json`）
- `AE_AUTOPILOT_REQUIRED_CHECKS`（既定 `gate`、カンマ区切り）

補足:
- `workflow_dispatch` は `AE_CODEX_AUTOPILOT_ENABLED` 未設定でも実行可能（手動検証用）
- `autopilot:on` かつ `AE_CODEX_AUTOPILOT_ENABLED=1` の PR では `copilot-auto-fix.yml` は重複実行抑止のため skip され、`pull_request_review` 起点の `Codex Autopilot Lane` が処理を継続

### 2. 起動条件

- `pull_request`（opened/synchronize/reopened/labeled/ready_for_review）
- `pull_request_review`（submitted）
- `issue_comment`（`/autopilot run`）
- `workflow_dispatch`（`pr_number` 必須）

対象 PR 条件:
- `autopilot:on` ラベルが付与されていること
- draft ではないこと
- fork PR ではないこと（権限の都合で運用非推奨）
- `pull_request_review` 起点は trusted reviewer のみ（`author_association` が MEMBER/OWNER/COLLABORATOR、または許可済み AI review actor）

### 3. 状態遷移（実装）

1. PR 状態を取得（mergeability / labels / check rollup）
2. Risk Policy (`policy/risk-policy.yml`) から required label を算出
   - `AE_AUTOPILOT_AUTO_LABEL=1` のときは不足ラベルを自動付与
   - 既定 (`0`) は不足ラベルを reason にして停止
3. `mergeState=BEHIND` なら `PR Maintenance` の update-branch を dispatch
4. 未解決の AI review thread を走査し、`suggestion` ではない actionable 指摘を検出した場合:
   - `AE_AUTOPILOT_ACTIONABLE_COMMAND` が設定されていれば実行し、結果を集計
   - `AE_AUTOPILOT_ACTIONABLE_COMMAND` 未設定時は `actionable review tasks pending` で停止
   - 人手コメントに `対応不要` / `対応済み` / `not applicable` / `fixed` 相当の disposition が含まれる指摘は actionable 対象から除外
   - 失敗（`failed > 0`）は fail-closed で `status:blocked`
   - active 実行で `skipped > 0` は `actionable execution incomplete` として fail-closed
   - 成功時は再評価へ進行
5. Copilot 未解決スレッドまたは gate failure / missing の場合:
   - `copilot-auto-fix.mjs` を force mode で実行
   - `copilot-review-gate.yml` を dispatch
6. `auto-merge-enabler.mjs` で auto-merge 有効化を試行
7. 収束しない場合は `status:blocked` を付与して停止

### 4. PR コメントと成果物契約

PR コメント（upsert）:
- marker: `<!-- AE-CODEX-AUTOPILOT v1 -->`
- `status=blocked` の場合は先頭 2 行を deterministic 形式で出力
  - `Blocked: <reason>`
  - `To unblock: <single action>`
- 追加情報として `reason` / `actions` / `unblock` の詳細を続けて出力
- actionable 実行結果は常に deterministic に出力
  - `execution-result: success|failed|skipped`
  - `actionable execution: <status> (attempted=..., succeeded=..., failed=..., skipped=...)`
  - `actionable-execution-preview:`（最大 3 件）

成果物（`AE_AUTOPILOT_WRITE_CONTRACT_ARTIFACTS=1` の場合）:
- `artifacts/ci/automation-report.json`
  - 自動化実行レポート（`ae-automation-report/v1`）
- `artifacts/ci/pr-state-v1.json`
  - PR 状態（`pr-state.v1` 契約）
- `artifacts/ci/execution-plan-v1.json`
  - ラウンド内タスク列（`execution-plan.v1` 契約）

### 5. `AE_AUTOPILOT_ACTIONABLE_COMMAND` の入出力契約

入力（環境変数）:
- `AE_ACTIONABLE_TASKS_JSON`（task 配列を含む JSON ファイル）
- `AE_ACTIONABLE_PR_NUMBER`
- `AE_ACTIONABLE_ROUND`

期待する標準出力:
- JSON object:
  - `{ "results": [{ "commentId": <number>, "status": "success|failed|skipped", "reason": "<optional>" }] }`

判定:
- `failed > 0` は fail-closed
- active 実行で `skipped > 0` は fail-closed
- すべて `success` のときのみ次段へ進行

### 6. 安全設計

- opt-in ラベル必須（`autopilot:on`）
- ラウンド上限あり（`AE_AUTOPILOT_MAX_ROUNDS`）
- dry-run あり（`AE_AUTOPILOT_DRY_RUN=1`）
- 競合状態（`CONFLICTING` / `DIRTY`）は自動停止して `status:blocked`

No Human Bottleneck 整合ポイント:
- 停止時は必ず「理由」と「最小解除手順」を同時に出す
- blocked comment は 1 行 1 アクションで再実行可能な文面に固定する
- `done` / `skip` / `blocked` の判定は `scripts/ci/codex-autopilot-lane.mjs` の reason ルールに一致させる

### 7. 運用メモ

- まず `AE_AUTOPILOT_DRY_RUN=1` で挙動確認してから本番有効化
- 自動復旧は `PR Self-Heal` と併用すると停止率を下げられる
- auto-merge が有効化されない場合は branch protection / required checks / label 条件を確認
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1`（既定）の場合、PR summary に `Change Package Validation` が出力済みであることを確認

### 8. 停止理由と解除手順（運用定型）

| status/reason | 最小解除手順 |
| --- | --- |
| `skip` + `missing label autopilot:on` | PR に `autopilot:on` ラベルを付与して `/autopilot run` |
| `skip` + `draft PR` | Ready for review に変更して `/autopilot run` |
| `blocked` + `missing policy labels: ...` | 不足ラベルを付与して `/autopilot run`（`AE_AUTOPILOT_AUTO_LABEL=1` なら自動付与） |
| `blocked` + `actionable review tasks pending: <n>` | actionable 指摘に対応、または非適用理由を返信して `/autopilot run` |
| `blocked` + `actionable execution failed: <x>/<y> failed` | 実行結果を確認し、手動修正または `AE_AUTOPILOT_ACTIONABLE_COMMAND` を修正して `/autopilot run` |
| `blocked` + `actionable execution incomplete: <x>/<y> skipped` | skip 理由を解消して再実行、または手動対応後に `/autopilot run` |
| `blocked` + `actionable review task scan truncated (pagination required)` | GraphQL / pagination 問題を解消して `/autopilot run` |
| `blocked` + `max rounds reached without convergence` | in-flight の checks / dispatch が収束するまで待機し、`/autopilot run` |
| `blocked` + `merge conflict` | update-branch または手動 rebase で衝突を解消し、push 後に `/autopilot run` |
| `done` + `checks healthy, waiting for required checks/merge queue` | required checks / merge queue の完了を待機 |
| `done` + `auto-merge enabled` / `already merged` | 追加操作不要 |

補足:
- `done` で上表以外の reason の場合は、PR checks を監視して merge 完了まで待機します。

### 9. 回帰確認コマンド（最小）

```bash
pnpm vitest run tests/unit/ci/codex-autopilot-lane.test.ts
```

`blocked` 系ケースで以下を確認します。
- 1 行目が `Blocked: ...`
- 2 行目が `To unblock: ...`
- reason ごとに解除手順が deterministic に一致
