---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Copilot Review Gate

This document defines the required gate that verifies AI review presence and resolved review threads before merge. / このドキュメントは、マージ前に AI review の存在と review thread 解消を必須化する gate を定義します。

Primary sources / 一次情報:
- workflow: `.github/workflows/copilot-review-gate.yml`
- script: `scripts/ci/copilot-review-gate.mjs`
- dispatch helper: `.github/workflows/agent-commands.yml`

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

`Copilot Review Gate` makes AI review a merge-blocking requirement. The gate fails when either of these conditions is missing:
- at least one review exists from an allowed AI review actor
- every thread touched by that actor is resolved

The required status context is `gate` (`Copilot Review Gate`).

### 2. How it works

- Workflow: `.github/workflows/copilot-review-gate.yml`
- Script: `scripts/ci/copilot-review-gate.mjs`
- Triggers:
  - `pull_request`
  - `pull_request_review`
  - `workflow_dispatch`
- Auxiliary trigger:
  - `.github/workflows/agent-commands.yml` on `issue_comment` (`created` / `edited`)
  - when an auto-fix result comment contains `<!-- AE-COPILOT-AUTO-FIX v1 -->`, the workflow dispatches `copilot-review-gate.yml` again for the PR head

The script queries PR reviews and review threads through GraphQL, then checks:
- whether a review exists from any account listed in `AI_REVIEW_ACTORS`
  - fallback: `COPILOT_ACTORS`
- whether every thread that the target actor participated in is `isResolved=true`

If either condition is missing, the workflow fails and blocks merge when `gate` is required.

Configuration resolution:
- `COPILOT_REVIEW_WAIT_MINUTES` / `COPILOT_REVIEW_MAX_ATTEMPTS`
  - resolved through `scripts/ci/lib/automation-config.mjs`
  - precedence: explicit variable -> `AE_AUTOMATION_PROFILE` -> built-in default
- GitHub API retries and throttling
  - handled through `scripts/ci/lib/gh-exec.mjs`
  - controlled by `AE_GH_THROTTLE_MS` / `AE_GH_RETRY_*`

Skip conditions in the current implementation:
- `issue_comment` without PR context
- `workflow_dispatch` on the default branch without `pr_number`
- empty `AI_REVIEW_ACTORS` (or empty fallback `COPILOT_ACTORS`)

### 3. Branch protection positioning

Add `gate` to required checks in branch protection.

Current reference example:
- `.github/branch-protection.main.verify-lite-noreview.json`

Operationally, this gate is part of the current PR baseline together with:
- `verify-lite`
- `policy-gate`
- `gate`

### 4. Normal usage

1. Request AI review through the GitHub UI review surface.
2. Address findings and resolve conversations on the PR.
3. Wait for `Copilot Review Gate / gate` to turn green.
4. If needed, run the workflow manually from Actions using `workflow_dispatch`.
   - On the default branch, a manual run without `pr_number` skips without evaluating checks, so `pr_number` is effectively required.
   - On non-default branches, or when there is no associated PR context, `pr_number` must be provided or the run fails.

### 5. Default AI review actors

- primary variable: `AI_REVIEW_ACTORS`
- legacy fallback: `COPILOT_ACTORS`
- built-in default actors when neither variable is set:
  - `copilot-pull-request-reviewer`
  - `github-copilot`
  - `github-copilot[bot]`
  - `copilot`
  - `copilot[bot]`
  - `chatgpt-codex-connector`
  - `chatgpt-codex-connector[bot]`
  - `Copilot`
- matching is case-insensitive

### 6. Wait / retry tuning

Operators can adjust review wait behavior with:
- `COPILOT_REVIEW_WAIT_MINUTES`
- `COPILOT_REVIEW_MAX_ATTEMPTS`

The default behavior is 5 minutes x 3 attempts. The same settings can also be managed through `AE_AUTOMATION_PROFILE`.

### 7. Exception handling

If AI review is unavailable in a given environment, do one of the following:
- do not include `gate` in required checks
- explicitly disable actor detection by setting `AI_REVIEW_ACTORS=(empty)`

That path should be treated as an operational exception, not the default baseline.

### 8. Troubleshooting

- AI review appears only as comments and not as a review:
  - start AI review from the PR-side review UI
- threads remain unresolved:
  - use `Resolve conversation` on the PR after handling the finding
- auto-fix resolved threads but did not push changes:
  - rerun `Copilot Review Gate` manually from Actions
- the `pull_request_review` path stays in `action_required`:
  - judge the final state from the PR head SHA status of `Copilot Review Gate / gate`
  - rerun via `workflow_dispatch` with `pr_number` if necessary
- the same head SHA shows both success and failure:
  - rerun the failed `Copilot Review Gate` workflow run
  - prefer the latest check run on the current head SHA
- the gate does not detect the AI actor:
  - confirm that `AI_REVIEW_ACTORS` or fallback `COPILOT_ACTORS` contains the actual account name
- fork PRs cannot post comments:
  - the workflow still evaluates the gate, but comment-side evidence may be absent
- required checks stay at `Expected — Waiting for status to be reported`:
  - verify that branch protection uses the actual job name / required context
  - verify that the workflow is eligible to run on the PR
  - see `docs/ci/branch-protection-operations.md`

### 9. Related documents

- `docs/ci/copilot-auto-fix.md`
- `docs/ci/pr-automation.md`
- `docs/ci/branch-protection-operations.md`
- `docs/ci/automation-profiles.md`

## 日本語

### 1. 目的

PR をマージする前に、GitHub Copilot 等の AI レビューが存在し、その指摘スレッドが解決済みであることを必須化します。

必須 status context は `gate`（`Copilot Review Gate`）です。

### 2. 仕組み

- Workflow: `.github/workflows/copilot-review-gate.yml`
- Script: `scripts/ci/copilot-review-gate.mjs`
- トリガー:
  - `pull_request`
  - `pull_request_review`
  - `workflow_dispatch`
- 補助トリガー:
  - `.github/workflows/agent-commands.yml` の `issue_comment(created/edited)`
  - auto-fix 結果コメント `<!-- AE-COPILOT-AUTO-FIX v1 -->` を検知すると、`copilot-review-gate.yml` を PR head に対して再 dispatch します

動作:
- PR の review 一覧と review thread を GraphQL で取得
- `AI_REVIEW_ACTORS`（未設定時は `COPILOT_ACTORS`）に含まれる actor の review が存在するかを確認
- 対象 actor が関与した thread がすべて `isResolved=true` かを確認

上記条件を満たさない場合は workflow を failure にし、`gate` を Required にしている場合は merge を停止します。

設定解決:
- `COPILOT_REVIEW_WAIT_MINUTES` / `COPILOT_REVIEW_MAX_ATTEMPTS`
  - `scripts/ci/lib/automation-config.mjs` で解決
  - 優先順位: 個別変数 -> `AE_AUTOMATION_PROFILE` -> 既定値
- GitHub API の retry / throttle
  - `scripts/ci/lib/gh-exec.mjs` 経由で実行
  - `AE_GH_THROTTLE_MS` / `AE_GH_RETRY_*` を適用

現行実装の skip 条件:
- `issue_comment` だが PR 文脈ではない
- default branch に対する `workflow_dispatch` で `pr_number` がない
- `AI_REVIEW_ACTORS`（または fallback の `COPILOT_ACTORS`）が空

### 3. 必須化（Branch protection）

`gate` を Required checks に追加してください。

現行の参照例:
- `.github/branch-protection.main.verify-lite-noreview.json`

現在の PR baseline は以下です。
- `verify-lite`
- `policy-gate`
- `gate`

### 4. 使い方

1. GitHub UI の review 導線から AI review を依頼
2. 指摘へ対応し、PR 上で conversation を resolve
3. `Copilot Review Gate / gate` が green になることを確認
4. 必要なら Actions から `workflow_dispatch` で手動実行
   - default branch では `pr_number` がないと skip されて判定が行われないため、実質必須
   - non-default branch、または PR 文脈を持たない手動実行では `pr_number` を指定しないと failure になります

### 5. 既定の AI review actor

- 優先変数: `AI_REVIEW_ACTORS`
- legacy fallback: `COPILOT_ACTORS`
- 両方未設定時の built-in default:
  - `copilot-pull-request-reviewer`
  - `github-copilot`
  - `github-copilot[bot]`
  - `copilot`
  - `copilot[bot]`
  - `chatgpt-codex-connector`
  - `chatgpt-codex-connector[bot]`
  - `Copilot`
- 照合は大文字小文字を区別しません

### 6. wait / retry 調整

review 到着待ちの調整変数:
- `COPILOT_REVIEW_WAIT_MINUTES`
- `COPILOT_REVIEW_MAX_ATTEMPTS`

既定は 5 分 x 3 回です。これらは `AE_AUTOMATION_PROFILE` でも一括管理できます。

### 7. 例外運用

AI review を使えない環境では、以下のいずれかで運用します。
- `gate` を Required checks に含めない
- `AI_REVIEW_ACTORS=(empty)` を設定して actor 判定を明示的に無効化する

この経路は通常 baseline ではなく、例外運用として扱います。

### 8. トラブルシューティング

- AI review が review ではなく comment としてしか出ない:
  - PR 側の review UI から AI review を起動する
- thread が unresolved のまま残る:
  - 対応後に PR 上で `Resolve conversation` を実行する
- auto-fix が thread を解消したが push が発生しない:
  - Actions から `Copilot Review Gate` を手動 rerun する
- `pull_request_review` 経路が `action_required` になる:
  - 最終判定は PR head SHA 上の `Copilot Review Gate / gate` を基準に見る
  - 必要なら `workflow_dispatch` で `pr_number` を指定して再評価する
- 同一 head SHA で success / failure が混在する:
  - failed の `Copilot Review Gate` run を rerun する
  - current head SHA の最新 check run を優先して判定する
- actor を検出しない:
  - `AI_REVIEW_ACTORS` または fallback の `COPILOT_ACTORS` に実 actor 名が含まれているか確認する
- fork PR で comment が出ない:
  - workflow の判定自体は実行されるが、comment 側の証跡は出ない場合がある
- Required checks が `Expected — Waiting for status to be reported` のまま:
  - branch protection の required context 名が実ジョブ名と一致しているか確認する
  - workflow が PR 条件で起動しているか確認する
  - `docs/ci/branch-protection-operations.md` を参照

### 9. 関連ドキュメント

- `docs/ci/copilot-auto-fix.md`
- `docs/ci/pr-automation.md`
- `docs/ci/branch-protection-operations.md`
- `docs/ci/automation-profiles.md`
