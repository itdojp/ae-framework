---
docRole: ssot
lastVerified: '2026-03-23'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# PR Automation (AI Review -> Auto Fix -> Auto Merge)

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This document defines the target pull request automation flow for `ae-framework`.

Target sequence:
- create the PR
- commit a plan artifact for `risk:high` changes
- run AI review
- respond to review through auto-fix where applicable
- avoid manual merge operations by enabling GitHub auto-merge

Goals:
- automate the review-response loop after AI review
- preserve branch protection and required quality gates

Non-goal:
- forcing GitHub to generate AI reviews outside the platform feature set

### 2. End-to-end flow

#### 2.1 Gate (review is required)

- `Copilot Review Gate / gate` (`.github/workflows/copilot-review-gate.yml`)
  - requires at least one allowed AI reviewer review
  - requires every AI-involved review thread to be resolved

#### 2.2 Auto Fix (apply ```` ```suggestion ```` blocks)

- `Copilot Auto Fix` (`.github/workflows/copilot-auto-fix.yml`)
  - runs on `pull_request_review: submitted`
  - extracts ```` ```suggestion ```` blocks from inline comments by allowed AI reviewers and applies them to the PR
  - conservatively resolves threads that were applied or are already satisfied
  - suppresses duplicate execution when `autopilot:on` and `AE_CODEX_AUTOPILOT_ENABLED=1` are both active

Important:
- if an AI reviewer leaves only comments without a submitted review, neither auto-fix nor the gate behaves as intended
- fork PRs are excluded from the `pull_request` auto-fix path
- fork PRs are excluded from the `pull_request` auto-merge path, but schedule-based maintenance can still enumerate open fork PRs

#### 2.3 Auto Merge (automatic enablement of GitHub auto-merge)

- `PR Maintenance` (`.github/workflows/pr-ci-status-comment.yml`)
  - runs `gh pr merge --auto --squash` when conditions are satisfied
  - GitHub performs the actual merge later
  - the `summarize` job can append report-only `hook-feedback` when a successful `verify-lite-report` artifact exists for the same head SHA

Important:
- if repository settings disable `Allow auto-merge`, `gh pr merge --auto` fails even when checks are green

### 3. Enablement (repository level)

All automation is controlled through GitHub Repository Variables (`Settings -> Secrets and variables -> Actions -> Variables`).

#### 3.0 Profile-based setup (recommended)

- `AE_AUTOMATION_PROFILE` applies a bundled default set managed by `automation-config`
  - `conservative` / `balanced` / `aggressive`
- explicit variables override the profile values, including:
  - `AI_REVIEW_ACTORS`
  - `AE_REVIEW_TOPOLOGY`
  - `AE_POLICY_MIN_HUMAN_APPROVALS`
  - `AE_COPILOT_AUTO_FIX*`
  - `AE_AUTO_MERGE*`
  - `AE_GH_*`
  - `COPILOT_REVIEW_*`
  - `AE_AUTOPILOT_AUTO_LABEL`
  - `AE_AUTOPILOT_RISK_POLICY_PATH`
- details: `docs/ci/automation-profiles.md`

#### 3.1 Recommended rollout order

1. Configure branch protection required checks, at minimum `verify-lite`, `policy-gate`, and `gate`
   - `verify-lite` always enforces root-layout checks and enforces required artifact checks for non-docs-only changes
2. Start with `AE_AUTOMATION_PROFILE=conservative` and docs-scope / label opt-in rollout
3. Expand to `balanced` or `aggressive` only after the flow is stable
4. Use explicit variable overrides only when necessary

Supplement:
- this repository manages branch protection through `.github/branch-protection.main.verify-lite-noreview.json`
- `gate` is recommended as a required check because it verifies AI review presence and unresolved review threads

#### 3.1.1 Review topology (solo / team)

`policy-gate` supports both solo and team approval models.

- `AE_REVIEW_TOPOLOGY=team` (default)
  - high-risk PRs require `high_risk.min_human_approvals` from `policy/risk-policy.yml`
- `AE_REVIEW_TOPOLOGY=solo`
  - high-risk PR approvals are evaluated as zero required human approvals
- `AE_POLICY_MIN_HUMAN_APPROVALS=<non-negative int>`
  - explicit override that takes precedence over topology

Notes:
- these variables affect behavior only in versions that include topology-aware `policy-gate` and `policy-gate.yml` integration with `automation-config`
- older versions ignore them for approval judgement
- see `docs/ci/review-topology-matrix.md` for the measurement matrix

Common operator flow in both models:
- create PR -> AI review -> resolve findings -> required checks green -> merge

#### 3.1.2 Recommended baseline by team shape

| Item | solo | team |
| --- | --- | --- |
| `AE_REVIEW_TOPOLOGY` | `solo` | `team` |
| `AE_POLICY_MIN_HUMAN_APPROVALS` | *(empty)* | *(empty)* |
| Branch protection required checks | `verify-lite`, `policy-gate`, `gate` | `verify-lite`, `policy-gate`, `gate` |
| branch rule approving review count | `0` | `0` (`policy-gate` handles high-risk approvals) |
| Flow | PR -> AI review -> auto-fix / reevaluation -> auto-merge | PR -> AI review -> auto-fix / reevaluation -> auto-merge |

Notes:
- if `AE_POLICY_MIN_HUMAN_APPROVALS` is set, it overrides topology
- making branch rules enforce high-risk approvals directly is not recommended for solo operation

#### 3.1.3 Policy engine rollout (`shadow` -> `shadow_strict`)

`policy-gate.yml` can roll out OPA shadow compare through `AE_POLICY_ENGINE_MODE`.

- `shadow` (default): report-only mismatch recording
- `shadow_strict`: mismatches and OPA evaluation errors become blocking

Recommended progression:
1. keep `AE_POLICY_ENGINE_MODE=shadow` and observe `artifacts/ci/policy-shadow-compare-v1.json`
2. move to `shadow_strict` only after mismatch behavior is understood
3. if unexpected divergence grows, roll back to `shadow` and inspect `policy-decision-js-v1.json` vs `policy-decision-opa-v1.json`

Normalization notes:
- unset values are treated as `shadow`
- values are normalized by trim + lowercase
- invalid values fall back to `shadow` and emit a warning from `policy-shadow-compare`

#### 3.2 Example variable set (conservative)

Review topology:
- `AE_REVIEW_TOPOLOGY=team` (default)
- `AE_REVIEW_TOPOLOGY=solo`
- `AE_POLICY_MIN_HUMAN_APPROVALS=` (empty means no override)

Policy engine rollout:
- `AE_POLICY_ENGINE_MODE=shadow` (default, report-only)
- `AE_POLICY_ENGINE_MODE=shadow_strict` (blocking on mismatch / OPA evaluation error)

Auto-fix (docs only):
- `AE_COPILOT_AUTO_FIX=1`
- `AE_COPILOT_AUTO_FIX_SCOPE=docs` (default)
- `AE_COPILOT_AUTO_FIX_LABEL=` (optional; if set, label opt-in becomes required)

Auto-merge (label opt-in):
- `AE_AUTO_MERGE=1`
- `AE_AUTO_MERGE_MODE=label`
- `AE_AUTO_MERGE_LABEL=auto-merge`
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1` (default)
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1` (default)
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=1` (default)

Global emergency stop:
- `AE_AUTOMATION_GLOBAL_DISABLE=1`
  - `true` / `yes` / `on` are treated as enabled values as well

Safety note for `AE_COPILOT_AUTO_FIX_SCOPE=docs`:
- if a PR contains files outside `docs/**` and the repository-root `../README.md`, the whole auto-fix flow is skipped

#### 3.2.1 Recommended mix of `AE_AUTOMATION_PROFILE` plus explicit overrides

| Use case | `AE_AUTOMATION_PROFILE` | Explicit overrides to add |
| --- | --- | --- |
| initial rollout | `conservative` | `AE_REVIEW_TOPOLOGY=solo|team` |
| normal operation | `balanced` | `AE_REVIEW_TOPOLOGY=solo|team`, optionally `AE_COPILOT_AUTO_FIX_SCOPE=docs` |
| aggressive automation | `aggressive` | `AE_REVIEW_TOPOLOGY=team` after high-risk procedures are ready |

Principle:
- choose a profile first, then override only the delta
- when intentionally clearing `AE_COPILOT_AUTO_FIX_LABEL` or `AE_AUTO_MERGE_LABEL`, use `(empty)` per `automation-config` semantics

#### 3.3 Fully automatic merge mode (`all`)

- `AE_AUTO_MERGE_MODE=all` (default)
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1` (`risk:low` required)

Important:
- because this has broader impact, stabilize exception handling in `label` mode before moving to `all`

#### 3.4 Required GitHub-side repository settings

1. General
   - enable `Allow auto-merge`
2. Branch protection (`main`)
   - set `verify-lite`, `policy-gate`, and `gate` as required checks
   - enable `Require branches to be up to date before merging`
3. Actions permissions
   - allow workflows to run with the required `contents: write`, `pull-requests: write`, `issues: write`, and similar permissions where needed
4. AI review enablement
   - enable the GitHub-side review automation used by the chosen AI reviewer
   - naming differs by GitHub plan / feature, so follow the organization-level GitHub administration path

### 4. Short operator runbook

1. Create the PR and add opt-in labels if required
2. For `risk:high`, commit `artifacts/plan/plan-artifact.json|md` so `policy-gate` does not fail on missing required plan artifacts
3. Start the AI review from the PR UI and wait for a submitted review
4. Confirm the `Copilot Auto Fix` result comment (`<!-- AE-COPILOT-AUTO-FIX v1 -->`)
5. Confirm `gate`, `policy-gate`, and `verify-lite` are green, and resolve any remaining review threads
6. Once conditions are satisfied, `PR Maintenance` enables auto-merge and GitHub merges the PR (`<!-- AE-AUTO-MERGE-STATUS v1 -->`)

Supplement:
- if a committed plan artifact exists, `PR Maintenance` appends the schema-validation result to the PR summary
- plan artifact is the pre-implementation review contract; Change Package is the post-implementation evidence contract

#### 4.1 Post-merge release verification path

- use `post-deploy-verify.yml` through `workflow_dispatch`
- local reproduction uses `pnpm run ae-framework -- release verify ...` or `ae release verify`
- `release_tag` is needed only when assurance summary should be loaded from a published release asset
- assurance summary is optional and report-only for post-deploy judgement
- manually running `release-quality-artifacts` only creates an Actions artifact; `release_tag` can reference only a published release asset
- details: `docs/operate/release-engineering.md`

### 5. Troubleshooting

#### 5.1 Copilot Review Gate fails

- `No Copilot review found`
  - the review may not have been submitted and may exist only as comments
  - verify `AI_REVIEW_ACTORS` / backward-compatible `COPILOT_ACTORS`
  - tune `COPILOT_REVIEW_WAIT_MINUTES` / `COPILOT_REVIEW_MAX_ATTEMPTS` if needed
- `Unresolved Copilot review threads`
  - resolve the conversation on the PR
  - if auto-fix does not commit/push, gate reevaluation may not trigger automatically, so rerun the gate from Actions
  - when auto-fix does run, the auto-fix result comment update causes the `dispatch` path to rerun the gate against the PR head
- `pull_request_review run is action_required`
  - the `pull_request_review` path can end as `action_required`
  - final judgement must be based on the PR-head `gate` result, rerunning through `workflow_dispatch` if required
- mixed `gate` success/failure on the same head SHA
  - rerun the failed `Copilot Review Gate` run (`gh run rerun <runId> --failed`)
  - make decisions from the latest `gate` result on the current head SHA

#### 5.2 Copilot Auto Fix is skipped

- `AE_COPILOT_AUTO_FIX` is unset or disabled
- `AE_COPILOT_AUTO_FIX_LABEL` is set but the label is missing
- `AE_COPILOT_AUTO_FIX_SCOPE=docs` and the PR contains non-doc changes
- the PR head advanced, or the review comment `commit_id` no longer matches the current head

#### 5.3 Auto-merge is not enabled

- `AE_AUTO_MERGE=1` is not set
- `AE_AUTO_MERGE_MODE=label` is active but the required label is missing, or `AE_AUTO_MERGE_LABEL` is unset
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1` but `risk:low` is missing
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1` but Change Package Validation is missing or outside the allowed status range
- branch protection metadata is unavailable and the logic failed closed
- repository settings disable `Allow auto-merge`
- the PR is draft, not mergeable, or still has pending required checks

#### 5.4 GitHub API 429 / secondary rate limit

This repository uses `scripts/ci/lib/gh-exec.mjs` for retry and backoff, with defaults managed in `scripts/ci/lib/automation-defaults.mjs` and `scripts/ci/lib/automation-config.mjs`.

Primary tuning variables:
- `AE_GH_RETRY_MAX_ATTEMPTS` (default `8`)
- `AE_GH_RETRY_INITIAL_DELAY_MS` (default `750`)
- `AE_GH_RETRY_MAX_DELAY_MS` (default `60000`)
- `AE_GH_RETRY_MULTIPLIER` (default `2`)
- `AE_GH_RETRY_JITTER_MS` (default `250`)
- `AE_GH_THROTTLE_MS` (default `250`; `0` disables throttling)
- `AE_GH_RETRY_DEBUG=1`
- `AE_GH_RETRY_NO_SLEEP=1`

##### 5.4.1 Retry / wait quick matrix

SSOT references:
- shared defaults: `scripts/ci/lib/automation-defaults.mjs`
- profile overrides and validation: `scripts/ci/lib/automation-config.mjs`
- self-heal defaults: `scripts/ci/pr-self-heal.mjs` and `.github/workflows/pr-self-heal.yml`
- autopilot defaults: `scripts/ci/codex-autopilot-lane.mjs` and `.github/workflows/codex-autopilot-lane.yml`

| Lane | Retry settings | Wait settings | Default | `AE_AUTOMATION_PROFILE` override |
| --- | --- | --- | --- | --- |
| gate (`copilot-review-gate`) | `COPILOT_REVIEW_MAX_ATTEMPTS` | `COPILOT_REVIEW_WAIT_MINUTES` (fixed) | `3` attempts / `5` minutes | conservative `4 / 7`, balanced `3 / 5`, aggressive `2 / 2` |
| autopilot (`codex-autopilot-lane`) | `AE_AUTOPILOT_MAX_ROUNDS` | `AE_AUTOPILOT_ROUND_WAIT_SECONDS`, `AE_AUTOPILOT_WAIT_STRATEGY`, `AE_AUTOPILOT_ROUND_WAIT_MAX_SECONDS` | `3` rounds / `8s` / `fixed` / `8s` | none |
| auto-fix (`copilot-auto-fix`) | no explicit retry variable | code constants, not ENV-overridable | `100ms` paging / `150ms` thread-resolve sleep | none |
| self-heal (`pr-self-heal`) | `AE_SELF_HEAL_MAX_ROUNDS` | `AE_SELF_HEAL_ROUND_WAIT_SECONDS`, `AE_SELF_HEAL_WAIT_STRATEGY`, `AE_SELF_HEAL_ROUND_WAIT_MAX_SECONDS` | `3` rounds / `60s` / `fixed` / `60s` | none |

| Shared `gh-exec` retry/backoff | default | conservative | balanced | aggressive |
| --- | --- | --- | --- | --- |
| `AE_GH_RETRY_MAX_ATTEMPTS` | `8` | `10` | `8` | `6` |
| `AE_GH_RETRY_INITIAL_DELAY_MS` | `750` | `1000` | `750` | `500` |
| `AE_GH_RETRY_MAX_DELAY_MS` | `60000` | `120000` | `60000` | `30000` |
| `AE_GH_RETRY_MULTIPLIER` | `2` | `2` | `2` | `2` |
| `AE_GH_RETRY_JITTER_MS` | `250` | `400` | `250` | `100` |
| `AE_GH_THROTTLE_MS` | `250` | `400` | `300` | `150` |

Notes:
- `automation-config` variables resolve in `explicit -> profile -> default` order
- `AE_AUTOPILOT_ACTIONABLE_COMMAND`, `AE_AUTOPILOT_ACTIONABLE_DRY_RUN`, `AE_AUTOPILOT_MAX_ROUNDS`, and `AE_AUTOPILOT_ROUND_WAIT_*` do not follow profiles
- wait values for `autopilot`, `auto-fix`, and `self-heal` are profile-independent
- if GitHub still fails, retry through Actions rerun (`failed only`)

#### 5.5 Self-Heal

- `PR Self-Heal` (`.github/workflows/pr-self-heal.yml`) can automatically:
  - rerun failed jobs with `gh run rerun --failed`
  - dispatch `PR Maintenance/update-branch` for behind PRs
  - apply `status:blocked` and a summary comment to PRs that do not converge
- enablement variables:
  - `AE_SELF_HEAL_ENABLED=1`
  - `AE_SELF_HEAL_MAX_ROUNDS` (default `3`)
  - `AE_SELF_HEAL_MAX_AGE_MINUTES` (default `180`)
  - `AE_SELF_HEAL_MAX_PRS` (default `20`)
  - `AE_SELF_HEAL_ROUND_WAIT_SECONDS` (default `60`)
  - `AE_SELF_HEAL_WAIT_STRATEGY` (`fixed` by default; `fixed` / `exponential`)
  - `AE_SELF_HEAL_ROUND_WAIT_MAX_SECONDS` (defaults to `AE_SELF_HEAL_ROUND_WAIT_SECONDS`)

#### 5.6 Codex Autopilot Lane (touchless merge opt-in)

- `Codex Autopilot Lane` (`.github/workflows/codex-autopilot-lane.yml`) automates the following for `autopilot:on` PRs:
  - update-branch dispatch
  - Copilot auto-fix in force mode
  - review-gate dispatch
  - auto-merge enable attempt
  - actionable non-suggestion review handling depending on `AE_AUTOPILOT_ACTIONABLE_COMMAND`
    - unset: fail closed with `status:blocked`
    - set: run the command and evaluate the result; `failed>0` or `skipped>0` on active runs still fail closed
- if the PR does not converge, the lane stops with `status:blocked`
- details: `docs/ci/codex-autopilot-lane.md`

Supplement:
- in CI, set these as Repository Variables and pass them into workflow `env:` as needed; current repository workflows already read `vars.*`

#### 5.7 Global kill-switch

- `AE_AUTOMATION_GLOBAL_DISABLE=1` skips the following automation:
  - `Copilot Auto Fix`
  - `PR Maintenance` update-branch / enable-auto-merge
  - `PR Self-Heal`
  - `Codex Autopilot Lane`
- to restore normal operation, return the variable to `0` or unset it, then rerun the required workflows

### 6. References

- `docs/ci/copilot-review-gate.md`
- `docs/ci/copilot-auto-fix.md`
- `docs/ci/auto-merge.md`
- `docs/ci/automation-failure-policies.md`
- `docs/ci/branch-protection-operations.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/automation-permission-boundaries.md`
- `docs/ci/automation-observability.md`
- `docs/ci/workflow-dispatch-validation-2026-02-12.md`
- `docs/product/MINIMAL-ADOPTION.md`
- `docs/operate/release-engineering.md`

---

## 日本語

## 1. 目的

PR運用を以下の形に収束させます。

- (1) PR作成
- (2) high-risk の場合は plan artifact を commit
- (3) GitHub AIレビュー
- (4) レビュー対応（auto-fix）
- (5) マージ操作の省略（auto-merge）

ゴール:
- (3)の後に(4)を自動化し、(5)の人手操作を省略する
- ただし品質ゲート（Branch protection の Required checks）は維持する

非ゴール:
- AIレビュー自体の生成を強制的に自動化する（GitHub側機能の運用に依存）

## 2. 全体フロー（実装準拠）

### 2.1 Gate（レビュー必須化）

- `Copilot Review Gate / gate`（`.github/workflows/copilot-review-gate.yml`）
  - 許可された AI reviewer のレビューが存在する
  - AI reviewer が関与したスレッドがすべて `isResolved=true`

### 2.2 Auto Fix（suggestion 自動適用）

- `Copilot Auto Fix`（`.github/workflows/copilot-auto-fix.yml`）
  - `pull_request_review: submitted` で起動
  - `AI_REVIEW_ACTORS`（未設定時は `COPILOT_ACTORS`）に含まれる actor のインラインコメント本文の ```` ```suggestion ```` を抽出し、PRへ適用（commit + push）
  - 適用（または既適用）と判断できた対象スレッドを resolve（保守的）
  - `autopilot:on` かつ `AE_CODEX_AUTOPILOT_ENABLED=1` のPRでは重複実行を抑止し、`Codex Autopilot Lane` 側で同等処理を継続

重要:
- AI reviewer が「コメント」だけを残し、レビューとして `submitted` されない場合は、auto-fix も gate も期待通りに動きません。
- fork PR の扱い:
  - auto-fix は fork PR を workflow 条件で除外します（`.github/workflows/copilot-auto-fix.yml`）。
  - auto-merge は `pull_request` 経路では fork PR を除外しますが、`schedule` 経路は open PR を列挙するため fork PR も対象になり得ます（`.github/workflows/pr-ci-status-comment.yml`, `scripts/ci/auto-merge-enabler.mjs`）。

### 2.3 Auto Merge（GitHub auto-merge の自動有効化）

- `PR Maintenance`（`.github/workflows/pr-ci-status-comment.yml`）
  - 条件成立時に `gh pr merge --auto --squash` を実行し、GitHub auto-merge を有効化
  - 実マージは GitHub が実施（条件成立時）
  - `summarize` job は同一 head SHA の successful `verify-lite-report` を取得できた場合、`artifacts/agents/hook-feedback.{json,md}` を report-only 生成し、PR summary に追記

注意:
- GitHub リポジトリ設定で "Allow auto-merge" が無効な場合、`gh pr merge --auto` は失敗します。

## 3. 有効化（プロジェクト単位）

いずれも GitHub Repository Variables（Settings -> Secrets and variables -> Actions -> Variables）で制御します。

### 3.0 プロファイル方式（推奨）

- `AE_AUTOMATION_PROFILE` を設定すると、`automation-config` が管理する既定値（actor/review topology/auto-fix/auto-merge/retry/wait など）をまとめて適用できます。
  - `conservative` / `balanced` / `aggressive`
- 個別変数（`AI_REVIEW_ACTORS`, `AE_REVIEW_TOPOLOGY`, `AE_POLICY_MIN_HUMAN_APPROVALS`, `AE_COPILOT_AUTO_FIX*`, `AE_AUTO_MERGE*`, `AE_GH_*`, `COPILOT_REVIEW_*`, `AE_AUTOPILOT_AUTO_LABEL`, `AE_AUTOPILOT_RISK_POLICY_PATH`）を設定した場合は、そちらが優先されます。
- 詳細: `docs/ci/automation-profiles.md`

### 3.1 推奨導入順（手戻りを減らす）

1. Branch protection で Required checks を整備（最小: `Verify Lite / verify-lite` + `Policy Gate / policy-gate`）
   - `verify-lite` は root layout 検査を全PRで必須実行し、required artifacts 検査を非 docs-only 変更で必須実行します
2. `AE_AUTOMATION_PROFILE=conservative` で docs領域 + label opt-in から段階導入
3. 問題がなければ `balanced` / `aggressive` へ拡張
4. 必要時のみ個別変数で上書き

補足:
- 本リポジトリの branch protection 定義（`.github/branch-protection.main.verify-lite-noreview.json`）は `verify-lite` / `policy-gate` / `gate` を Required checks として管理しています。
- `gate` は AI review の存在/未解決スレッドを検証するため、無人運用では Required 化を推奨します。

### 3.1.1 承認トポロジ（1人体制 / 複数人体制）

`policy-gate` の人手承認要件は、次の変数で切替できます。

- `AE_REVIEW_TOPOLOGY=team`（既定）
  - high risk PR は `policy/risk-policy.yml` の `high_risk.min_human_approvals` を要求
- `AE_REVIEW_TOPOLOGY=solo`
  - high risk PR の approvals 要件を 0 として評価
- `AE_POLICY_MIN_HUMAN_APPROVALS=<non-negative int>`
  - 上記より優先される明示 override（例: `2`）

注記:
- これら2変数は、`policy-gate` の topology対応実装と `policy-gate.yml` の automation-config連携が導入されているバージョンで有効です。
- 導入前バージョンでは設定しても approvals 判定は変わりません。
- 実測手順は `docs/ci/review-topology-matrix.md` を参照してください。

運用フローは体制にかかわらず共通です。
- PR作成 → AI review → 指摘解消 → required checks green → merge
- 差分は `policy-gate` の approvals 判定条件のみです。

### 3.1.2 体制別ベースライン設定（推奨）

| 項目 | 1人体制（solo） | 2人以上（team） |
| --- | --- | --- |
| `AE_REVIEW_TOPOLOGY` | `solo` | `team` |
| `AE_POLICY_MIN_HUMAN_APPROVALS` | *(empty)* | *(empty)* |
| Branch protection required checks | `verify-lite`, `policy-gate`, `gate` | `verify-lite`, `policy-gate`, `gate` |
| branch rule の approving review count | `0` | `0`（high risk は `policy-gate` が制御） |
| フロー | PR作成 → AI review → auto-fix/再評価 → auto-merge | PR作成 → AI review → auto-fix/再評価 → auto-merge |

注記:
- `AE_POLICY_MIN_HUMAN_APPROVALS` を設定した場合は topology 設定より優先されます。
- high risk PR の人手承認を branch rule 側で必須化すると、solo 運用と整合しないため非推奨です。

### 3.1.3 Policy Engine ロールアウト（`shadow` → `shadow_strict`）

`policy-gate.yml` の OPA shadow compare は `AE_POLICY_ENGINE_MODE`（Repository Variables）で段階移行できます。

- `shadow`（既定）: 既存互換。`policy-shadow-compare` は report-only で実行し、mismatch は成果物に記録
- `shadow_strict`: `policy-shadow-compare` を strict 判定で実行し、mismatch と OPA evaluation error（`status=error` の非ゼロ終了）を `policy-gate` 失敗として扱う

推奨移行手順:
1. `AE_POLICY_ENGINE_MODE=shadow` のまま `artifacts/ci/policy-shadow-compare-v1.json` を観測し、mismatch 傾向を把握する
2. 運用上許容できる水準まで収束したら `AE_POLICY_ENGINE_MODE=shadow_strict` に切り替える
3. 想定外差分が増えた場合は `AE_POLICY_ENGINE_MODE=shadow` に戻し、`policy-decision-js-v1.json` / `policy-decision-opa-v1.json` 差分を起点に原因を切り分ける

注記:
- 未設定時は `shadow` として扱われます
- 変数値は trim + lowercase で正規化して判定します（例: `Shadow_Strict ` は `shadow_strict` と同等）
- 不正値は `shadow` にフォールバックし、`policy-shadow-compare` が warning を出力します

### 3.2 変数セット例（保守的）

体制切替:
- `AE_REVIEW_TOPOLOGY=team`（既定、複数人体制）
- `AE_REVIEW_TOPOLOGY=solo`（1人体制）
- `AE_POLICY_MIN_HUMAN_APPROVALS=`（空: override無効）

policy engine rollout:
- `AE_POLICY_ENGINE_MODE=shadow`（既定、report-only）
- `AE_POLICY_ENGINE_MODE=shadow_strict`（mismatch / OPA evaluation error をblocking）

auto-fix（docsのみ）:
- `AE_COPILOT_AUTO_FIX=1`
- `AE_COPILOT_AUTO_FIX_SCOPE=docs`（既定）
- `AE_COPILOT_AUTO_FIX_LABEL=`（任意。設定時はラベルopt-in必須）

auto-merge（ラベルopt-in）:
- `AE_AUTO_MERGE=1`
- `AE_AUTO_MERGE_MODE=label`
- `AE_AUTO_MERGE_LABEL=auto-merge`
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1`（既定）
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1`（既定）
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=1`（既定）

全自動化の緊急停止（kill-switch）:
- `AE_AUTOMATION_GLOBAL_DISABLE=1`
  - `true` / `yes` / `on` も有効値として扱います。

`AE_COPILOT_AUTO_FIX_SCOPE=docs` の安全設計（A）:
- PR差分に `docs/**` と README.md 以外が含まれる場合、auto-fix 全体をスキップします（`scripts/ci/copilot-auto-fix.mjs` の allowlist に準拠）。

### 3.2.1 `AE_AUTOMATION_PROFILE` + 個別上書きの推奨セット

| 用途 | `AE_AUTOMATION_PROFILE` | 追加で明示推奨する個別変数 |
| --- | --- | --- |
| 初期導入（安全側） | `conservative` | `AE_REVIEW_TOPOLOGY=solo|team` |
| 通常運用 | `balanced` | `AE_REVIEW_TOPOLOGY=solo|team`, 必要に応じて `AE_COPILOT_AUTO_FIX_SCOPE=docs` |
| 高速運用 | `aggressive` | `AE_REVIEW_TOPOLOGY=team`（高リスク時の運用手順を先に整備） |

原則:
- まず profile を選び、差分だけ個別変数で上書きします。
- `AE_COPILOT_AUTO_FIX_LABEL` / `AE_AUTO_MERGE_LABEL` を意図的に空にする場合は `(empty)` を使います（`automation-config` 仕様）。

### 3.3 全PR自動マージ（積極設定）

- `AE_AUTO_MERGE_MODE=all`（既定）
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1`（`risk:low` 必須）

注意:
- 影響範囲が大きいため、まず `label` モードで運用設計と例外対応を固めることを推奨します。

### 3.4 GitHub 側の必須設定（workflow前提）

Settings（Repository）で次を確認してください。

1. General
   - `Allow auto-merge` を有効化
2. Branch protection (`main`)
   - Required checks に `verify-lite`, `policy-gate`, `gate` を設定
   - `Require branches to be up to date before merging` を有効化（strict）
3. Actions permissions
   - Workflow が必要に応じて `contents: write` / `pull-requests: write` / `issues: write` などの権限で実行できる状態であること
4. AI review 起動設定
   - 利用する AI reviewer（Copilot など）が PR review を自動起票/実行する GitHub 側設定を有効化
   - 設定名称は GitHub プラン/機能差で変わるため、組織の GitHub 管理設定に従って有効化する

## 4. PR作者の運用手順（最短）

1. PR作成（必要なら opt-in ラベルを付与）
2. `risk:high` の場合は `artifacts/plan/plan-artifact.json|md` を commit し、`policy-gate` が `missing required plan artifact` で落ちない状態にする
3. PR画面の Copilot パネルからレビューを実行し、レビューが `submitted` されるのを待つ
4. `Copilot Auto Fix` の実行結果コメントを確認（marker: `<!-- AE-COPILOT-AUTO-FIX v1 -->`）
5. `Copilot Review Gate / gate` と `Policy Gate / policy-gate` が green であることを確認（未解決スレッドは Resolve）
6. 条件が揃うと `PR Maintenance` が auto-merge を有効化し、GitHubが自動マージします（marker: `<!-- AE-AUTO-MERGE-STATUS v1 -->`）

補足:
- `PR Maintenance` は commit 済み `artifacts/plan/plan-artifact.json` がある場合、schema validate 結果を PR summary に追記します。
- plan artifact は人手の事前レビュー契約であり、Change Package は実装後の証跡契約です。

### 4.1 マージ後の release verify 導線

- PRマージ後の運用判定は `post-deploy-verify.yml`（workflow_dispatch）で実施します。
- ローカル再現は `pnpm run ae-framework -- release verify ...`（または `ae release verify`）を使用します。
- `release_tag` は、release asset `quality-artifacts.tgz` から assurance summary を取得して Step Summary に追記したい場合だけ指定します。
- assurance summary は optional / report-only であり、`post-deploy-verify.json` の gate 判定そのものは変えません。
- `release-quality-artifacts` を manual 実行しただけでは Actions artifact しか作られないため、`release_tag` で参照できるのは公開済み release asset がある場合だけです。
- 手順詳細: `docs/operate/release-engineering.md`

## 5. トラブルシューティング

### 5.1 Copilot Review Gate が失敗する

- "No Copilot review found"
  - Copilotレビューが `submitted` されていない（コメントのみ）可能性
  - `AI_REVIEW_ACTORS`（後方互換で `COPILOT_ACTORS`）が実アカウント名と一致しているか確認（`.github/workflows/copilot-review-gate.yml`）
  - wait/retry は `COPILOT_REVIEW_WAIT_MINUTES` / `COPILOT_REVIEW_MAX_ATTEMPTS` を調整（workflow env）
- "Unresolved Copilot review threads"
  - PR上で Resolve conversation
  - auto-fix が commit/push を行わない場合（既適用など）、ゲート再評価が走らないことがあるため、Actions から gate を rerun
  - auto-fix が動作している場合は、auto-fix の結果コメント更新をトリガーに Copilot Review Gate の `dispatch` job（issue_comment→workflow_dispatch）が gate を PR head に対して再実行します（`issue_comment` -> `workflow_dispatch` 経路）
- "pull_request_review run is action_required"
  - `pull_request_review` 経路の実行が `action_required` になる場合があります
  - 最終判定は PR の `Copilot Review Gate / gate` が PR head SHA で green かどうかで確認し、必要なら `workflow_dispatch`（`pr_number` 指定）で再実行
- "Copilot Review Gate / gate が success/failure 混在で残る"
  - 同一 head SHA 上で `gate` の success と failure が混在した場合、失敗した `Copilot Review Gate` ランを `Re-run failed jobs` で再実行してください（CLI例: `gh run rerun <runId> --failed`）
  - head SHA 単位で check-runs を確認し、最新 SHA 上の `gate` を基準に判定してください

### 5.2 Copilot Auto Fix がスキップされる

- `AE_COPILOT_AUTO_FIX` が未設定（OFF）
- `AE_COPILOT_AUTO_FIX_LABEL` を設定しているがラベルが付いていない
- `AE_COPILOT_AUTO_FIX_SCOPE=docs` で docs外差分が混在（安全側で全スキップ）
- PR head が進んだ、または review comment の `commit_id` が head と一致しない（行番号ズレ回避のため）

### 5.3 auto-merge が有効化されない

- `AE_AUTO_MERGE=1` が未設定（OFF）
- `AE_AUTO_MERGE_MODE=label` でラベル不足、または `AE_AUTO_MERGE_LABEL` 未設定
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1` で `risk:low` が未付与
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1` で Change Package Validation 要約が未生成、または許容外（`FAIL` / `WARN`禁止時）
- Branch protection の required checks が空、または保護情報取得ができない（fail-closed）
- repo側で "Allow auto-merge" が無効
- PRが `draft` / `mergeable != MERGEABLE` / required checks pending

### 5.4 GitHub API の 429 / secondary rate limit

`gh` CLI 経由のAPI呼び出しは GitHub secondary rate limit（HTTP 429）で失敗することがあります。
本リポジトリのCIスクリプトは `scripts/ci/lib/gh-exec.mjs` により retry/backoff を行います。
既定値は `scripts/ci/lib/automation-defaults.mjs` と `scripts/ci/lib/automation-config.mjs` で管理されています。

調整用ENV（必要時のみ）:
- `AE_GH_RETRY_MAX_ATTEMPTS`（既定 8）
- `AE_GH_RETRY_INITIAL_DELAY_MS`（既定 750）
- `AE_GH_RETRY_MAX_DELAY_MS`（既定 60000）
- `AE_GH_RETRY_MULTIPLIER`（既定 2。指数backoffの倍率）
- `AE_GH_RETRY_JITTER_MS`（既定 250。retry待機に追加するランダムジッター上限ms）
- `AE_GH_THROTTLE_MS`（既定 250。`gh` 呼び出し間の最小間隔ms。`0` で無効化）
- `AE_GH_RETRY_DEBUG=1`（retryログ出力）
- `AE_GH_RETRY_NO_SLEEP=1`（テスト用途: sleep無効）

### 5.4.1 retry / wait 設定 早見表（gate / autopilot / auto-fix / self-heal）

SSOT:
- 共通既定値: `scripts/ci/lib/automation-defaults.mjs`
- profile 上書き・バリデーション（`AI_REVIEW_ACTORS`, `AE_REVIEW_TOPOLOGY`, `AE_POLICY_MIN_HUMAN_APPROVALS`, `AE_COPILOT_AUTO_FIX*`, `AE_AUTO_MERGE*`, `AE_GH_*`, `COPILOT_REVIEW_*`, `AE_AUTOPILOT_AUTO_LABEL`, `AE_AUTOPILOT_RISK_POLICY_PATH`）: `scripts/ci/lib/automation-config.mjs`
- self-heal lane 既定値: `scripts/ci/pr-self-heal.mjs`（および `.github/workflows/pr-self-heal.yml`）
- autopilot lane 既定値: `scripts/ci/codex-autopilot-lane.mjs`（および `.github/workflows/codex-autopilot-lane.yml`）

| レーン | retry 設定 | wait 設定 | 既定値 | `AE_AUTOMATION_PROFILE` による上書き |
| --- | --- | --- | --- | --- |
| gate (`copilot-review-gate`) | `COPILOT_REVIEW_MAX_ATTEMPTS` | `COPILOT_REVIEW_WAIT_MINUTES`（fixed） | `3` 回 / `5` 分 | conservative: `4` 回 / `7` 分、balanced: `3` 回 / `5` 分、aggressive: `2` 回 / `2` 分 |
| autopilot (`codex-autopilot-lane`) | `AE_AUTOPILOT_MAX_ROUNDS` | `AE_AUTOPILOT_ROUND_WAIT_SECONDS`, `AE_AUTOPILOT_WAIT_STRATEGY`, `AE_AUTOPILOT_ROUND_WAIT_MAX_SECONDS` | `3` 回 / `8` 秒 / `fixed` / `8` 秒 | なし |
| auto-fix (`copilot-auto-fix`) | （明示的な retry 変数なし） | コード定数（ENV で上書き不可）: `COPILOT_AUTO_FIX_PAGING_SLEEP_MS_DEFAULT`, `COPILOT_AUTO_FIX_THREAD_RESOLVE_SLEEP_MS_DEFAULT` | `100ms` / `150ms` | なし |
| self-heal (`pr-self-heal`) | `AE_SELF_HEAL_MAX_ROUNDS` | `AE_SELF_HEAL_ROUND_WAIT_SECONDS`, `AE_SELF_HEAL_WAIT_STRATEGY`, `AE_SELF_HEAL_ROUND_WAIT_MAX_SECONDS` | `3` 回 / `60` 秒 / `fixed` / `60` 秒 | なし |

| 共通 `gh-exec` retry/backoff（全レーン） | default | conservative | balanced | aggressive |
| --- | --- | --- | --- | --- |
| `AE_GH_RETRY_MAX_ATTEMPTS` | `8` | `10` | `8` | `6` |
| `AE_GH_RETRY_INITIAL_DELAY_MS` | `750` | `1000` | `750` | `500` |
| `AE_GH_RETRY_MAX_DELAY_MS` | `60000` | `120000` | `60000` | `30000` |
| `AE_GH_RETRY_MULTIPLIER` | `2` | `2` | `2` | `2` |
| `AE_GH_RETRY_JITTER_MS` | `250` | `400` | `250` | `100` |
| `AE_GH_THROTTLE_MS` | `250` | `400` | `300` | `150` |

注記:
- `automation-config` 管理下の変数は `explicit -> profile -> default` の優先順位で確定します。
- `AE_AUTOPILOT_ACTIONABLE_COMMAND` / `AE_AUTOPILOT_ACTIONABLE_DRY_RUN` / `AE_AUTOPILOT_MAX_ROUNDS` / `AE_AUTOPILOT_ROUND_WAIT_*` は profile 非連動で、Repository Variables の値がそのまま使われます。
- `autopilot` / `auto-fix` / `self-heal` の wait 値は profile 非連動です。

それでも失敗する場合は、Actions の rerun（failedのみ）で再試行してください。

### 5.5 Self-Heal（自動復旧）

- `PR Self-Heal`（`.github/workflows/pr-self-heal.yml`）を有効化すると、次を自動復旧します。
  - failed checks の `gh run rerun --failed`
  - behind PR の `PR Maintenance/update-branch` dispatch
  - 収束しない PR の `status:blocked` ラベル付与と要約コメント
- 有効化変数:
  - `AE_SELF_HEAL_ENABLED=1`
  - `AE_SELF_HEAL_MAX_ROUNDS`（既定 `3`）
  - `AE_SELF_HEAL_MAX_AGE_MINUTES`（既定 `180`）
  - `AE_SELF_HEAL_MAX_PRS`（既定 `20`）
  - `AE_SELF_HEAL_ROUND_WAIT_SECONDS`（既定 `60`）
  - `AE_SELF_HEAL_WAIT_STRATEGY`（既定 `fixed`。`fixed` / `exponential`）
  - `AE_SELF_HEAL_ROUND_WAIT_MAX_SECONDS`（既定 `AE_SELF_HEAL_ROUND_WAIT_SECONDS` と同値）

### 5.6 Codex Autopilot Lane（touchless merge の opt-in）

- `Codex Autopilot Lane`（`.github/workflows/codex-autopilot-lane.yml`）は `autopilot:on` ラベル付きPRで次を自動化します。
  - update-branch dispatch
  - copilot auto-fix（force mode）
  - review gate dispatch
  - auto-merge 有効化試行
  - 非 suggestion の actionable review 指摘が残る場合は `AE_AUTOPILOT_ACTIONABLE_COMMAND` の設定有無で分岐
    - 未設定: fail-closed で `status:blocked`
    - 設定済み: コマンドを実行して結果を判定（`failed>0` または active 実行で `skipped>0` は fail-closed）
- 収束しない場合は `status:blocked` を付与して停止します。
- 詳細: `docs/ci/codex-autopilot-lane.md`
補足:
- CI で調整する場合、これらは Repository Variables として設定し、ワークフロー側で `env:` に渡します（本リポジトリの `copilot-auto-fix.yml` / `pr-ci-status-comment.yml` は `vars.*` を参照）。

### 5.7 グローバル kill-switch

- `AE_AUTOMATION_GLOBAL_DISABLE=1` を設定すると、次の自動実行を停止します（skip）:
  - `Copilot Auto Fix`
  - `PR Maintenance` の `update-branch` / `enable-auto-merge`
  - `PR Self-Heal`
  - `Codex Autopilot Lane`
- 復帰時は `AE_AUTOMATION_GLOBAL_DISABLE=0`（または未設定）へ戻し、必要なworkflowを rerun してください。

## 6. 参照

- `docs/ci/copilot-review-gate.md`
- `docs/ci/copilot-auto-fix.md`
- `docs/ci/auto-merge.md`
- `docs/ci/automation-failure-policies.md`
- `docs/ci/branch-protection-operations.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/automation-permission-boundaries.md`
- `docs/ci/automation-observability.md`
- `docs/ci/workflow-dispatch-validation-2026-02-12.md`
- `docs/product/MINIMAL-ADOPTION.md`
- `docs/operate/release-engineering.md`
