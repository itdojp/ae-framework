---
docRole: ssot
lastVerified: '2026-03-22'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Auto Merge（GitHub Auto-merge の自動有効化）

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
This document defines how `ae-framework` automatically enables GitHub auto-merge when a pull request is mergeable and satisfies the required checks and review conditions.

Notes:
- This automation only enables GitHub auto-merge. GitHub performs the actual merge after conditions are satisfied.
- If branch protection is incomplete, the automation cannot infer the required checks or review constraints correctly.
- If the repository setting `Allow auto-merge` is disabled, `gh pr merge --auto` fails even when the PR is otherwise eligible.

Related:
- End-to-end PR automation flow: `docs/ci/pr-automation.md`

### 2. Enablement (repository level)
This feature is controlled per repository through GitHub Repository Variables.

Supplement:
- `AE_AUTOMATION_PROFILE` can provide the default auto-merge settings, unless an explicit `AE_AUTO_MERGE*` variable overrides them.
- Details: `docs/ci/automation-profiles.md`

#### 2.1 Required toggle
- Set `AE_AUTO_MERGE=1` to enable the feature.
- If it is unset or not equal to `1`, the auto-merge job in `pr-ci-status-comment.yml` does not run.

#### 2.2 Selection mode
Use `AE_AUTO_MERGE_MODE` to select which PRs are eligible.

- `AE_AUTO_MERGE_MODE=all` (default): evaluate every eligible PR
- `AE_AUTO_MERGE_MODE=label`: only evaluate PRs with `AE_AUTO_MERGE_LABEL`

When `AE_AUTO_MERGE_MODE=label` is used:
- `AE_AUTO_MERGE_LABEL` must be set
- if the label is missing on the PR, auto-merge is not enabled

#### 2.3 Risk label condition
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1` (default): only PRs labeled `risk:low` are eligible
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=0`: disable the risk label restriction

#### 2.4 Change Package condition
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1` (default): require Change Package Validation in the PR summary
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=1` (default): allow `WARN`
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=0`: only `PASS` is allowed

### 3. Current implementation
- Workflow: `.github/workflows/pr-ci-status-comment.yml`
- Main script: `scripts/ci/auto-merge-enabler.mjs`
- Eligibility probe: `scripts/ci/auto-merge-eligible.mjs`

Behavior:
- on `pull_request`, the workflow evaluates the current PR
- on `schedule`, it enumerates open PRs and evaluates them up to the configured limit
- when a PR is eligible, the script runs `gh pr merge --auto --squash`

Assumption:
- GitHub-hosted `ubuntu-latest` is the default runner model
- on self-hosted runners, `gh` CLI must be available

### 4. Eligibility
Auto-merge is enabled only when the following are true:
- the PR is not a draft
- `mergeable == MERGEABLE`
- all required checks from branch protection are green
- if branch protection requires reviews, `reviewDecision == APPROVED`
- if `AE_AUTO_MERGE_MODE=label`, the configured label is present
- if `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1`, `risk:low` is present
- if `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1`, Change Package Validation is within the allowed status set

Branch protection note:
- if the base branch is protected but protection metadata cannot be retrieved, the logic fails closed and does not enable auto-merge

### 5. PR status comment
`scripts/ci/auto-merge-enabler.mjs` upserts a status comment on the PR.

- marker: `<!-- AE-AUTO-MERGE-STATUS v1 -->`
- typical contents: mergeable state, review/check aggregates, and reasons why auto-merge is not enabled

### 6. Manual eligibility check
You can run `PR Maintenance` from Actions UI using `workflow_dispatch`.

- `mode=eligibility`
- `pr_number=<target PR>`
- `enable_auto_merge=true` enables auto-merge when the PR is eligible

This path runs `scripts/ci/auto-merge-eligible.mjs` and prints the result to standard output.

### 7. Troubleshooting
- Auto-merge is not enabled
  - verify branch protection required checks and review requirements
  - if `AE_AUTO_MERGE_MODE=label`, verify `AE_AUTO_MERGE_LABEL` and the PR label
  - if `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1`, verify `risk:low`
  - if `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1`, verify the Change Package Validation section in the PR summary
  - check whether branch protection metadata retrieval failed closed
- Self-hosted runner
  - install `gh` CLI
- GitHub API 429 / secondary rate limit
  - adjust `AE_GH_THROTTLE_MS` and `AE_GH_RETRY_*` if required
  - see `docs/ci/pr-automation.md` and `scripts/ci/lib/gh-exec.mjs`

---

## 日本語

## 1. 目的

PR の状態が「マージ可能」かつ「Required checks/レビュー条件が満たされている」場合に、GitHub の auto-merge（`--auto`）を **自動で有効化**します。

注意:
- ここで行うのは「auto-merge の有効化」です。実際のマージは GitHub が条件成立後に実施します。
- ブランチ保護の設定が不十分な場合、CI/レビュー要件を正しく推論できません（Required checks が空の場合など）。
- GitHub リポジトリ設定で "Allow auto-merge" が無効な場合、`gh pr merge --auto` は失敗します。

関連:
- PR自動化の運用全体像（Copilot→auto-fix→auto-merge）: `docs/ci/pr-automation.md`

## 2. 有効化（プロジェクト単位）

本機能は **リポジトリ毎**に GitHub Repository Variables で制御します。

補足:
- `AE_AUTOMATION_PROFILE` を設定すると、auto-merge 関連の既定値も自動解決されます（個別変数が優先）。
- 詳細: `docs/ci/automation-profiles.md`

### 2.1 必須（ON/OFF）
- `AE_AUTO_MERGE=1` を設定すると有効化します。
- 未設定/`1` 以外の場合、`pr-ci-status-comment.yml` の auto-merge ジョブは起動しません。

### 2.2 方式（全PR / ラベルopt-in）

`AE_AUTO_MERGE_MODE` で対象PRの選別方式を指定できます。

- `AE_AUTO_MERGE_MODE=all`（既定）: 条件を満たす PR をすべて対象
- `AE_AUTO_MERGE_MODE=label`: `AE_AUTO_MERGE_LABEL` を付与した PR のみ対象

`AE_AUTO_MERGE_MODE=label` の場合:
- `AE_AUTO_MERGE_LABEL`（例: `auto-merge`）を必ず設定してください
- 指定ラベルが PR に付与されていない場合、auto-merge は有効化されません

### 2.3 リスクラベル条件（既定）

- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1`（既定）: `risk:low` ラベル付き PR のみ auto-merge 対象
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=0`: リスクラベル制約を無効化

### 2.4 Change Package 条件（既定）

- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1`（既定）: PR Summary（`<!-- AE-PR-SUMMARY -->`）に Change Package Validation が存在することを要求
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=1`（既定）: validation が `WARN` でも許可
- `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=0`: validation は `PASS` のみ許可（`WARN` はブロック）

## 3. 動作概要（実装準拠）

- Workflow: `.github/workflows/pr-ci-status-comment.yml`
  - `pull_request` / `schedule` / `workflow_dispatch` で起動
  - `enable-auto-merge` ジョブが `node scripts/ci/auto-merge-enabler.mjs` を実行
- `scripts/ci/auto-merge-enabler.mjs` は open PR を評価し、eligible なら `gh pr merge --auto --squash` を実行
  - `pull_request` イベント時は `PR_NUMBER` が渡され、単一 PR を処理
  - `schedule` 実行時は open PR を列挙して処理（上限あり）

前提:
- GitHub-hosted runner（`ubuntu-latest`）想定。self-hosted の場合は `gh` CLI が必要です。

## 4. Eligibility（有効化条件）

`ae-framework` は以下を満たす場合に auto-merge を有効化します（一次情報: `scripts/ci/auto-merge-enabler.mjs`）。

- PR が draft でない
- `mergeable == MERGEABLE`
- ブランチ保護から取得した Required checks がすべて成功（failure/pending が 0）
- ブランチ保護のレビュー要件がある場合、`reviewDecision == APPROVED`
- `AE_AUTO_MERGE_MODE=label` の場合、`AE_AUTO_MERGE_LABEL` が付与されている
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1` の場合、`risk:low` が付与されている
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1` の場合、Change Package Validation が `PASS`（または `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN=1` なら `WARN` も可）

ブランチ保護の扱い:
- base ブランチが「保護されている」場合に protection 情報が取得できないときは fail-closed（auto-merge を有効化しない）

## 5. PR へのステータスコメント

`scripts/ci/auto-merge-enabler.mjs` は PR にステータスコメントを upsert します。

- marker: `<!-- AE-AUTO-MERGE-STATUS v1 -->`
- 内容例: mergeable / review / checks の集計、非対象理由（label不足、checks pending 等）

## 6. 手動実行（eligibility 判定）

Actions UI から `PR Maintenance`（`.github/workflows/pr-ci-status-comment.yml`）を `workflow_dispatch` で実行できます。

- `mode=eligibility`
- `pr_number=<対象PR番号>`
- `enable_auto_merge=true` を指定すると eligible 時に auto-merge を有効化

これは `scripts/ci/auto-merge-eligible.mjs` が PR を評価し、結果を標準出力に出します。

## 7. トラブルシューティング

- auto-merge が有効化されない:
  - Required checks / required reviews がブランチ保護に設定されているか確認
  - `AE_AUTO_MERGE_MODE=label` の場合、`AE_AUTO_MERGE_LABEL` が設定され PR に付与されているか確認
  - `AE_AUTO_MERGE_REQUIRE_RISK_LOW=1` の場合、`risk:low` が付与されているか確認
  - `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1` の場合、PR summary に `Change Package Validation` セクションが存在し、結果が許容範囲か確認
  - base ブランチ保護が取得不可になっていないか（token権限/Not Found）確認
- self-hosted runner:
  - `gh` CLI の導入が必要です
- GitHub API 429 / secondary rate limit:
  - `gh` の一時的失敗が発生する場合があります（HTTP 429 等）
  - 必要に応じて `AE_GH_THROTTLE_MS` と `AE_GH_RETRY_*` を調整してください（詳細: `docs/ci/pr-automation.md` / 実装: `scripts/ci/lib/gh-exec.mjs`）。
