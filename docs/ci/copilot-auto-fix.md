---
docRole: ssot
lastVerified: '2026-03-22'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Copilot Auto Fix（suggestion 自動適用）

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
This document defines how GitHub Copilot review ```` ```suggestion ```` blocks are automatically applied to the PR branch.

Goals:
- automate part of the review-response loop after AI review
- start from lower-risk areas such as docs-only changes

Related:
- end-to-end PR automation flow: `docs/ci/pr-automation.md`

### 2. Enablement (repository level)
This feature is controlled per repository through GitHub Repository Variables.

Supplement:
- `AE_AUTOMATION_PROFILE` can also provide the default auto-fix values, unless explicit variables override them
- details: `docs/ci/automation-profiles.md`

#### 2.1 Required toggle
- set `AE_COPILOT_AUTO_FIX=1` to enable the workflow
- if unset or not equal to `1`, the auto-fix flow is disabled after config resolution and the workflow exits early without applying changes

#### 2.2 Scope
- `AE_COPILOT_AUTO_FIX_SCOPE=docs` (default)
  - if the PR contains files outside `docs/**` and the repository-root README file named README.md, the whole auto-fix flow is skipped as a fail-safe
- `AE_COPILOT_AUTO_FIX_SCOPE=all`
  - suggestions may be applied to all files

Implementation reference:
- allowlist: `docs/**`, repository-root README file named README.md
- source: `scripts/ci/copilot-auto-fix.mjs`

#### 2.3 Label opt-in
If `AE_COPILOT_AUTO_FIX_LABEL` is set, auto-fix runs only when the PR has that label.

Example:
- `AE_COPILOT_AUTO_FIX_LABEL=copilot-auto-fix`

### 3. Current implementation
- Workflow: `.github/workflows/copilot-auto-fix.yml`
  - runs on `pull_request_review: submitted`
  - excludes fork PRs
  - delegates `AE_COPILOT_AUTO_FIX` / `AE_COPILOT_AUTO_FIX_FORCE` gating to `scripts/ci/copilot-auto-fix.mjs` after `automation-config` resolution
  - continues only when `github.actor` matches `AI_REVIEW_ACTORS` or the legacy `COPILOT_ACTORS`
- Script: `node scripts/ci/copilot-auto-fix.mjs`
  - enumerates PR review comments
  - extracts the first ```` ```suggestion ```` block from each eligible comment
  - rewrites the target line range
  - commits and pushes only when file content actually changes
  - resolves only threads judged to be applied or already satisfied

Assumption:
- GitHub-hosted `ubuntu-latest` is the default runner model
- self-hosted runners must provide `gh` CLI

### 4. Safety design
The script skips execution when any of the following is true:
- `PR_HEAD_SHA` does not match the checked-out commit
- the PR head has advanced after the event
- the review comment `commit_id` does not match `PR_HEAD_SHA`
- `AE_COPILOT_AUTO_FIX_SCOPE=docs` but the PR contains non-doc changes

Operational note:
- `AE_COPILOT_AUTO_FIX_FORCE=1` allows forced execution even when `GITHUB_ACTOR` is not a Copilot actor; this is intended for automation lanes such as Codex Autopilot

The implementation also rejects writes outside the repository and symlink-based writes by checking `realpath` and `lstat`.

### 5. Supported suggestion shape
- supported: the first ```` ```suggestion ```` block in a review comment body
- skipped:
  - comments without a suggestion block
  - overlapping suggestions on the same file/range
  - out-of-range line numbers

Supplement:
- comments without a suggestion can still be counted as actionable non-suggestion comments and summarized in the PR result comment
- actual handling of non-suggestion feedback remains manual or delegated to Codex Autopilot Lane

### 6. Result comment on the PR
The script upserts an execution result comment on the PR.

- marker: `<!-- AE-COPILOT-AUTO-FIX v1 -->`
- typical contents:
  - applied / already-applied / resolved thread counts
  - changed files
  - skipped reasons
  - actionable non-suggestion previews

### 7. Troubleshooting
- The workflow does not start
  - verify `AE_COPILOT_AUTO_FIX=1`
  - verify the reviewer actor is included in `AI_REVIEW_ACTORS` or `COPILOT_ACTORS`
- `AE_COPILOT_AUTO_FIX_SCOPE=docs` causes a skip
  - the PR includes non-doc changes; split the PR or consider `AE_COPILOT_AUTO_FIX_SCOPE=all`
- Copilot Review Gate remains failing
  - if auto-fix does not commit/push, the gate reevaluation may not trigger automatically
  - when the auto-fix result comment is updated, `agent-commands` dispatches `copilot-review-gate.yml` against the PR head in the usual path
  - if reevaluation still does not happen, rerun `Copilot Review Gate` or update the PR head
- GitHub API 429 / secondary rate limit
  - tune `AE_GH_RETRY_*` and `AE_GH_THROTTLE_MS` as needed
  - details: `docs/ci/pr-automation.md`, implementation: `scripts/ci/lib/gh-exec.mjs`

---

## 日本語

## 1. 目的

Copilot レビューのインラインコメントに含まれる ```` ```suggestion ```` ブロックを抽出し、PR ブランチへ **自動適用（コミット + push）**します。

狙い:
- (1)PR作成 → (2)Copilotレビュー → (3)対応 のうち、(3)の一部を自動化する
- docs のような低リスク領域から段階導入する

関連:
- PR自動化の運用全体像（Copilot→auto-fix→auto-merge）: `docs/ci/pr-automation.md`

## 2. 有効化（プロジェクト単位）

本機能は **リポジトリ毎**に GitHub Repository Variables で制御します。

補足:
- `AE_AUTOMATION_PROFILE` を設定すると、auto-fix 関連の既定値も自動解決されます（個別変数が優先）。
- 詳細: `docs/ci/automation-profiles.md`

### 2.1 必須（ON/OFF）
- `AE_COPILOT_AUTO_FIX=1` を設定すると有効化します。
- 未設定/`1` 以外の場合、workflow 自体は起動し得ますが、config 解決後に auto-fix を無効として early exit します。

### 2.2 スコープ（docs / all）

- `AE_COPILOT_AUTO_FIX_SCOPE=docs`（既定）
  - PR の差分に `docs/**` と README.md 以外が含まれる場合、**auto-fix 全体をスキップ**します（安全側）
  - 理由は PR コメントに記録します
- `AE_COPILOT_AUTO_FIX_SCOPE=all`
  - すべてのファイルを対象に suggestion 適用を試行します

根拠（実装）:
- allowlist: `docs/**`, README.md（`scripts/ci/copilot-auto-fix.mjs`）

### 2.3 ラベルopt-in（任意）

`AE_COPILOT_AUTO_FIX_LABEL` を設定すると、PR にそのラベルが付与されている場合のみ auto-fix を実行します。

例:
- `AE_COPILOT_AUTO_FIX_LABEL=copilot-auto-fix`

## 3. 動作概要（実装準拠）

- Workflow: `.github/workflows/copilot-auto-fix.yml`
  - `pull_request_review: submitted` で起動
  - fork PR は対象外
  - `AE_COPILOT_AUTO_FIX` / `AE_COPILOT_AUTO_FIX_FORCE` の判定は `automation-config` 解決後に `scripts/ci/copilot-auto-fix.mjs` 側で行う
  - `github.actor` が `AI_REVIEW_ACTORS`（未設定時は `COPILOT_ACTORS`）に一致する場合のみ適用処理を継続
- 実行: `node scripts/ci/copilot-auto-fix.mjs`
  - PR review comments（`pulls/{number}/comments`）から ```` ```suggestion ```` を抽出
  - 行番号レンジ（`start_line`〜`line`）を suggestion で置換
  - 変更があれば commit して PR head ブランチへ push
  - 適用（または既適用）と判断できた Copilot コメントのスレッドのみ resolve（保守的）

前提:
- GitHub-hosted runner（`ubuntu-latest`）想定。self-hosted の場合は `gh` CLI が必要です。

## 4. 安全設計（誤適用防止）

`scripts/ci/copilot-auto-fix.mjs` は以下を満たさない場合、スキップします。

- `PR_HEAD_SHA` が checkout した commit と一致しない
- イベント後に PR head が進んでいる（レビュー時の行番号がズレる可能性があるため）
- review comment の `commit_id` が `PR_HEAD_SHA` と一致しない
- `AE_COPILOT_AUTO_FIX_SCOPE=docs` で docs 以外のファイルが含まれる

運用補足:
- `AE_COPILOT_AUTO_FIX_FORCE=1` を指定すると、`GITHUB_ACTOR` が Copilot アクターでなくても適用処理を実行できます（Codex Autopilot Lane などの自動オーケストレーション用途）。

また、ファイル書き込みは repo 外や symlink を拒否します（`realpath` + `lstat`）。

## 5. 対応範囲（suggestion の扱い）

- 対応: レビューコメント本文の ```` ```suggestion ```` ブロック（最初の1つのみ）
- 非対応（スキップ扱い）:
  - suggestion ブロックが無いコメント
  - suggestion が重なっている（同一ファイルで行レンジが重複）
  - 行番号が範囲外

補足:
- suggestion が無いコメントでも、本文が action 指示として解釈できる場合は `actionable non-suggestion comments` として件数/プレビューを結果コメントへ出力します（自動適用はしません）。
- 非 suggestion 指摘の実際の処理は Codex Autopilot Lane または手動対応に委ねます。

## 6. PR への実行結果コメント

実行結果は PR コメントとして upsert します（一次情報: `scripts/ci/copilot-auto-fix.mjs`）。

- marker: `<!-- AE-COPILOT-AUTO-FIX v1 -->`
- 主な内容:
  - applied / already / resolved threads
  - changed files
  - skipped の理由（上限あり）
  - actionable non-suggestion comments（件数とプレビュー）

## 7. トラブルシューティング

- ワークフローが起動しない:
  - `AE_COPILOT_AUTO_FIX=1` が設定されているか確認
  - レビュー実行者が `AI_REVIEW_ACTORS`（後方互換で `COPILOT_ACTORS`）に含まれるか確認
- `AE_COPILOT_AUTO_FIX_SCOPE=docs` でスキップされる:
  - docs 以外の差分が含まれているため。docs のみに分割するか、`AE_COPILOT_AUTO_FIX_SCOPE=all` を検討
- Copilot Review Gate が失敗のまま:
  - auto-fix が commit/push を行わない場合（既適用など）、ゲートの再評価が走らないことがあります
  - auto-fix 結果コメント（marker: `<!-- AE-COPILOT-AUTO-FIX v1 -->`）が作成されると、`agent-commands` が `copilot-review-gate.yml` を `workflow_dispatch` し、gate を PR head に対して再実行します（通常は手動 rerun 不要）
  - それでも更新されない場合は、`Copilot Review Gate` の再実行（Actions UI）や、PR の更新（空コミット等）で再評価してください
- GitHub API 429 / secondary rate limit:
  - `gh` の一時的失敗が発生する場合があります（HTTP 429 等）
  - 必要に応じて `AE_GH_RETRY_*` や `AE_GH_THROTTLE_MS` を調整してください（詳細: `docs/ci/pr-automation.md` / 実装: `scripts/ci/lib/gh-exec.mjs`）。
