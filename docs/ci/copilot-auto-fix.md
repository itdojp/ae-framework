# Copilot Auto Fix（suggestion 自動適用）

> Language / 言語: English | 日本語

---

## English (Summary)

- Automatically applies GitHub Copilot review ```` ```suggestion ```` blocks to the PR branch.
- Can be enabled per repository with variables (`AE_COPILOT_AUTO_FIX`, `AE_COPILOT_AUTO_FIX_SCOPE`, `AE_COPILOT_AUTO_FIX_LABEL`).
- In `docs` scope mode, the entire auto-fix is skipped if the PR contains non-doc changes (fail-safe).

Primary sources: `.github/workflows/copilot-auto-fix.yml`, `scripts/ci/copilot-auto-fix.mjs`, `scripts/ci/lib/automation-config.mjs`.

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
- 未設定/`1` 以外の場合、`.github/workflows/copilot-auto-fix.yml` は起動しません。

### 2.2 スコープ（docs / all）

- `AE_COPILOT_AUTO_FIX_SCOPE=docs`（既定）
  - PR の差分に `docs/**` と `../../README.md` 以外が含まれる場合、**auto-fix 全体をスキップ**します（安全側）
  - 理由は PR コメントに記録します
- `AE_COPILOT_AUTO_FIX_SCOPE=all`
  - すべてのファイルを対象に suggestion 適用を試行します

根拠（実装）:
- allowlist: `docs/**`, `../../README.md`（`scripts/ci/copilot-auto-fix.mjs`）

### 2.3 ラベルopt-in（任意）

`AE_COPILOT_AUTO_FIX_LABEL` を設定すると、PR にそのラベルが付与されている場合のみ auto-fix を実行します。

例:
- `AE_COPILOT_AUTO_FIX_LABEL=copilot-auto-fix`

## 3. 動作概要（実装準拠）

- Workflow: `.github/workflows/copilot-auto-fix.yml`
  - `pull_request_review: submitted` で起動
  - fork PR は対象外
  - `vars.AE_COPILOT_AUTO_FIX == '1'` を満たす場合のみ実行
  - `github.actor` が Copilot 系アクターに一致する場合のみ実行（workflow 側で制限）
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

## 6. PR への実行結果コメント

実行結果は PR コメントとして upsert します（一次情報: `scripts/ci/copilot-auto-fix.mjs`）。

- marker: `<!-- AE-COPILOT-AUTO-FIX v1 -->`
- 主な内容:
  - applied / already / resolved threads
  - changed files
  - skipped の理由（上限あり）

## 7. トラブルシューティング

- ワークフローが起動しない:
  - `AE_COPILOT_AUTO_FIX=1` が設定されているか確認
  - Copilot レビューの実行者が想定アクターに含まれるか確認（workflow の `COPILOT_ACTORS`）
- `AE_COPILOT_AUTO_FIX_SCOPE=docs` でスキップされる:
  - docs 以外の差分が含まれているため。docs のみに分割するか、`AE_COPILOT_AUTO_FIX_SCOPE=all` を検討
- Copilot Review Gate が失敗のまま:
  - auto-fix が commit/push を行わない場合（既適用など）、ゲートの再評価が走らないことがあります
  - auto-fix 結果コメント（marker: `<!-- AE-COPILOT-AUTO-FIX v1 -->`）が作成されると、`agent-commands` が `copilot-review-gate.yml` を `workflow_dispatch` し、gate を PR head に対して再実行します（通常は手動 rerun 不要）
  - それでも更新されない場合は、`Copilot Review Gate` の再実行（Actions UI）や、PR の更新（空コミット等）で再評価してください
- GitHub API 429 / secondary rate limit:
  - `gh` の一時的失敗が発生する場合があります（HTTP 429 等）
  - 必要に応じて `AE_GH_RETRY_*` や `AE_GH_THROTTLE_MS` を調整してください（詳細: `docs/ci/pr-automation.md` / 実装: `scripts/ci/lib/gh-exec.mjs`）。
