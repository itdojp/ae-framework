# Auto Merge（GitHub Auto-merge の自動有効化）

> Language / 言語: English | 日本語

---

## English (Summary)

- This document describes how `ae-framework` can enable GitHub auto-merge automatically per repository.
- It is controlled by GitHub Repository Variables (`AE_AUTO_MERGE`, `AE_AUTO_MERGE_MODE`, `AE_AUTO_MERGE_LABEL`).
- Eligibility is evaluated against branch protection (required checks + required reviews) and PR state.

Primary sources: `.github/workflows/pr-ci-status-comment.yml`, `scripts/ci/auto-merge-enabler.mjs`, `scripts/ci/auto-merge-eligible.mjs`.

---

## 日本語

## 1. 目的

PR の状態が「マージ可能」かつ「Required checks/レビュー条件が満たされている」場合に、GitHub の auto-merge（`--auto`）を **自動で有効化**します。

注意:
- ここで行うのは「auto-merge の有効化」です。実際のマージは GitHub が条件成立後に実施します。
- ブランチ保護の設定が不十分な場合、CI/レビュー要件を正しく推論できません（Required checks が空の場合など）。

## 2. 有効化（プロジェクト単位）

本機能は **リポジトリ毎**に GitHub Repository Variables で制御します。

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
  - base ブランチ保護が取得不可になっていないか（token権限/Not Found）確認
- self-hosted runner:
  - `gh` CLI の導入が必要です

*** Add File: ae-framework/docs/ci/copilot-auto-fix.md
# Copilot Auto Fix（suggestion 自動適用）

> Language / 言語: English | 日本語

---

## English (Summary)

- Automatically applies GitHub Copilot review ` ```suggestion` blocks to the PR branch.
- Can be enabled per repository with variables (`AE_COPILOT_AUTO_FIX`, `AE_COPILOT_AUTO_FIX_SCOPE`, `AE_COPILOT_AUTO_FIX_LABEL`).
- In `docs` scope mode, the entire auto-fix is skipped if the PR contains non-doc changes (fail-safe).

Primary sources: `.github/workflows/copilot-auto-fix.yml`, `scripts/ci/copilot-auto-fix.mjs`.

---

## 日本語

## 1. 目的

Copilot レビューのインラインコメントに含まれる ` ```suggestion` ブロックを抽出し、PR ブランチへ **自動適用（コミット + push）**します。

狙い:
- (1)PR作成 → (2)Copilotレビュー → (3)対応 のうち、(3)の一部を自動化する
- docs のような低リスク領域から段階導入する

## 2. 有効化（プロジェクト単位）

本機能は **リポジトリ毎**に GitHub Repository Variables で制御します。

### 2.1 必須（ON/OFF）
- `AE_COPILOT_AUTO_FIX=1` を設定すると有効化します。
- 未設定/`1` 以外の場合、`.github/workflows/copilot-auto-fix.yml` は起動しません。

### 2.2 スコープ（docs / all）

- `AE_COPILOT_AUTO_FIX_SCOPE=docs`（既定）
  - PR の差分に `docs/**` と `README.md` 以外が含まれる場合、**auto-fix 全体をスキップ**します（安全側）
  - 理由は PR コメントに記録します
- `AE_COPILOT_AUTO_FIX_SCOPE=all`
  - すべてのファイルを対象に suggestion 適用を試行します

根拠（実装）:
- allowlist: `docs/**`, `README.md`（`scripts/ci/copilot-auto-fix.mjs`）

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
  - PR review comments（`pulls/{number}/comments`）から ` ```suggestion` を抽出
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

また、ファイル書き込みは repo 外や symlink を拒否します（`realpath` + `lstat`）。

## 5. 対応範囲（suggestion の扱い）

- 対応: レビューコメント本文の ` ```suggestion` ブロック（最初の1つのみ）
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
  - `Copilot Review Gate` の再実行（Actions UI）や、PR の更新（空コミット等）で再評価してください

