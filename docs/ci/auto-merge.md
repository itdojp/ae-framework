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
- GitHub リポジトリ設定で "Allow auto-merge" が無効な場合、`gh pr merge --auto` は失敗します。

関連:
- PR自動化の運用全体像（Copilot→auto-fix→auto-merge）: `docs/ci/pr-automation.md`

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
- GitHub API 429 / secondary rate limit:
  - `gh` の一時的失敗が発生する場合があります（HTTP 429 等）
  - 必要に応じて `AE_GH_THROTTLE_MS` と `AE_GH_RETRY_*` を調整してください（詳細: `docs/ci/pr-automation.md` / 実装: `scripts/ci/lib/gh-exec.mjs`）。
