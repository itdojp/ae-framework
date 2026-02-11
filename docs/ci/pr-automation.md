# PR Automation (Copilot Review -> Auto Fix -> Auto Merge)

> Language / 言語: English | 日本語

---

## English (Summary)

This document describes an end-to-end PR automation runbook:
- Require Copilot review + resolved threads (Copilot Review Gate)
- Auto-apply Copilot ```` ```suggestion ```` blocks (Copilot Auto Fix)
- Enable GitHub auto-merge when eligible (Auto Merge)

It is controlled per repository via GitHub Repository Variables.

Primary sources:
- Workflows: `.github/workflows/copilot-review-gate.yml`, `.github/workflows/copilot-auto-fix.yml`, `.github/workflows/pr-ci-status-comment.yml`
- Scripts: `scripts/ci/copilot-auto-fix.mjs`, `scripts/ci/auto-merge-enabler.mjs`, `scripts/ci/auto-merge-eligible.mjs`

---

## 日本語

## 1. 目的

PR運用を以下の形に収束させます。

- (1) PR作成
- (2) GitHub Copilotレビュー
- (3) レビュー対応（auto-fix）
- (4) マージ操作の省略（auto-merge）

ゴール:
- (2)の後に(3)を自動化し、(4)の人手操作を省略する
- ただし品質ゲート（Branch protection の Required checks）は維持する

非ゴール:
- Copilotレビュー自体の生成を強制的に自動化する（GitHub側機能の運用に依存）

## 2. 全体フロー（実装準拠）

### 2.1 Gate（レビュー必須化）

- `Copilot Review Gate / gate`（`.github/workflows/copilot-review-gate.yml`）
  - Copilotレビューの存在
  - Copilotが関与したスレッドがすべて `isResolved=true`

### 2.2 Auto Fix（suggestion 自動適用）

- `Copilot Auto Fix`（`.github/workflows/copilot-auto-fix.yml`）
  - `pull_request_review: submitted` で起動
  - Copilotのインラインコメント本文の ```` ```suggestion ```` を抽出し、PRへ適用（commit + push）
  - 適用（または既適用）と判断できた Copilot スレッドを resolve（保守的）

重要:
- Copilotが「コメント」だけを残し、レビューとして `submitted` されない場合は、auto-fix も gate も期待通りに動きません。
- fork PR の扱い:
  - auto-fix は fork PR を workflow 条件で除外します（`.github/workflows/copilot-auto-fix.yml`）。
  - auto-merge は `pull_request` 経路では fork PR を除外しますが、`schedule` 経路は open PR を列挙するため fork PR も対象になり得ます（`.github/workflows/pr-ci-status-comment.yml`, `scripts/ci/auto-merge-enabler.mjs`）。

### 2.3 Auto Merge（GitHub auto-merge の自動有効化）

- `PR Maintenance`（`.github/workflows/pr-ci-status-comment.yml`）
  - 条件成立時に `gh pr merge --auto --squash` を実行し、GitHub auto-merge を有効化
  - 実マージは GitHub が実施（条件成立時）

注意:
- GitHub リポジトリ設定で "Allow auto-merge" が無効な場合、`gh pr merge --auto` は失敗します。

## 3. 有効化（プロジェクト単位）

いずれも GitHub Repository Variables（Settings -> Secrets and variables -> Actions -> Variables）で制御します。

### 3.1 推奨導入順（手戻りを減らす）

1. Branch protection で Required checks を整備（最小: `Verify Lite / verify-lite` + `Copilot Review Gate / gate`）
2. `AE_COPILOT_AUTO_FIX=1` + `AE_COPILOT_AUTO_FIX_SCOPE=docs` で docs領域から auto-fix を段階導入
3. `AE_AUTO_MERGE=1` + `AE_AUTO_MERGE_MODE=label` で opt-in から auto-merge を段階導入
4. 問題がなければスコープ/モードを拡張（`all` へ）

### 3.2 変数セット例（保守的）

auto-fix（docsのみ）:
- `AE_COPILOT_AUTO_FIX=1`
- `AE_COPILOT_AUTO_FIX_SCOPE=docs`（既定）
- `AE_COPILOT_AUTO_FIX_LABEL=`（任意。設定時はラベルopt-in必須）

auto-merge（ラベルopt-in）:
- `AE_AUTO_MERGE=1`
- `AE_AUTO_MERGE_MODE=label`
- `AE_AUTO_MERGE_LABEL=auto-merge`

`AE_COPILOT_AUTO_FIX_SCOPE=docs` の安全設計（A）:
- PR差分に `docs/**` と `README.md` 以外が含まれる場合、auto-fix 全体をスキップします（`scripts/ci/copilot-auto-fix.mjs` の allowlist に準拠）。

### 3.3 全PR自動マージ（積極設定）

- `AE_AUTO_MERGE_MODE=all`（既定）

注意:
- 影響範囲が大きいため、まず `label` モードで運用設計と例外対応を固めることを推奨します。

## 4. PR作者の運用手順（最短）

1. PR作成（必要なら opt-in ラベルを付与）
2. PR画面の Copilot パネルからレビューを実行し、レビューが `submitted` されるのを待つ
3. `Copilot Auto Fix` の実行結果コメントを確認（marker: `<!-- AE-COPILOT-AUTO-FIX v1 -->`）
4. `Copilot Review Gate / gate` が green であることを確認（未解決スレッドは Resolve）
5. 条件が揃うと `PR Maintenance` が auto-merge を有効化し、GitHubが自動マージします（marker: `<!-- AE-AUTO-MERGE-STATUS v1 -->`）

## 5. トラブルシューティング

### 5.1 Copilot Review Gate が失敗する

- "No Copilot review found"
  - Copilotレビューが `submitted` されていない（コメントのみ）可能性
  - `COPILOT_ACTORS` が実アカウント名と一致しているか確認（`.github/workflows/copilot-review-gate.yml`）
  - wait/retry は `COPILOT_REVIEW_WAIT_MINUTES` / `COPILOT_REVIEW_MAX_ATTEMPTS` を調整（workflow env）
- "Unresolved Copilot review threads"
  - PR上で Resolve conversation
  - auto-fix が commit/push を行わない場合（既適用など）、ゲート再評価が走らないことがあるため、Actions から gate を rerun
  - auto-fix が動作している場合は、auto-fix の結果コメント更新をトリガーに gate が再実行されます（`issue_comment` 経路）

### 5.2 Copilot Auto Fix がスキップされる

- `AE_COPILOT_AUTO_FIX` が未設定（OFF）
- `AE_COPILOT_AUTO_FIX_LABEL` を設定しているがラベルが付いていない
- `AE_COPILOT_AUTO_FIX_SCOPE=docs` で docs外差分が混在（安全側で全スキップ）
- PR head が進んだ、または review comment の `commit_id` が head と一致しない（行番号ズレ回避のため）

### 5.3 auto-merge が有効化されない

- `AE_AUTO_MERGE=1` が未設定（OFF）
- `AE_AUTO_MERGE_MODE=label` でラベル不足、または `AE_AUTO_MERGE_LABEL` 未設定
- Branch protection の required checks が空、または保護情報取得ができない（fail-closed）
- repo側で "Allow auto-merge" が無効
- PRが `draft` / `mergeable != MERGEABLE` / required checks pending

### 5.4 GitHub API の 429 / secondary rate limit

`gh` CLI 経由のAPI呼び出しは GitHub secondary rate limit（HTTP 429）で失敗することがあります。
本リポジトリのCIスクリプトは `scripts/ci/lib/gh-exec.mjs` により retry/backoff を行います。

調整用ENV（必要時のみ）:
- `AE_GH_RETRY_MAX_ATTEMPTS`（既定 8）
- `AE_GH_RETRY_INITIAL_DELAY_MS`（既定 750）
- `AE_GH_RETRY_MAX_DELAY_MS`（既定 60000）
- `AE_GH_THROTTLE_MS`（既定 0。`gh` 呼び出し間の最小間隔ms）
- `AE_GH_RETRY_DEBUG=1`（retryログ出力）
- `AE_GH_RETRY_NO_SLEEP=1`（テスト用途: sleep無効）

それでも失敗する場合は、Actions の rerun（failedのみ）で再試行してください。

補足:
- CI で調整する場合、これらは Repository Variables として設定し、ワークフロー側で `env:` に渡します（本リポジトリの `copilot-auto-fix.yml` / `pr-ci-status-comment.yml` は `vars.*` を参照）。

## 6. 参照

- `docs/ci/copilot-review-gate.md`
- `docs/ci/copilot-auto-fix.md`
- `docs/ci/auto-merge.md`
- `docs/ci/branch-protection-operations.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/product/MINIMAL-ADOPTION.md`
