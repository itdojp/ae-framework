# Codex Autopilot Lane

`Codex Autopilot Lane` は、`autopilot:on` ラベル付きPRを対象に、レビュー対応から auto-merge 有効化までを自動で進める opt-in レーンです。

一次情報:
- `.github/workflows/codex-autopilot-lane.yml`
- `scripts/ci/codex-autopilot-lane.mjs`
- `scripts/ci/copilot-auto-fix.mjs`
- `scripts/ci/auto-merge-enabler.mjs`

## 1. 有効化

Repository Variables:

- `AE_CODEX_AUTOPILOT_ENABLED=1`（必須）
- `AE_AUTOPILOT_MAX_ROUNDS`（既定 `3`）
- `AE_AUTOPILOT_ROUND_WAIT_SECONDS`（既定 `8`）
- `AE_AUTOPILOT_DRY_RUN=1` で副作用なし検証

補足:
- `workflow_dispatch` は `AE_CODEX_AUTOPILOT_ENABLED` 未設定でも実行可能（手動検証用）

## 2. 起動条件

- `pull_request`（opened/synchronize/reopened/labeled/ready_for_review）
- `issue_comment`（`/autopilot run`）
- `workflow_dispatch`（`pr_number` 必須）

対象PR条件:
- `autopilot:on` ラベルが付与されていること
- draft ではないこと
- fork PR ではないこと（権限の都合で運用非推奨）

## 3. 状態遷移（実装）

1. PR状態を取得（mergeability / labels / check rollup）
2. `mergeState=BEHIND` なら `PR Maintenance` の update-branch を dispatch
3. Copilot未解決スレッドまたは gate failure/missing の場合:
   - `copilot-auto-fix.mjs` を force mode で実行
   - `copilot-review-gate.yml` を dispatch
4. `auto-merge-enabler.mjs` で auto-merge 有効化を試行
5. 収束しない場合は `status:blocked` を付与して停止

PRコメント（upsert）:
- marker: `<!-- AE-CODEX-AUTOPILOT v1 -->`

## 4. 安全設計

- opt-in ラベル必須（`autopilot:on`）
- ラウンド上限あり（`AE_AUTOPILOT_MAX_ROUNDS`）
- dry-run あり（`AE_AUTOPILOT_DRY_RUN=1`）
- 競合状態（`CONFLICTING` / `DIRTY`）は自動停止して `status:blocked`

## 5. 運用メモ

- まず `AE_AUTOPILOT_DRY_RUN=1` で挙動確認してから本番有効化
- 自動復旧は `PR Self-Heal`（`pr-self-heal.yml`）と併用すると停止率を下げられます
- auto-merge が有効化されない場合は branch protection / required checks / label条件を確認してください
