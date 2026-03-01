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
- `AE_AUTOPILOT_WAIT_STRATEGY`（既定 `fixed`。`fixed` / `exponential`）
- `AE_AUTOPILOT_ROUND_WAIT_MAX_SECONDS`（既定 `AE_AUTOPILOT_ROUND_WAIT_SECONDS` と同値）
- `AE_AUTOPILOT_DRY_RUN=1` で副作用なし検証
- `AE_AUTOPILOT_AUTO_LABEL=1` のとき、Risk Policy 由来の不足ラベルを自動付与（既定は `0`）
- `AE_AUTOPILOT_RISK_POLICY_PATH`（既定 `policy/risk-policy.yml`）

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
2. Risk Policy (`policy/risk-policy.yml`) から required label を算出
   - `AE_AUTOPILOT_AUTO_LABEL=1` のときは不足ラベルを自動付与
   - 既定 (`0`) は不足ラベルを reason にして停止
3. `mergeState=BEHIND` なら `PR Maintenance` の update-branch を dispatch
4. Copilot未解決スレッドまたは gate failure/missing の場合:
   - `copilot-auto-fix.mjs` を force mode で実行
   - `copilot-review-gate.yml` を dispatch
5. `auto-merge-enabler.mjs` で auto-merge 有効化を試行
6. 収束しない場合は `status:blocked` を付与して停止

PRコメント（upsert）:
- marker: `<!-- AE-CODEX-AUTOPILOT v1 -->`
- `status=blocked` の場合は先頭2行を deterministic 形式で出力
  - `Blocked: <reason>`
  - `To unblock: <single action>`
- 追加情報として `reason` / `actions` / `unblock` の詳細を続けて出力

## 4. 安全設計

- opt-in ラベル必須（`autopilot:on`）
- ラウンド上限あり（`AE_AUTOPILOT_MAX_ROUNDS`）
- dry-run あり（`AE_AUTOPILOT_DRY_RUN=1`）
- 競合状態（`CONFLICTING` / `DIRTY`）は自動停止して `status:blocked`

## 5. 運用メモ

- まず `AE_AUTOPILOT_DRY_RUN=1` で挙動確認してから本番有効化
- 自動復旧は `PR Self-Heal`（`pr-self-heal.yml`）と併用すると停止率を下げられます
- auto-merge が有効化されない場合は branch protection / required checks / label条件を確認してください
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE=1`（既定）の場合、PR summary に `Change Package Validation` が出力済みであることを確認してください

## 6. 停止理由と解除手順（運用定型）

| status/reason | 最小解除手順 |
| --- | --- |
| `skip` + `missing label autopilot:on` | PR に `autopilot:on` ラベルを付与して `/autopilot run` |
| `skip` + `draft PR` | Ready for review に変更して `/autopilot run` |
| `blocked` + `missing policy labels: ...` | 不足ラベルを付与して `/autopilot run`（`AE_AUTOPILOT_AUTO_LABEL=1` なら自動付与） |
| `blocked` + `merge conflict` | update-branch または手動 rebase で衝突を解消して push 後に `/autopilot run` |
| `done` + `checks healthy, waiting for required checks/merge queue` | required checks/merge queue の完了を待機（追加修正不要） |
| `done` + `auto-merge enabled` / `already merged` | 追加操作不要 |

補足:
- `done` で上表以外の reason の場合は、PR checks を監視して merge 完了まで待機します。
- レスポンス契約（継続/停止の定義）は `docs/integrations/CODEX-CONTINUATION-CONTRACT.md` を参照してください。
