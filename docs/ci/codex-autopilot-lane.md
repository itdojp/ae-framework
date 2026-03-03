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
- `AE_AUTOPILOT_ACTIONABLE_COMMAND`（任意）: actionable non-suggestion 指摘を処理する実行コマンド
- `AE_AUTOPILOT_ACTIONABLE_DRY_RUN`（任意）: actionable 実行のみ dry-run を個別制御（未設定時は `AE_AUTOPILOT_DRY_RUN` に追従）
- `AE_AUTOPILOT_AUTO_LABEL=1` のとき、Risk Policy 由来の不足ラベルを自動付与（既定は `0`）
- `AE_AUTOPILOT_RISK_POLICY_PATH`（既定 `policy/risk-policy.yml`）

補足:
- `workflow_dispatch` は `AE_CODEX_AUTOPILOT_ENABLED` 未設定でも実行可能（手動検証用）
- `autopilot:on` かつ `AE_CODEX_AUTOPILOT_ENABLED=1` のPRでは `copilot-auto-fix.yml` は重複実行抑止のため skip され、`pull_request_review` 起点の `Codex Autopilot Lane` が処理を継続

## 2. 起動条件

- `pull_request`（opened/synchronize/reopened/labeled/ready_for_review）
- `pull_request_review`（submitted）
- `issue_comment`（`/autopilot run`）
- `workflow_dispatch`（`pr_number` 必須）

対象PR条件:
- `autopilot:on` ラベルが付与されていること
- draft ではないこと
- fork PR ではないこと（権限の都合で運用非推奨）
- `pull_request_review` 起点は trusted reviewer のみ（`author_association` が MEMBER/OWNER/COLLABORATOR、または許可済みAI review actor）

## 3. 状態遷移（実装）

1. PR状態を取得（mergeability / labels / check rollup）
2. Risk Policy (`policy/risk-policy.yml`) から required label を算出
   - `AE_AUTOPILOT_AUTO_LABEL=1` のときは不足ラベルを自動付与
   - 既定 (`0`) は不足ラベルを reason にして停止
3. `mergeState=BEHIND` なら `PR Maintenance` の update-branch を dispatch
4. 未解決の AI review thread を走査し、`suggestion` ではない actionable 指摘を検出した場合:
   - `AE_AUTOPILOT_ACTIONABLE_COMMAND` が設定されていれば実行し、結果を集計
   - `AE_AUTOPILOT_ACTIONABLE_COMMAND` 未設定時は `actionable review tasks pending` で停止（従来どおり）
   - 人手コメントに `対応不要/対応済み/not applicable/fixed` 相当の disposition が含まれる指摘は actionable 対象から除外
   - 失敗（`failed > 0`）は fail-closed で `status:blocked`
   - active実行で `skipped > 0` は `actionable execution incomplete` として fail-closed
   - 成功時は再評価へ進行
5. Copilot未解決スレッドまたは gate failure/missing の場合:
   - `copilot-auto-fix.mjs` を force mode で実行
   - `copilot-review-gate.yml` を dispatch
6. `auto-merge-enabler.mjs` で auto-merge 有効化を試行
7. 収束しない場合は `status:blocked` を付与して停止

PRコメント（upsert）:
- marker: `<!-- AE-CODEX-AUTOPILOT v1 -->`
- `status=blocked` の場合は先頭2行を deterministic 形式で出力
  - `Blocked: <reason>`
  - `To unblock: <single action>`
- 追加情報として `reason` / `actions` / `unblock` の詳細を続けて出力
- actionable 実行結果は常に deterministic に出力
  - `- execution-result: success|failed|skipped`
  - `- actionable execution: <status> (attempted=..., succeeded=..., failed=..., skipped=...)`
  - `- actionable-execution-preview:`（最大3件）

### `AE_AUTOPILOT_ACTIONABLE_COMMAND` の入出力契約

- 入力（環境変数）:
  - `AE_ACTIONABLE_TASKS_JSON`（task配列を含むJSONファイル）
  - `AE_ACTIONABLE_PR_NUMBER`
  - `AE_ACTIONABLE_ROUND`
- 期待する標準出力:
  - JSON object: `{ "results": [{ "commentId": <number>, "status": "success|failed|skipped", "reason": "<optional>" }] }`
- 判定:
  - `failed > 0` は fail-closed
  - active 実行で `skipped > 0` は fail-closed
  - すべて `success` のときのみ次段へ進行

No Human Bottleneck（Issue #2333）整合ポイント:
- 停止時は必ず「理由」と「最小解除手順」を同時に出す（オープンエンド質問を禁止）
- `blocked` コメントは 1 行 1 アクションで再実行可能な文面に固定する
- `done`/`skip`/`blocked` の判定は `scripts/ci/codex-autopilot-lane.mjs` の reason ルールに一致させる

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
| `blocked` + `actionable review tasks pending: <n>` | actionable 指摘に対応（または非適用理由を返信）して `/autopilot run` |
| `blocked` + `actionable execution failed: <x>/<y> failed` | 実行結果を確認し、手動修正または `AE_AUTOPILOT_ACTIONABLE_COMMAND` を修正して `/autopilot run` |
| `blocked` + `actionable execution incomplete: <x>/<y> skipped` | skip 理由を解消して再実行（または手動対応）後に `/autopilot run` |
| `blocked` + `actionable review task scan truncated (pagination required)` | GitHub API/GraphQL 応答異常やページング失敗を解消して `/autopilot run` |
| `blocked` + `max rounds reached without convergence` | 進行中の checks/dispatch が収束するまで待機し、`/autopilot run` を再実行 |
| `blocked` + `merge conflict` | update-branch または手動 rebase で衝突を解消して push 後に `/autopilot run` |
| `done` + `checks healthy, waiting for required checks/merge queue` | required checks/merge queue の完了を待機（追加修正不要） |
| `done` + `auto-merge enabled` / `already merged` | 追加操作不要 |

補足:
- `done` で上表以外の reason の場合は、PR checks を監視して merge 完了まで待機します。
- レスポンス契約（継続/停止の定義）は `docs/integrations/CODEX-CONTINUATION-CONTRACT.md` を参照してください。

## 7. 回帰確認コマンド（最小）

```bash
pnpm vitest run tests/unit/ci/codex-autopilot-lane.test.ts
```

`blocked` 系ケースで以下を確認します。
- 1行目が `Blocked: ...`
- 2行目が `To unblock: ...`
- reason ごとに解除手順が deterministic に一致
