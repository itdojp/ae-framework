# PR State / Execution Plan v1 Draft

対象Issue: `#2405`  
目的: `pr-state.v1` と `execution-plan.v1` の契約を先に固定し、workflow分散実装から段階移行できる基準を作る。

## 1. 背景

現行の PR 自動化は、`policy-gate` / `copilot-review-gate` / `codex-autopilot-lane` / `pr-ci-status-comment` へ責務が分散している。  
本ドラフトは、以下の2契約を導入して状態遷移と実行計画を統一する。

- `schema/pr-state-v1.schema.json`
- `schema/execution-plan-v1.schema.json`

## 2. `pr-state.v1` の設計意図

- PR単位の「現在状態」と「遷移理由」を機械可読で保持する
- `blocked` 状態では `reasonCode` / `unblockActions[]` / `ownerHint` を必須化する
- required checks や evidence 参照を契約化し、ゲート実装差分を減らす

### 状態列挙（理想設計との対応）

- `draft`
- `ready_for_review`
- `review_feedback_pending`
- `action_execution`
- `gate_recheck`
- `merge_eligible`
- `blocked`
- `merged`

## 3. `execution-plan.v1` の設計意図

- 1回の収束ループ（例: autopilot）で行う処理をタスク列として固定する
- 各タスクに `owner`（`ai`/`human`/`either`）と依存関係 `dependsOn[]` を持たせる
- `stopOnFailure` / `maxAttempts` で再試行挙動を規定する

### 主要タスク種別

- `review_fetch`
- `suggestion_apply`
- `workflow_dispatch`
- `gate_recheck`
- `label_sync`
- `artifact_collect`
- `comment_emit`
- `block_emit`

## 4. 既存契約との関係

- 既存:
  - `schema/state-machine.schema.json`
  - `schema/execplan.schema.json`
- 追加:
  - `schema/pr-state-v1.schema.json`
  - `schema/execution-plan-v1.schema.json`

使い分け:
- 既存 schema は汎用契約として維持
- 新規 schema は PR 自動化専用契約として導入
- 移行期間は dual-write / dual-validate を前提とする

## 5. サンプル

- `fixtures/pr-state/sample.pr-state.blocked.json`
- `fixtures/pr-state/sample.pr-state.merge-eligible.json`
- `fixtures/execution-plan/sample.execution-plan.autopilot.json`

## 6. 次アクション

1. `scripts/ci/codex-autopilot-lane.mjs` から `execution-plan.v1` を出力
2. `policy-gate` と `copilot-review-gate` の判定結果を `pr-state.v1` に集約
3. `pr-ci-status-comment` で `blocked_reason` と `unblock_actions` を表示
