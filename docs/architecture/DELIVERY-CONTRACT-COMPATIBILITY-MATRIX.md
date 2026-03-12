---
docRole: ssot
lastVerified: '2026-03-12'
owner: architecture-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Delivery Contract Compatibility Matrix

対象 Issue: `#2579`, `#2581`

## 1. 目的

`#2579` で提案されている delivery-layer 契約を、そのまま一括追加すると既存契約との責務重複が発生する。  
本ドキュメントは、現行契約の SSOT を固定し、新規契約を追加する場合の分割順序を定義する。

## 2. 決定事項

- `context-bundle` は task-scoped context input の正本として維持する。
- `execplan` は汎用 execution DAG 契約として維持する。
- `execution-plan-v1` は PR 自動化専用契約として維持する。
- `state-machine` は runtime/state modeling 契約であり、delivery plan の代替にはしない。
- `plan-artifact/v1` は high-risk PR review / policy-gate 用の operation 契約として維持する。
- `ae-handoff/v1` は現行 handoff 契約の正本として維持し、v2 は baseline builder の運用結果を踏まえて判断する。

## 3. 現行契約の役割

| Contract | Primary role | 現行の用途 | SSOT 判定 |
| --- | --- | --- | --- |
| `schema/context-bundle.schema.json` | `input` | task/scenario ごとの context 入力束 | 維持 |
| `schema/execplan.schema.json` | `operation` | 汎用 execution DAG | 維持 |
| `schema/execution-plan-v1.schema.json` | `operation` | PR 自動化用の専用 execution plan | 維持 |
| `schema/state-machine.schema.json` | `input` | runtime / formal state-machine 定義 | 維持 |
| `schema/plan-artifact.schema.json` | `operation` | high-risk PR の plan artifact | 維持 |
| `schema/ae-handoff.schema.json` | `input` | agent handoff / resume artifact | 維持 |

## 4. 重複しない境界

### 4.1 `context-bundle`

- 目的は「task 実行時に読み込む context の deterministic な入力束」。
- `boundary-map` のような slice 間 produce/consume 契約とは役割が異なる。
- したがって、将来 `context-pack-boundary-map/v1` を導入しても、`context-bundle` は置換しない。

### 4.2 `execplan` と `execution-plan-v1`

- `execplan` は汎用 contract。
- `execution-plan-v1` は `codex-autopilot-lane` で使う PR 自動化専用 contract。
- 将来の `delivery-plan/v1` は、この 2 つを上書き置換せず、非 PR の delivery consumer が必要になった時点で新規契約として導入する。

### 4.3 `state-machine`

- `state-machine` は runtime / formal spec 用の状態遷移定義。
- delivery task lifecycle の canonical contract にはしない。
- delivery state を導入する場合も、`state-machine` そのものを PR/task orchestration の SSOT に転用しない。

### 4.4 `plan-artifact/v1`

- 現行 consumer は `policy-gate`、`pr-ci-status-comment`、validation scripts。
- 高リスク PR の review / rollback / verification 要件を束ねる contract であり、汎用 delivery task contract ではない。
- `v2` を追加する場合は consumer migration を先に定義する。

### 4.5 `ae-handoff/v1`

- 現行運用の resume cursor は `ae-handoff/v1`。
- baseline builder (`#2578`) の実運用で不足が確定するまでは `v2` を作らない。

## 5. `#2579` 提案項目の扱い

| Proposed contract / surface | 判定 | 理由 | 次アクション |
| --- | --- | --- | --- |
| `context-pack-boundary-map/v1` | split | 既存 Context Pack / context-bundle とは非重複だが、新規 sidecar として切り出す方が安全 | `#2648` |
| `delivery-plan/v1` | defer | `execplan` / `execution-plan-v1` と重なる。非 PR consumer を先に固定すべき | `#2649` |
| `plan-artifact/v2` | split | `v1` consumer が既にあるため、schema 追加より migration plan が先 | `#2650` |
| `goal-verification/v1` | defer | `verify-lite`, `assurance-summary`, `formal-summary`, `trace-validation` と証跡責務が重なる | consumer を先に定義 |
| `delivery-summary/v1` | defer | `quality-scorecard`, PR summary, assurance summary との summary layering を整理してから | consumer を先に定義 |
| `ae-handoff/v2` | defer | `ae-handoff/v1` と baseline builder (`#2578`) が先 | `#2651` (`#2578` 完了後) |
| `ae boundary|delivery|context|verify|summary|handoff` 一括 CLI | reject | 一括追加は境界が粗く、既存 CLI と重複する | 小粒 Issue に分割 |

## 6. 将来導入時の SSOT ルール

### 6.1 sidecar は既存正本を置換しない

- `boundary-map` は Context Pack sidecar。
- delivery-level summary は既存 evidence の fold であり、既存 summary を置換しない。

### 6.2 generic と domain-specific を混在させない

- generic execution contract は `execplan`。
- PR automation 専用 contract は `execution-plan-v1`。
- high-risk review contract は `plan-artifact/v1`。
- 新しい contract は、この 3 つのどれを拡張するのかを明示しない限り追加しない。

### 6.3 v2 は consumer migration を条件にする

- `plan-artifact/v2`
- `ae-handoff/v2`
- 将来の `delivery-summary/v1`

これらは schema 追加だけでは完了としない。`validate-json`, `validate-artifacts-ajv`, workflow, summary renderer, doc consumer の移行計画を同時に定義する。

## 7. 実装順序

1. `#2578` baseline builder を mainline 運用に載せる
2. `#2648` で `context-pack-boundary-map/v1` の sidecar 導入可否を判断する
3. `#2650` で `plan-artifact/v2` の consumer migration plan を定義する
4. `#2649` で `delivery-plan/v1` / `goal-verification/v1` / `delivery-summary/v1` の consumer を固定する
5. `#2651` で `ae-handoff/v2` を `#2578` の運用実績ベースで再評価する

## 8. 完了条件

- `#2579` を一括実装しない理由が明文化されている
- 既存契約の SSOT が固定されている
- follow-up Issue 単位で着手順が定義されている
