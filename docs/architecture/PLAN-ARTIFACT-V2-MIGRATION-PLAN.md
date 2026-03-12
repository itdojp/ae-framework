---
docRole: ssot
lastVerified: '2026-03-12'
owner: architecture-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Plan Artifact v2 Migration Plan

対象 Issue: `#2650`, `#2579`, `#2581`

## 1. 結論

- 現時点では `plan-artifact/v2` を導入しない。
- 当面の canonical contract は `plan-artifact/v1` を維持する。
- 非 PR 向け delivery execution が必要になった場合も、先に consumer を定義し、必要なら adapter か sidecar で対応する。

## 2. 現行 `plan-artifact/v1` の producer / consumer

| 区分 | 実体 | 役割 |
| --- | --- | --- |
| Producer | `scripts/plan-artifact/generate.mjs` | high-risk PR 向け事前レビュー契約を生成 |
| Validator | `scripts/plan-artifact/validate.mjs` | schema / risk policy 整合を検証 |
| Gate consumer | `scripts/ci/policy-gate.mjs` | high-risk PR の必須契約として block 判定 |
| Report consumer | `.github/workflows/pr-ci-status-comment.yml` | commit 済み artifact がある場合に PR summary へ反映 |
| Human consumer | `docs/ci/plan-artifact.md` | 運用 runbook / reviewer 手順 |

根拠:
- `schema/plan-artifact.schema.json`
- `docs/reference/CONTRACT-CATALOG.md`
- `docs/architecture/DELIVERY-CONTRACT-CONSUMER-INVENTORY.md`

## 3. フィールド分類

### 3.1 PR 固有であるため、そのまま再利用しない項目

| Field | 理由 |
| --- | --- |
| `source.prNumber` | PR lifecycle に依存する |
| `source.baseRef` / `source.headRef` | Git branch topology に依存する |
| `risk.selected` | 現行は PR label / review topology と連動している |
| `risk.requiresHumanApproval` / `risk.minHumanApprovals` | policy-gate の PR review 要件に結び付く |
| `filesExpectedToChange` | PR diff の予告という意味が強い |
| `rollbackPlan` | PR / branch rollback を前提に記述されている |
| `requiredHumanInput` | 現行運用では PR review / approval を表す |

### 3.2 将来的に再利用し得る項目

| Field | 再利用条件 |
| --- | --- |
| `goal` | delivery slice 単位の目的として再利用可能 |
| `scope` | execution scope の要約として再利用可能 |
| `assumptions` | 環境前提・依存条件として再利用可能 |
| `verificationPlan` | generic verification step と evidence へ分解可能 |
| `notes` | narrative 補足として再利用可能 |

## 4. 判断

### 4.1 `v2` を直ちに作らない理由

1. 現行 consumer はすべて PR 文脈で成立している
2. `v2` を追加しても、現時点で移行先 consumer が存在しない
3. `#2649` で検討中の `delivery-plan/v1` / `goal-verification/v1` / `delivery-summary/v1` と責務が重なる
4. schema を増やすと SSOT が分散し、`policy-gate` と report chain の整合維持コストが上がる

### 4.2 当面の方針

- `plan-artifact/v1` は high-risk PR review 契約として固定する
- 非 PR consumer が必要になった場合は、まず consumer-first で別契約を定義する
- `v1` をそのまま汎化するのではなく、必要なら adapter 層で generic plan へ写像する

## 5. `v2` を許可する条件

`plan-artifact/v2` は、次の条件をすべて満たす場合にのみ導入する。

1. PR 以外の concrete consumer が存在する
2. その consumer が `v1` では表現できない追加フィールドを必要とする
3. producer / validator / consumer の最低 1 本ずつが同一 PR で接続される
4. dual-write または adapter migration が文書化される
5. `validate-json` または `validate-artifacts-ajv` に追加される
6. `CONTRACT-CATALOG` と一次文書が同時更新される

## 6. migration 方針

### 6.1 許可される移行パターン

- adapter-first
  - `plan-artifact/v1` を入力にし、consumer 側で必要な generic plan へ変換する
- dual-write
  - `v1` と `v2` を同一 producer から同時出力し、validator を両方通す
- consumer cutover
  - すべての主要 consumer が `v2` に移ったことを確認してから `v1` 廃止を計画する

### 6.2 現時点で不許可のパターン

- schema だけ先に追加する
- `v1` validator / policy-gate / PR summary を更新せずに `v2` を導入する
- consumer を未定義のまま `v2` を future contract として catalog に載せる

## 7. 現時点の決定

- keep: `plan-artifact/v1`
- adapter candidate: future non-PR delivery consumer
- replace: 未決定
- `plan-artifact/v2`: deferred

## 8. 次アクション

1. `#2649` で non-PR consumer inventory を先に確定する
2. その consumer が `plan-artifact/v1` を直接使えるかを判定する
3. 直接使えない場合だけ adapter / sidecar / `v2` の比較を行う
