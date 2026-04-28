---
docRole: ssot
lastVerified: '2026-03-12'
owner: architecture-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Delivery Contract Consumer Inventory

対象 Issue: `#2649`, `#2579`, `#2581`

## 1. 目的

`delivery-plan/v1`、`goal-verification/v1`、`delivery-summary/v1` を導入する前に、現行実装で既に存在する consumer を固定する。  
新契約は consumer-first で追加し、既存 evidence / operation 契約の SSOT を分散させない。

## 2. 現行 consumer の所在

### 2.1 planning / operation

| Contract | Primary producer | Primary consumer | 用途 |
| --- | --- | --- | --- |
| `execplan` | fixture / future generic producers | `scripts/ci/validate-json.mjs`, `docs/guides/EXECPLAN-SCHEMA.md` | 汎用 execution DAG |
| `execution-plan-v1` | `scripts/ci/codex-autopilot-lane.mjs` | `docs/ci/codex-autopilot-lane.md`, `scripts/ci/validate-json.mjs` | PR 自動化専用 plan |
| `plan-artifact/v1` | `scripts/plan-artifact/generate.mjs` | `scripts/plan-artifact/validate.mjs`, `scripts/ci/policy-gate.mjs`, `.github/workflows/pr-ci-status-comment.yml` | high-risk PR review / rollback / verification 要件 |
| `ae-handoff/v1` | `scripts/agents/create-handoff.mjs`, `templates/comments/AE-HANDOFF.md`（manual/export）, `docs/agents/handoff.md` | `scripts/agents/validate-handoff.mjs`, future PR/Issue handoff consumer | resumable handoff |

### 2.2 evidence / verification

| Contract | Primary producer | Primary consumer | 用途 |
| --- | --- | --- | --- |
| `verify-lite-run-summary` | `verify-lite.yml`, `scripts/ci/write-verify-lite-summary.mjs` | `assurance`, `quality-scorecard`, `report-envelope`, `hook-feedback`, onboarding docs | baseline verification summary |
| `assurance-summary` | `scripts/assurance/aggregate-lanes.mjs`, `verify-lite.yml` | `enforce-assurance`, `quality-scorecard`, `claim-evidence-manifest`, `render-pr-summary`, `hook-feedback`, `scripts/agents/create-handoff.mjs` | structured assurance evidence |
| `claim-evidence-manifest/v1` | `scripts/assurance/build-claim-evidence-manifest.mjs`, `verify-lite.yml` | `validate-artifacts-ajv`, `render-pr-summary`, `pr-ci-status-comment`, future policy-gate consumers | per-claim evidence / achieved-level sidecar |
| `formal-summary-v1/v2` | `scripts/formal/generate-formal-summary-v1.mjs` | `validate-formal-summary-*`, `quality-scorecard`, run-manifest generation | formal evidence aggregation |
| `trace-validation` | `scripts/trace/run-kvonce-conformance.sh` ほか | `validate-artifacts-ajv`, `render-trace-summary` | trace-based conformance evidence |
| `quality-scorecard/v1` | `scripts/quality/build-quality-scorecard.mjs`, `.github/workflows/verify-lite.yml` | `scripts/ci/validate-quality-scorecard.mjs`, `scripts/summary/render-pr-summary.mjs`, `.github/workflows/pr-ci-status-comment.yml` | 横断 quality 集約 |

## 3. `#2579` 提案との重複点

### 3.1 `delivery-plan/v1`

- `execplan` と責務が近い。
- `execution-plan-v1` と task ordering / dependency / retry semantics が重なる。
- 現時点で非 PR の concrete consumer が存在しない。

判定:
- consumer を先に持たない `delivery-plan/v1` は deferred。
- 追加するなら `#2649` 内で非 PR consumer を定義してから。

### 3.2 `goal-verification/v1`

- `verify-lite-run-summary`
- `assurance-summary`
- `formal-summary-v1/v2`
- `trace-validation`
- `quality-scorecard/v1`
  と verification evidence の責務が重なる。

判定:
- 新契約を追加する前に、どの consumer が「単一の goal-level verdict」を必要とするかを定義する。
- その consumer が存在しない限り、現行 evidence を fold するだけで足りる可能性が高い。

### 3.3 `delivery-summary/v1`

- `quality-scorecard/v1`
- `render-pr-summary`
- `assurance-summary`
  と summary layering が重なる。

判定:
- task / slice / milestone summary を fold する consumer が未定義のため deferred。
- summary contract を追加するなら、PR summary / closeout / handoff のどれを置換するかを先に定義する。

## 4. consumer-first 導入条件

新契約は、少なくとも以下を満たす場合のみ追加する。

1. 現行契約で代替できない consumer が存在する
2. producer と consumer の双方が同一 PR で最低限接続される
3. `validate-json` または `validate-artifacts-ajv` に載る
4. `CONTRACT-CATALOG` と一次文書に SSOT 境界が追記される

## 5. split 方針

### 5.1 先に進めるもの

- `#2648` `context-pack-boundary-map/v1`
  - 既存 `context-bundle` / `context-pack-v1` を置換しない sidecar

### 5.2 consumer を先に定義すべきもの

- `#2649` `delivery-plan/v1`
- `#2649` `goal-verification/v1`
- `#2649` `delivery-summary/v1`

### 5.3 migration plan が先のもの

- `#2650` `plan-artifact/v2`
- `#2651` `ae-handoff/v2`

## 6. 実装判断

- `#2579` は umbrella として維持する
- 実装は split Issue 単位で進める
- `delivery-plan/v1` / `goal-verification/v1` / `delivery-summary/v1` は、この inventory に concrete consumer を追記できた時点で個別に起票する
