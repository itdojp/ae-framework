---
docRole: ssot
lastVerified: '2026-05-08'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Change Package v2

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

`change-package/v2` extends `change-package/v1` so that a PR or release can carry a reviewable assurance package. It records requirement references, touched files, validation lanes, evidence links, per-claim achieved levels, assumptions, waivers, runtime controls, residual risks, policy decisions, and release/post-deploy controls.

The default compatibility contract remains `change-package/v1`. v2 is the stabilized proof-carrying extension used through opt-in generation, dual-write, strict validation, and PR summary rendering when the v2 artifact is present.

### 2. Schema and Fixture

- Schema: `schema/change-package-v2.schema.json`
- Sample fixture: `fixtures/change-package/sample.change-package-v2.json`
- Current default contract: `schema/change-package.schema.json` (`change-package/v1`)

Minimal excerpt:

```json
{
  "schemaVersion": "change-package/v2",
  "requirements": {
    "changedRefs": ["docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md"],
    "claimRefs": [
      {
        "claimId": "no-negative-balance",
        "refs": ["docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md"]
      }
    ]
  },
  "assurance": {
    "targetLevel": "A3",
    "achievedLevel": "A2",
    "status": "partial"
  },
  "claims": [
    {
      "id": "no-negative-balance",
      "statement": "The change must not allow a negative balance.",
      "criticality": "high",
      "targetLevel": "A3",
      "achievedLevel": "A3",
      "status": "model-checked",
      "requirementRefs": ["docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md"],
      "artifactRefs": ["artifacts/assurance/claim-level-summary.json"]
    }
  ]
}
```

Use the fixture for a complete schema-valid sample, including `validationLanes`, `policyDecision`, `releaseControls`, and `residualRisks`.

### 3. Differences from v1

| Field | v1 | v2 |
| --- | --- | --- |
| Primary purpose | aggregate PR risk, evidence, rollout | proof-carrying PR/release assurance package |
| Requirement refs | implicit in docs/diff | explicit `requirements` and `claims[].requirementRefs[]` |
| Touched files | `scope.changedFiles[]` | preserved in `scope.changedFiles[]` |
| Validation lanes | inferred from CI artifacts | explicit `validationLanes[]` with `pass` / `warn` / `fail` / `missing` |
| Evidence manifest link | evidence catalog only | explicit `claimEvidenceManifest` / `claimLevelSummary` evidence items |
| Achieved level | absent | package-level and per-claim `targetLevel` / `achievedLevel` |
| Claims | absent | `claims[]` with first-class status |
| Policy decision | external artifact only | summarized as `policyDecision` |
| Residual risks | notes or exceptions | explicit `residualRisks[]` |
| Release controls | rollout / monitoring only | explicit `releaseControls` for pre-deploy, post-deploy, rollback |
| Waivers | only `exceptions[]` | `waivers[]` linked to claims and evidence refs |

### 4. Claim states

`claims[].status` distinguishes review-relevant outcomes instead of collapsing them into a generic pass/fail result:

- `satisfied`
- `tested`
- `model-checked`
- `proved`
- `runtime-mitigated`
- `waived`
- `unresolved`
- `failed`
- `not-applicable`

`runtime-mitigated` is not proof. `waived` is not satisfied. `failed` and `not-applicable` are first-class states, not comments.

### 5. Core sections

- `requirements`: changed requirement references plus claim-to-requirement links. Empty arrays mean no requirement reference was found, not that the field was skipped.
- `validationLanes`: validation lanes and their status with evidence refs.
- `policyDecision`: policy-gate result, mode, enforcement flag, reason, warnings, and errors.
- `claims`: claim statements, criticality, target/achieved levels, status, requirement refs, artifact refs, and optional per-claim decision.
- `assumptions`: assumptions on which assurance depends.
- `proofObligations`: claim-specific verification obligations and their discharge state.
- `counterexamples`: open, resolved, or accepted-risk counterexample artifacts.
- `runtimeControls`: runtime alerts and feature flags that mitigate but do not prove a claim.
- `releaseControls`: pre-deploy checks, post-deploy checks, and rollback signals.
- `residualRisks`: unresolved, failed, waived, runtime-mitigated, or assumption-driven risks requiring human review.
- `waivers`: owner, expiry, reason, related claim IDs, and evidence refs.

### 6. Generation and validation

```bash
node scripts/change-package/generate.mjs \
  --schema-version v2 \
  --claim-evidence-manifest artifacts/assurance/claim-evidence-manifest.json \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --claim-level-summary artifacts/assurance/claim-level-summary.json

node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package-v2.json \
  --schema schema/change-package-v2.schema.json \
  --artifact-root . \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --strict
```

Use `pnpm run change-package:generate:dual` and `pnpm run change-package:validate:dual` for v1/v2 compatibility checks. The v1 default is preserved; consumers should migrate by dual-write and dual-validate before relying on v2-only fields.

### 7. PR / release summary behavior

The generated Markdown points to the evidence package path, lists claim-state counts, and includes policy decision, validation lanes, release controls, residual risks, proof obligations, and waivers. `scripts/summary/render-pr-summary.mjs` also adds a digest line when `artifacts/change-package/change-package-v2.json` is present.

---

## 日本語

## 1. 目的

`change-package/v2` は、PR または release の受入判断に使う proof-carrying assurance package です。requirement reference、変更ファイル、validation lane、evidence link、claim 単位の achieved level、assumption、waiver、runtime control、residual risk、policy decision、release/post-deploy control を記録します。

互換性のため、既定 contract は引き続き `change-package/v1` です。v2 は opt-in 生成、dual-write、strict validation、v2 artifact が存在する場合の PR summary rendering に接続された安定化済み拡張 contract として扱います。

## 2. スキーマと fixture

- スキーマ: `schema/change-package-v2.schema.json`
- sample fixture: `fixtures/change-package/sample.change-package-v2.json`
- 既定 contract: `schema/change-package.schema.json`（`change-package/v1`）

完全な schema-valid sample は fixture を参照してください。fixture には `validationLanes`、`policyDecision`、`releaseControls`、`residualRisks` も含まれます。

## 3. v1 との差分

| 項目 | v1 | v2 |
| --- | --- | --- |
| 主要目的 | PR リスク・evidence・rollout の集約 | PR/release 向け proof-carrying assurance package |
| requirement refs | docs/diff に暗黙 | `requirements` と `claims[].requirementRefs[]` に明示 |
| touched files | `scope.changedFiles[]` | `scope.changedFiles[]` として維持 |
| validation lanes | CI artifact から推測 | `validationLanes[]` に `pass` / `warn` / `fail` / `missing` として明示 |
| evidence manifest link | evidence catalog のみ | `claimEvidenceManifest` / `claimLevelSummary` evidence item として明示 |
| achieved level | なし | package-level と claim-level の `targetLevel` / `achievedLevel` |
| claims | なし | first-class status 付きの `claims[]` |
| policy decision | 外部 artifact のみ | `policyDecision` として要約 |
| residual risks | notes / exceptions に分散 | `residualRisks[]` に明示 |
| release controls | rollout / monitoring のみ | pre-deploy / post-deploy / rollback を `releaseControls` に明示 |
| waivers | `exceptions[]` のみ | claim と evidence refs に紐づく `waivers[]` |

## 4. claim state

`claims[].status` は次を区別します。

- `satisfied`
- `tested`
- `model-checked`
- `proved`
- `runtime-mitigated`
- `waived`
- `unresolved`
- `failed`
- `not-applicable`

`runtime-mitigated` は proof ではありません。`waived` は satisfied ではありません。`failed` と `not-applicable` はコメントではなく first-class state です。

## 5. 主要セクション

- `requirements`: 変更された requirement reference と claim-to-requirement link。空配列は「対象なし」を意味し、「未評価」と区別します。
- `validationLanes`: 検証レーン、状態、evidence refs。
- `policyDecision`: policy-gate の result / mode / enforcement / reason / warnings / errors。
- `claims`: claim statement、criticality、target/achieved level、status、requirement refs、artifact refs、任意の per-claim decision。
- `assumptions`: assurance の前提。
- `proofObligations`: claim 単位の検証 obligation と discharge 状態。
- `counterexamples`: open / resolved / accepted-risk の counterexample artifact。
- `runtimeControls`: claim を緩和する runtime alert / feature flag。proof には昇格しません。
- `releaseControls`: pre-deploy check、post-deploy check、rollback signal。
- `residualRisks`: human review が必要な unresolved / failed / waived / runtime-mitigated / assumption 起因のリスク。
- `waivers`: owner、expiry、reason、related claim IDs、evidence refs。

## 6. 生成・検証

```bash
node scripts/change-package/generate.mjs \
  --schema-version v2 \
  --claim-evidence-manifest artifacts/assurance/claim-evidence-manifest.json \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --claim-level-summary artifacts/assurance/claim-level-summary.json

node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package-v2.json \
  --schema schema/change-package-v2.schema.json \
  --artifact-root . \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --strict
```

v1/v2 互換性確認には `pnpm run change-package:generate:dual` と `pnpm run change-package:validate:dual` を使います。v1 default は維持し、v2-only field に依存する consumer は dual-write / dual-validate 期間を置いて移行します。

## 7. PR / release summary

生成 Markdown は evidence package path を示し、claim-state counts、policy decision、validation lanes、release controls、residual risks、proof obligations、waivers を表示します。`artifacts/change-package/change-package-v2.json` が存在する場合、`scripts/summary/render-pr-summary.mjs` も PR summary digest に v2 情報を追加します。
