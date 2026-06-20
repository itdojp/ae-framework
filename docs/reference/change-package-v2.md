---
docRole: ssot
lastVerified: '2026-06-06'
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

Use the fixture for a complete schema-valid sample, including `validationLanes`, `policyDecision`, `releaseControls`, `residualRisks`, and optional `contractMigrationNotes`.

### 3. Differences from v1

| Field | v1 | v2 |
| --- | --- | --- |
| Primary purpose | aggregate PR risk, evidence, rollout | proof-carrying PR/release assurance package |
| Requirement refs | implicit in docs/diff | explicit `requirements` and `claims[].requirementRefs[]` |
| Touched files | `scope.changedFiles[]` | preserved in `scope.changedFiles[]` |
| Validation lanes | inferred from CI artifacts | explicit `validationLanes[]` with `pass` / `warn` / `fail` / `missing` |
| Evidence manifest link | evidence catalog only | explicit `claimEvidenceManifest` / `claimLevelSummary` evidence items |
| Achieved level | absent | package-level and per-claim `targetLevel` / `achievedLevel` |
| Claims | absent | `claims[]` with package/release outcome status |
| Policy decision | external artifact only | summarized as `policyDecision` |
| Residual risks | notes or exceptions | explicit `residualRisks[]` |
| Release controls | rollout / monitoring only | explicit `releaseControls` for pre-deploy, post-deploy, rollback |
| Contract migration notes | absent | optional `contractMigrationNotes[]` for compatibility-impacting assurance contract changes |
| Waivers | only `exceptions[]` | `waivers[]` linked to claims and evidence refs |

### 4. Claim states

`claims[].status` is a package / release-decision outcome field. It preserves review-relevant outcomes instead of collapsing a package into a generic pass/fail result:

- `satisfied`
- `tested`
- `model-checked`
- `proved`
- `runtime-mitigated`
- `waived`
- `unresolved`
- `failed`
- `not-applicable`

These values are `change-package/v2` package states, not `claim-evidence-manifest/v1` claim statuses or evidence kinds. `failed` means the package records a failed or insufficient claim outcome; it is not an evidence kind. `not-applicable` means the package explicitly records that a claim is out of scope or non-applicable for this package, with reviewable references or rationale. It must not be silently inferred from missing requirement references, empty per-claim `requirementRefs` arrays, or absent artifacts.

`tested` is behavior evidence, not proof. `model-checked` is model evidence, not proof. `runtime-mitigated` is runtime evidence, not proof. `waived` is not satisfied. `change-package/v2` status values must not expand `claim-evidence-manifest/v1` claim-status or evidence-kind vocabularies, or agent PR metric states, without an explicit schema and policy migration.

### 5. Core sections

- `requirements`: changed requirement references plus claim-to-requirement links. Empty requirement-reference arrays mean no requirement reference was found, not that the field was skipped or that claims are automatically non-applicable.
- `validationLanes`: validation lanes and their status with evidence refs.
- `policyDecision`: policy-gate result, mode, enforcement flag, reason, warnings, and errors.
- `claims`: claim statements, criticality, target/achieved levels, package/release outcome status, requirement refs, artifact refs, and optional per-claim decision.
- `assumptions`: assumptions on which assurance depends.
- `proofObligations`: claim-specific verification obligations and their discharge state.
- `counterexamples`: open, resolved, or accepted-risk counterexample artifacts.
- `runtimeControls`: runtime alerts and feature flags that mitigate but do not prove a claim.
- `releaseControls`: pre-deploy checks, post-deploy checks, and rollback signals.
- `residualRisks`: unresolved, failed, waived, runtime-mitigated, or assumption-driven risks requiring human review.
- `contractMigrationNotes`: optional PR/release summary notes for assurance-facing schema, canonical route, policy-gate, or change-package contract changes. Each note records the contract ID, compatibility state, dual-write / dual-validate status, affected producers/consumers, migration note refs, rollback refs, and a concise summary. Use it only when the PR has contract migration impact; ordinary PRs should omit the section.
- `waivers`: owner, expiry, reason, related claim IDs, and evidence refs.

### 6. Generation and validation

```bash
node scripts/change-package/generate.mjs \
  --schema-version v2 \
  --claim-evidence-manifest artifacts/assurance/claim-evidence-manifest.json \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --claim-level-summary artifacts/assurance/claim-level-summary.json \
  --contract-migration-notes artifacts/change-package/contract-migration-notes.json

node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package-v2.json \
  --schema schema/change-package-v2.schema.json \
  --artifact-root . \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --strict
```

Use `pnpm run change-package:generate:dual` and `pnpm run change-package:validate:dual` for v1/v2 compatibility checks. The v1 default is preserved; consumers should migrate by dual-write and dual-validate before relying on v2-only fields.

### 7. PR / release summary behavior

The generated Markdown points to the evidence package path, lists claim-state counts, and includes policy decision, validation lanes, release controls, residual risks, proof obligations, waivers, and contract migration notes when provided. `scripts/summary/render-pr-summary.mjs` also adds a digest line when `artifacts/change-package/change-package-v2.json` is present. If `contractMigrationNotes[]` is absent or empty, both change-package Markdown and PR summaries omit the contract migration section.

---

## 日本語

## 1. 目的

`change-package/v2` は、PR または release の受入判断に使う proof-carrying assurance package です。requirement reference、変更ファイル、validation lane、evidence link、claim 単位の achieved level、assumption、waiver、runtime control、residual risk、policy decision、release/post-deploy control を記録します。

互換性のため、既定 contract は引き続き `change-package/v1` です。v2 は opt-in 生成、dual-write、strict validation、v2 artifact が存在する場合の PR summary rendering に接続された安定化済み拡張 contract として扱います。

## 2. スキーマと fixture

- スキーマ: `schema/change-package-v2.schema.json`
- sample fixture: `fixtures/change-package/sample.change-package-v2.json`
- 既定 contract: `schema/change-package.schema.json`（`change-package/v1`）

完全な schema-valid sample は fixture を参照してください。fixture には `validationLanes`、`policyDecision`、`releaseControls`、`residualRisks`、任意の `contractMigrationNotes` も含まれます。

## 3. v1 との差分

| 項目 | v1 | v2 |
| --- | --- | --- |
| 主要目的 | PR リスク・evidence・rollout の集約 | PR/release 向け proof-carrying assurance package |
| requirement refs | docs/diff に暗黙 | `requirements` と `claims[].requirementRefs[]` に明示 |
| touched files | `scope.changedFiles[]` | `scope.changedFiles[]` として維持 |
| validation lanes | CI artifact から推測 | `validationLanes[]` に `pass` / `warn` / `fail` / `missing` として明示 |
| evidence manifest link | evidence catalog のみ | `claimEvidenceManifest` / `claimLevelSummary` evidence item として明示 |
| achieved level | なし | package-level と claim-level の `targetLevel` / `achievedLevel` |
| claims | なし | package / release outcome status 付きの `claims[]` |
| policy decision | 外部 artifact のみ | `policyDecision` として要約 |
| residual risks | notes / exceptions に分散 | `residualRisks[]` に明示 |
| release controls | rollout / monitoring のみ | pre-deploy / post-deploy / rollback を `releaseControls` に明示 |
| contract migration notes | なし | 互換性影響のある assurance contract 変更向けの任意 `contractMigrationNotes[]` |
| waivers | `exceptions[]` のみ | claim と evidence refs に紐づく `waivers[]` |

## 4. claim state

`claims[].status` は package / release-decision outcome field です。package 全体を generic pass/fail に潰さず、review に必要な outcome を保持します。

- `satisfied`
- `tested`
- `model-checked`
- `proved`
- `runtime-mitigated`
- `waived`
- `unresolved`
- `failed`
- `not-applicable`

これらは `change-package/v2` の package state であり、`claim-evidence-manifest/v1` の claim status や evidence kind ではありません。`failed` は package が failed / insufficient な claim outcome を記録したことを表し、evidence kind ではありません。`not-applicable` は、その package において claim が明示的に scope 外 / 非対象であることを、review 可能な reference または rationale とともに記録する state です。missing requirement references、空の per-claim `requirementRefs` 配列、artifact 欠落から暗黙推論してはいけません。

`tested` は behavior evidence であり proof ではありません。`model-checked` は model evidence であり proof ではありません。`runtime-mitigated` は runtime evidence であり proof ではありません。`waived` は satisfied ではありません。`change-package/v2` の status value は、明示的な schema / policy migration なしに `claim-evidence-manifest/v1` の claim-status / evidence-kind vocabulary や agent PR metric state を拡張しません。

## 5. 主要セクション

- `requirements`: 変更された requirement reference と claim-to-requirement link。空の requirement-reference 配列は requirement reference が見つからなかったことを表し、field skipped や claim の自動的な non-applicable を意味しません。
- `validationLanes`: 検証レーン、状態、evidence refs。
- `policyDecision`: policy-gate の result / mode / enforcement / reason / warnings / errors。
- `claims`: claim statement、criticality、target/achieved level、package / release outcome status、requirement refs、artifact refs、任意の per-claim decision。
- `assumptions`: assurance の前提。
- `proofObligations`: claim 単位の検証 obligation と discharge 状態。
- `counterexamples`: open / resolved / accepted-risk の counterexample artifact。
- `runtimeControls`: claim を緩和する runtime alert / feature flag。proof には昇格しません。
- `releaseControls`: pre-deploy check、post-deploy check、rollback signal。
- `residualRisks`: human review が必要な unresolved / failed / waived / runtime-mitigated / assumption 起因のリスク。
- `contractMigrationNotes`: assurance-facing schema、canonical route、policy-gate、change-package contract の変更に対する任意の PR/release summary 注記です。contract ID、compatibility state、dual-write / dual-validate status、affected producers/consumers、migration note refs、rollback refs、短い summary を記録します。contract migration impact がある PR のみで使い、通常 PR では省略します。
- `waivers`: owner、expiry、reason、related claim IDs、evidence refs。

## 6. 生成・検証

```bash
node scripts/change-package/generate.mjs \
  --schema-version v2 \
  --claim-evidence-manifest artifacts/assurance/claim-evidence-manifest.json \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --claim-level-summary artifacts/assurance/claim-level-summary.json \
  --contract-migration-notes artifacts/change-package/contract-migration-notes.json

node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package-v2.json \
  --schema schema/change-package-v2.schema.json \
  --artifact-root . \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --strict
```

v1/v2 互換性確認には `pnpm run change-package:generate:dual` と `pnpm run change-package:validate:dual` を使います。v1 default は維持し、v2-only field に依存する consumer は dual-write / dual-validate 期間を置いて移行します。

## 7. PR / release summary

生成 Markdown は evidence package path を示し、claim-state counts、policy decision、validation lanes、release controls、residual risks、proof obligations、waivers、および提供された場合の contract migration notes を表示します。`artifacts/change-package/change-package-v2.json` が存在する場合、`scripts/summary/render-pr-summary.mjs` も PR summary digest に v2 情報を追加します。`contractMigrationNotes[]` が無い、または空の場合、change-package Markdown と PR summary は contract migration section を省略します。
