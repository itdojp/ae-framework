---
docRole: ssot
lastVerified: '2026-03-21'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Change Package v2

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

`change-package/v2` extends `change-package/v1` so that safety reasoning can be recorded in terms of claims, assumptions, proof obligations, counterexamples, trust boundaries, and runtime controls.

The default production contract remains `change-package/v1`, but v2 is now connected through opt-in generation, dual-write, strict validation, and PR summary rendering when the v2 artifact is present.

### 2. Schema and Fixture

- Schema: `schema/change-package-v2.schema.json`
- Sample fixture: `fixtures/change-package/sample.change-package-v2.json`
- Current production contract: `schema/change-package.schema.json` (`change-package/v1`)

Minimal excerpt:

```json
{
  "schemaVersion": "change-package/v2",
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
      "status": "model-checked",
      "artifactRefs": [
        "artifacts/assurance/assurance-summary.json"
      ]
    }
  ],
  "proofObligations": [
    {
      "id": "obl-1",
      "claimId": "no-negative-balance",
      "method": "tla",
      "status": "discharged",
      "artifactRefs": [
        "artifacts/hermetic-reports/formal/tla-summary.json"
      ]
    }
  ]
}
```

This excerpt focuses on the `assurance`, `claims`, and `proofObligations` structure while keeping the shown entries schema-valid. Use `fixtures/change-package/sample.change-package-v2.json` for the complete sample.

### 3. Differences from v1

| Field | v1 | v2 |
| --- | --- | --- |
| Primary purpose | aggregate PR risk, evidence, rollout | record assurance package claim by claim |
| assurance level | absent | `assurance.targetLevel` / `achievedLevel` / `status` |
| claim | absent | `claims[]` |
| assumption | absent | `assumptions[]` |
| proof obligation | absent | `proofObligations[]` |
| counterexample | absent | `counterexamples[]` |
| trust boundary | implicit | `trustBoundary.outsideModel` |
| runtime control | spread across rollout / monitoring | explicit `runtimeControls.alerts[]` / `runtimeControls.featureFlags[]` |
| waiver | only `exceptions[]` | adds `waivers[]` linked to claims |

### 4. Meaning of Additional Sections

#### 4.1 `assurance`
Records the target assurance level and the currently achieved level for the entire change package.

#### 4.2 `claims`
Declares what the change is intended to guarantee. Current status values distinguish at least:

- `proved`
- `model-checked`
- `tested`
- `runtime-mitigated`
- `waived`
- `unresolved`

#### 4.3 `assumptions`
Records the assumptions on which the assurance depends, including external systems and operational dependencies.

#### 4.4 `proofObligations`
Records which verification obligation exists for which claim, and whether it has been discharged.

#### 4.5 `counterexamples`
Preserves references to counterexample artifacts, whether still open or already resolved.

#### 4.6 `trustBoundary` / `runtimeControls` / `waivers`
Separates what is not closed by proof alone from what is controlled operationally or intentionally waived.

### 5. Staged Migration Policy

1. Phase 1: add schema, fixture, and docs
2. Phase 2: add opt-in v2 generation and Markdown renderer support
3. Phase 3: use v1 + v2 dual-write / dual-validate in selected CI lanes before considering a default switch

Current state:
- default generator stays on `scripts/change-package/generate.mjs` for v1
- `--schema-version v2` writes `artifacts/change-package/change-package-v2.json|md`
- `--dual-write` writes v1 and v2 in one command
- validator auto-detects v2 when the input has `schemaVersion: "change-package/v2"` and no explicit `--schema` override
- strict v2 validation checks schema, evidence counts, `artifactRefs` existence, proof-obligation claim references, waiver claim references, counterexample claim references, and optional policy-decision consistency

### 6. Manual Validation Example

```bash
node scripts/change-package/generate.mjs \
  --schema-version v2 \
  --claim-evidence-manifest artifacts/assurance/claim-evidence-manifest.json \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --assurance-summary artifacts/assurance/assurance-summary.json

node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package-v2.json \
  --schema schema/change-package-v2.schema.json \
  --artifact-root . \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --strict
```

This validates schema shape, required evidence IDs, present/missing count consistency, v2 claim references, artifact reference existence, and policy-decision alignment. Use `pnpm run change-package:generate:dual` and `pnpm run change-package:validate:dual` for opt-in dual-write / dual-validate migration checks.

### 7. Design Notes

- Do not collapse `proved`, `tested`, and `runtime-mitigated` into one category.
- Every waiver should retain `owner`, `expires`, `reason`, and `relatedClaimIds`.
- Treat v2 as an additive migration contract, not as an in-place overwrite of v1.

---

## 日本語

## 1. 目的

`change-package/v2` は、現行の `change-package/v1` に対して、変更の安全性説明を claim / assumption / proof obligation / counterexample / runtime control 単位で残すための拡張契約です。

既定契約は引き続き `change-package/v1` ですが、v2 は opt-in 生成、dual-write、strict validation、v2 artifact が存在する場合の PR summary 表示に接続済みです。

## 2. スキーマと fixture

- スキーマ: `schema/change-package-v2.schema.json`
- sample fixture: `fixtures/change-package/sample.change-package-v2.json`
- 現行 production contract: `schema/change-package.schema.json`（`change-package/v1`）

最小例（抜粋）:

```json
{
  "schemaVersion": "change-package/v2",
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
      "status": "model-checked",
      "artifactRefs": [
        "artifacts/assurance/assurance-summary.json"
      ]
    }
  ],
  "proofObligations": [
    {
      "id": "obl-1",
      "claimId": "no-negative-balance",
      "method": "tla",
      "status": "discharged",
      "artifactRefs": [
        "artifacts/hermetic-reports/formal/tla-summary.json"
      ]
    }
  ]
}
```

上記は `assurance` / `claims` / `proofObligations` の shape を示す**抜粋**です。`schema/change-package-v2.schema.json` を満たす完全なサンプルは `fixtures/change-package/sample.change-package-v2.json` を参照してください。

## 3. v1 との差分

| 項目 | v1 | v2 |
| --- | --- | --- |
| 主要目的 | PR リスク・evidence・rollout の集約 | 変更の assurance package を claim 単位で記録 |
| assurance level | なし | `assurance.targetLevel` / `achievedLevel` / `status` |
| claim | なし | `claims[]` |
| assumption | なし | `assumptions[]` |
| proof obligation | なし | `proofObligations[]` |
| counterexample | なし | `counterexamples[]` |
| trust boundary | 暗黙 | `trustBoundary.outsideModel` |
| runtime control | rollout/monitoring に分散 | `runtimeControls` に明示 |
| waiver | `exceptions[]` のみ | `waivers[]` を追加し claim とひも付け |

## 4. 追加セクションの意味

### 4.1 `assurance`
変更全体として要求した level と、現時点で達成した level を記録します。

### 4.2 `claims`
変更で何を保証したいのかを明示します。`status` は少なくとも次を区別します。

- `proved`
- `model-checked`
- `tested`
- `runtime-mitigated`
- `waived`
- `unresolved`

### 4.3 `assumptions`
保証の前提条件です。システム外部や運用上の依存もここに記録します。

### 4.4 `proofObligations`
どの claim に対して、どの検証 obligation があり、どこまで discharge されたかを記録します。

### 4.5 `counterexamples`
未解決・解消済みを問わず、反例 artifact への参照を change package に残します。

### 4.6 `trustBoundary` / `runtimeControls` / `waivers`
proof だけで閉じない範囲を分離して記述します。

## 5. 段階移行方針

1. Phase 1: schema/fixture/docs を追加する
2. Phase 2: opt-in v2 生成と Markdown renderer を追加する
3. Phase 3: 既定切替の前に、選択した CI lane で v1 + v2 dual-write / dual-validate を運用する

現時点では、次を維持します。
- 既定 generator: `scripts/change-package/generate.mjs` は v1 のまま
- `--schema-version v2` で `artifacts/change-package/change-package-v2.json|md` を出力する
- `--dual-write` で v1 と v2 を同時出力する
- validator は入力の `schemaVersion: "change-package/v2"` を自動検出し、明示 `--schema` がない場合は v2 schema を使う
- v2 strict validation は schema、evidence 件数、`artifactRefs` 実在、proof-obligation / waiver / counterexample の claim 参照、任意の policy-decision 整合性を確認する

## 6. 手動検証例

```bash
node scripts/change-package/generate.mjs \
  --schema-version v2 \
  --claim-evidence-manifest artifacts/assurance/claim-evidence-manifest.json \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --assurance-summary artifacts/assurance/assurance-summary.json

node scripts/change-package/validate.mjs \
  --file artifacts/change-package/change-package-v2.json \
  --schema schema/change-package-v2.schema.json \
  --artifact-root . \
  --policy-decision artifacts/ci/policy-decision-js-v1.json \
  --strict
```

このコマンドは schema validation、required evidence、present/missing 件数、v2 の claim 参照、artifact ref 実在、policy-decision 整合性を確認します。段階移行確認には `pnpm run change-package:generate:dual` と `pnpm run change-package:validate:dual` を使用します。

## 7. 設計上の注意

- `proved` と `tested` と `runtime-mitigated` を混同しない
- `waivers` は必ず owner / expires / reason / relatedClaimIds を持たせる
- v2 は v1 の完全置換ではなく、段階移行前提の追加契約として扱う
