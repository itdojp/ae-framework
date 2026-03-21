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

Phase 1 currently covers schema and documentation only. The default production generator / validator contract remains `change-package/v1`.

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
2. Phase 2: add `generate-v2.mjs` and Markdown renderer support
3. Phase 3: move to v1 + v2 dual-write / dual-validate

Current state:
- generator stays on `scripts/change-package/generate.mjs` for v1
- default validator stays on `scripts/change-package/validate.mjs --schema schema/change-package.schema.json`
- strict mode is not yet wired to v2

### 6. Manual Validation Example

```bash
node scripts/change-package/validate.mjs \
  --file fixtures/change-package/sample.change-package-v2.json \
  --schema schema/change-package-v2.schema.json
```

This validates schema shape and evaluates evidence consistency, including required evidence IDs and present/missing count mismatches. Artifact-ref existence checks and CI dual-write remain follow-up work.

### 7. Design Notes

- Do not collapse `proved`, `tested`, and `runtime-mitigated` into one category.
- Every waiver should retain `owner`, `expires`, `reason`, and `relatedClaimIds`.
- Treat v2 as an additive migration contract, not as an in-place overwrite of v1.

---

## 日本語

## 1. 目的

`change-package/v2` は、現行の `change-package/v1` に対して、変更の安全性説明を claim / assumption / proof obligation / counterexample / runtime control 単位で残すための拡張契約です。

Phase 1 の現時点では、**schema とドキュメントの定義**までを対象とします。既存の generator / validator の既定契約は引き続き `v1` です。

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
2. Phase 2: `generate-v2.mjs` / Markdown renderer を追加する
3. Phase 3: v1 + v2 dual-write / dual-validate に移行する

現時点では、次を維持します。
- 既存 generator: `scripts/change-package/generate.mjs` は v1 のまま
- 既存 validator default: `scripts/change-package/validate.mjs --schema schema/change-package.schema.json`
- strict mode は v2 へまだ連動しない

## 6. 手動検証例

```bash
node scripts/change-package/validate.mjs \
  --file fixtures/change-package/sample.change-package-v2.json \
  --schema schema/change-package-v2.schema.json
```

このコマンドは schema validation を実施します。artifact ref の実在確認や CI dual-write は後続 Issue の対象です。

## 7. 設計上の注意

- `proved` と `tested` と `runtime-mitigated` を混同しない
- `waivers` は必ず owner / expires / reason / relatedClaimIds を持たせる
- v2 は v1 の完全置換ではなく、段階移行前提の追加契約として扱う
