---
docRole: ssot
lastVerified: '2026-03-10'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Change Package v2

> Language / 言語: English | 日本語

---

## English (Summary)

`change-package/v2` is the proof-carrying extension of the existing change package contract.

Current Phase 1 scope:
- schema definition
- sample fixture
- migration notes from v1 to v2

Current non-goals:
- switching the default generator/validator from v1 to v2
- automatic dual-write in CI
- strict artifact existence enforcement

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
