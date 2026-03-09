# Assurance Profile v1

> Language / 言語: English | 日本語

---

## English (Summary)

`assurance-profile/v1` is the Phase 1 contract that binds business claims to required assurance levels, validation lanes, and evidence kinds.

Current scope:
- schema and fixture validation
- optional references from Context Pack v1
- documentation of level semantics
- report-only `verify:assurance` aggregation
- Verify Lite collection of assurance summary
- label-gated strict enforcement via `enforce-assurance`

Not in scope yet:
- full achieved-level automation
- direct `policy-gate` interpretation of assurance summary

---

## 日本語

## 1. 目的

`assurance-profile/v1` は、業務上の claim を次の要素に機械可読で結び付けるための入力契約です。

- target assurance level
- required validation lanes
- required evidence kinds
- Context Pack 上の object / morphism / diagram / acceptance test 参照

現時点では、**schema とドキュメント整備、`verify:assurance` による summary 生成、Verify Lite での assurance 収集、および `enforce-assurance` ラベル時の strict enforcement** までを実装済みとします。通常 PR は report-only のまま維持し、strict 化は label-gated でのみ有効化します。

## 2. スキーマ

- スキーマ: `schema/assurance-profile.schema.json`
- sample fixture: `fixtures/assurance/sample.assurance-profile.json`
- Context Pack 側の参照先: `schema/context-pack-v1.schema.json` の optional `assurance`

最小構造:

```json
{
  "schemaVersion": "assurance-profile/v1",
  "profileId": "inventory-baseline-v1",
  "scope": {
    "contextPackSources": ["spec/context-pack/**/*.{yml,yaml,json}"],
    "componentGlobs": ["src/domain/inventory/**"]
  },
  "claims": [
    {
      "id": "no-negative-stock",
      "statement": "Inventory stock never becomes negative after an accepted reservation.",
      "kind": "safety",
      "criticality": "high",
      "targetLevel": "A2",
      "minIndependentSources": 2,
      "requiredLanes": ["spec", "behavior", "model"],
      "requiredEvidenceKinds": ["property", "product-coproduct", "counterexample-closed"]
    }
  ]
}
```

## 3. assurance level の暫定意味

| Level | 意味 | 典型 evidence |
| --- | --- | --- |
| `A0` | 契約・lint・build が成立している最低限の整合性 | schema, lint, type, build |
| `A1` | unit/integration/property によりサンプル的に確認済み | unit, integration, property |
| `A2` | 構造的な仕様検証まで到達 | product-coproduct, natural-transformation, conformance |
| `A3` | 反例探索やモデル検査で critical claim を閉じている | model-check, counterexample-closed |
| `A4` | proof-carrying な厳密保証を持つ | proof |

この表は Phase 1/2 の暫定定義です。`verify:assurance` は lane / evidence / warning を集約しますが、最終的な `achievedLevel` 自動判定はまだ後続フェーズです。

## 4. claim の設計指針

1. claim は実装方針ではなく、業務上の正しさを述べる
2. `criticality` は low/medium/high/critical の 4 段階で記録する
3. `requiredLanes` は同じ誤解を共有しない観点で複数レーンを選ぶ
4. `requiredEvidenceKinds` は「何を集めれば claim が説明できるか」を明示する
5. `scopeRefs` は Context Pack の ID にひも付け、仕様断片との対応を残す

### 4.1 `requiredLanes` と `minIndependentSources`

- `requiredLanes` は「何本テストがあるか」ではなく、「異なる観点から claim を叩いているか」を表します。
- `minIndependentSources` は `verify:assurance` が使う最小 independence rule です。
- 未指定時の既定値:
  - `critical` / `high`: `2`
  - `medium` / `low`: `1`

例:
- `spec + behavior + model` を要求する claim は、仕様・実装・モデルの少なくとも 2 系統以上が観測されることを期待する
- `behavior` だけを増やしても、すべて `source-derived` なら independence warning は解消しない

## 5. Context Pack v1 との結合

Context Pack には optional `assurance` セクションを追加できます。

```yaml
assurance:
  profile: inventory-baseline-v1
  claim_refs:
    - no-negative-stock
```

用途:
- どの Context Pack がどの assurance profile を参照するかを明示する
- morphism / diagram / acceptance test と claim を間接的に結ぶ
- assurance 未導入リポジトリでは、このセクションを省略して既存挙動を維持する

## 6. 現時点の非目標

- `verify-lite-run-summary` 自体へ achieved level を書き戻すこと
- `policy-gate` が assurance artifact 自体を直接解釈して blocking 判定すること
- `policy-input` / `policy-decision` への assurance 判定追加
- 全 claim の formal proof
- assurance 未設定 PR を既定で blocking にすること

## 7. 変更時の注意

- 新しい claim kind や evidence kind を追加する場合は、`schema/assurance-profile.schema.json` と本ドキュメントを同一 PR で更新する
- 新しい schema を追加したため、`docs/reference/CONTRACT-CATALOG.md` を同時に更新する
- sample fixture を変更する場合は `tests/contracts/assurance-profile-contract.test.ts` を更新する
- lane taxonomy は `docs/quality/assurance-lanes.md` を SSOT とし、本書では入力契約への接続だけを記述する
- 実行手順と strict / report-only の使い分けは `docs/quality/assurance-operations-runbook.md` を正とする
