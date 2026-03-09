# Assurance Model

> Language / 言語: English | 日本語

---

## English (Summary)

This document defines the working assurance model for ae-framework:
- claim
- level
- validation lane
- evidence kind
- assumption / waiver / runtime control

It is a positioning and contract-alignment document. Full automation is introduced incrementally.

---

## 日本語

## 1. 目的

ae-framework でいう assurance を、実装・運用・ドキュメント間で同じ意味に揃えるための基準資料です。

この文書は次を定義します。
- claim
- assurance level
- validation lane
- evidence kind
- assumption / waiver / runtime control

## 2. 基本単位

### 2.1 claim
業務上または設計上、何を保証したいのかを記述する単位です。

例:
- Ledger balance never becomes negative.
- Replay is idempotent.
- Required audit fields are always emitted.

### 2.2 level
保証の重さを claim 単位で表す段階です。

| Level | 意味 | 典型的な裏付け |
| --- | --- | --- |
| `A0` | 契約・lint・build が成立 | schema, lint, build |
| `A1` | 単体/結合/property で基本確認 | unit, integration, property |
| `A2` | 構造的な仕様整合まで確認 | Context Pack, product-coproduct, natural-transformation, conformance |
| `A3` | モデル検査や反例探索で critical claim を閉じる | TLA, Alloy, SMT, CSP, counterexample-closed |
| `A4` | proof-carrying な保証まで到達 | Lean, Kani, equivalence proof |

### 2.3 validation lane
同じ誤解を共有しないための検証経路です。

- `spec`
- `behavior`
- `adversarial`
- `model`
- `proof`
- `runtime`

| lane | 代表 producer | 主な役割 |
| --- | --- | --- |
| `spec` | Context Pack validate / functor / natural transformation / product-coproduct / phase5 | 仕様記述と構造整合の確認 |
| `behavior` | unit / integration / property / MBT | 実装振る舞いの確認 |
| `adversarial` | mutation / fuzz / differential / counterexample replay | 壊れ方・反例探索の確認 |
| `model` | conformance / TLA / Alloy / SMT / CSP / SPIN | モデル・状態遷移・規則整合の確認 |
| `proof` | Lean / Kani / equivalence proof | 機械的 proof による厳密保証 |
| `runtime` | monitoring / alert / rollout guard / runtime conformance | 運用時の補償制御 |

taxonomy と independence rule の詳細は `docs/quality/assurance-lanes.md` を参照してください。

### 2.4 evidence kind
claim の説明に使う証跡の型です。

- schema / lint / type / build
- unit / integration / property
- conformance / product-coproduct / natural-transformation
- model-check / counterexample-closed
- proof
- runtime-control
- waiver

## 3. 補助要素

### 3.1 assumption
保証の前提条件です。DB isolation、clock source、外部SaaSの整合性など、モデル外の前提を明示します。

### 3.2 runtime control
proof や model-check で閉じない部分を、feature flag / alert / rollout / monitor で補う制御です。

### 3.3 waiver
例外を許容する場合の記録です。owner / expires / reason / related claims を残します。

## 4. 現行実装との対応

現時点で main に実装済み:
- Context Pack v1 とその拡張マップ群
- verify-lite summary
- formal summary / formal aggregate
- policy gate / change package v1
- assurance profile v1
- change-package v2
- report-only `verify:assurance` summary generation
- `enforce-assurance` ラベル時の Verify Lite strict enforcement
- PR / release / post-deploy summary への assurance 表示

未実装または段階導入中:
- claim ごとの achieved level 集約
- policy-gate への assurance-aware enforcement

## 5. 運用上の原則

1. claim を書かずに「高保証」とだけ表現しない
2. `proved` / `model-checked` / `tested` / `runtime-mitigated` / `waived` / `unresolved` を混同しない
3. heavy assurance は high-risk change に限定し、通常 PR lane を維持する
4. summary artifact を判断面の一次情報とし、raw log は補助とする
5. assumption と trust boundary を残し、保証範囲を過大表現しない

## 6. 関連契約

main に存在する契約:
- `schema/context-pack-v1.schema.json`
- `schema/assurance-profile.schema.json`
- `schema/assurance-summary.schema.json`
- `schema/change-package.schema.json`
- `schema/change-package-v2.schema.json`

段階導入中の契約:
- `schema/verify-lite-run-summary.schema.json`（将来拡張候補）
- `schema/policy-input-v1.schema.json` / `schema/policy-decision-v1.schema.json`（将来拡張候補）
