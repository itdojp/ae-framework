---
docRole: ssot
lastVerified: '2026-04-05'
owner: assurance-model
verificationCommand: pnpm -s run check:doc-consistency
---
# Assurance Model

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
This document defines the working assurance model for ae-framework so that implementation, operations, and documentation use the same meaning for assurance-related terms.

It fixes the meaning of:
- claim
- assurance level
- validation lane
- evidence kind
- assumption / waiver / runtime control

This is both a positioning document and a contract-alignment reference. Full automation is introduced incrementally, but the terminology is intended to remain stable.

### 2. Basic unit

#### 2.1 Claim
A claim is the unit that states what the system wants to guarantee from a business or design perspective.

Examples:
- Ledger balance never becomes negative.
- Replay is idempotent.
- Required audit fields are always emitted.

#### 2.2 Assurance level
Assurance level expresses the weight of assurance for each claim.

| Level | Meaning | Typical backing evidence |
| --- | --- | --- |
| `A0` | contracts, lint, and build remain valid | schema, lint, build |
| `A1` | basic behavior is checked by unit / integration / property testing | unit, integration, property |
| `A2` | structural specification consistency is also checked | Context Pack, product-coproduct, natural-transformation, conformance |
| `A3` | critical claims are closed by model checking or counterexample exploration | TLA, Alloy, SMT, CSP, counterexample-closed |
| `A4` | proof-carrying assurance is reached | Lean, Kani, equivalence proof |

#### 2.3 Validation lane
A validation lane is an independent verification path so that a single misunderstanding is not repeated across all checks.

- `spec`
- `behavior`
- `adversarial`
- `model`
- `proof`
- `runtime`

| lane | Representative producer | Primary role |
| --- | --- | --- |
| `spec` | Context Pack validate / functor / natural transformation / product-coproduct / phase5 | verify specification description and structural consistency |
| `behavior` | unit / integration / property / MBT | verify implementation behavior |
| `adversarial` | mutation / fuzz / differential / counterexample replay | verify failure modes and counterexample search |
| `model` | conformance / TLA / Alloy / SMT / CSP / SPIN | verify models, state transitions, and rule consistency |
| `proof` | Lean / Kani / equivalence proof | provide machine-checked proof-level guarantees |
| `runtime` | monitoring / alert / rollout guard / runtime conformance | provide operational compensation and runtime controls |

For taxonomy details and the independence rule, see `docs/quality/assurance-lanes.md`.

#### 2.4 Evidence kind
Evidence kind is the type used to explain why a claim is considered supported.

- schema / lint / type / build
- unit / integration / property
- conformance / product-coproduct / natural-transformation
- model-check / counterexample-closed
- proof
- runtime-control
- waiver

#### 2.5 Claim status vocabulary

Claim status is the per-claim review vocabulary used by PR and release summaries. It describes the strongest current evidence state for the claim, not the trustworthiness of the producer that reported it.

| Status | Meaning | Policy note |
| --- | --- | --- |
| `proved` | Proof-lane evidence, such as Lean/Kani/equivalence proof, is linked and scoped to the claim. | Strongest evidence state; assumptions and proof scope must remain visible. |
| `model-checked` | Model checking or counterexample exploration has covered the stated model scope. | Record bounded scope, model assumptions, and any counterexample closure. |
| `tested` | Unit, integration, property, conformance, MBT, or equivalent behavior evidence supports the claim. | Do not describe this as proof. |
| `runtime-mitigated` | Runtime guard, circuit breaker, feature flag, alert, rollout guard, or monitor reduces operational risk. | Mitigation is not proof or model checking. |
| `waived` | A time-bounded exception was approved with owner, reason, expiry, affected claim, and evidence link. | Waiver keeps risk visible; it does not satisfy the claim. |
| `unresolved` | Evidence is missing, stale, failed, insufficient, or not yet judged. | Default PR behavior may be report-only, but summaries must preserve the unresolved count. |

`claim-level-summary/v1` also uses projection states such as `satisfied`, `failed`, and `not-applicable` for PR/release reporting. Those projection states do not replace the six primary evidence states above.

### 3. Supporting elements

#### 3.1 Assumption
An assumption is a prerequisite for the guarantee. Typical examples include DB isolation, clock source behavior, or consistency guarantees of external SaaS dependencies.

#### 3.2 Runtime control
Runtime control compensates for areas that are not closed by proof or model checking, such as feature flags, alerts, rollout guards, and monitors.

#### 3.3 Waiver
A waiver is the record used when an exception is accepted. It should retain owner, expiry, reason, and related claims.

### 4. Mapping to the current implementation

Implemented on current `main`:
- Context Pack v1 and its extended map family
- verify-lite summary
- formal summary / formal aggregate
- policy-gate / change-package v1 (default flow)
- assurance profile v1
- report-only `verify:assurance` summary generation
- strict assurance enforcement when the `enforce-assurance` label is set
- assurance display in PR / release / post-deploy summaries
- policy-gate decision artifacts carry a report-only waiver-aware assurance section when `claim-evidence-manifest/v1` is available

Not yet implemented or still being phased in:
- change-package v2 preview contract (schema / docs only)
- strict assurance-aware enforcement directly inside `policy-gate` (the default mode remains report-only)

### 5. Operating principles

1. Do not describe something as “high assurance” without stating the claim.
2. Do not conflate `proved`, `model-checked`, `tested`, `runtime-mitigated`, `waived`, and `unresolved`.
3. Limit heavy assurance to high-risk changes and keep the normal PR lane fast.
4. Use summary artifacts as the primary input for judgment; raw logs are supporting evidence.
5. Retain assumptions and trust boundaries so that the guarantee scope is not overstated.

### 6. Related contracts

Contracts already present on `main`:
- `schema/context-pack-v1.schema.json`
- `schema/assurance-profile.schema.json`
- `schema/assurance-summary.schema.json`
- `schema/change-package.schema.json`
- `schema/change-package-v2.schema.json`
- `schema/claim-evidence-manifest.schema.json`
- `schema/policy-input-v1.schema.json`
- `schema/policy-decision-v1.schema.json`

Contracts that remain incremental candidates:
- `schema/verify-lite-run-summary.schema.json`

---

## 日本語

### 1. 目的

ae-framework における assurance（保証）を、実装・運用・ドキュメント間で同じ意味に揃えるための基準資料です。

この文書は次を定義します。
- クレーム（claim）
- 保証レベル（assurance level）
- 検証レーン（validation lane）
- 証跡種別（evidence kind）
- 前提条件 / 例外記録 / 運用時制御

これは位置付け文書であり、かつ契約整合（contract-alignment）の参照基準でもあります。自動化は段階導入ですが、用語自体は安定させる前提です。

### 2. 基本単位

#### 2.1 クレーム（claim）
業務上または設計上、何を保証したいのかを記述する単位です。

例:
- Ledger balance never becomes negative.
- Replay is idempotent.
- Required audit fields are always emitted.

#### 2.2 保証レベル（assurance level）
保証の重さをクレーム（claim）単位で表す段階です。

| Level | 意味 | 典型的な裏付け |
| --- | --- | --- |
| `A0` | 契約・lint・build が成立 | schema, lint, build |
| `A1` | 単体/結合/property で基本確認 | unit, integration, property |
| `A2` | 構造的な仕様整合まで確認 | Context Pack, product-coproduct, natural-transformation, conformance |
| `A3` | モデル検査や反例探索で critical claim を閉じる | TLA, Alloy, SMT, CSP, counterexample-closed |
| `A4` | proof-carrying な保証まで到達 | Lean, Kani, equivalence proof |

#### 2.3 検証レーン（validation lane）
同じ誤解を共有しないための検証経路です。

- `spec`
- `behavior`
- `adversarial`
- `model`
- `proof`
- `runtime`

| lane | 主な生成元（producer） | 主な役割 |
| --- | --- | --- |
| `spec` | Context Pack validate / functor / natural transformation / product-coproduct / phase5 | 仕様記述と構造整合の確認 |
| `behavior` | unit / integration / property / MBT | 実装振る舞いの確認 |
| `adversarial` | mutation / fuzz / differential / counterexample replay | 壊れ方・反例探索の確認 |
| `model` | conformance / TLA / Alloy / SMT / CSP / SPIN | モデル・状態遷移・規則整合の確認 |
| `proof` | Lean / Kani / equivalence proof | 機械的 proof による厳密保証 |
| `runtime` | monitoring / alert / rollout guard / runtime conformance | 運用時の補償制御 |

taxonomy と独立性ルール（independence rule）の詳細は `docs/quality/assurance-lanes.md` を参照してください。

#### 2.4 証跡種別（evidence kind）
クレーム（claim）の説明に使う証跡の型です。

- schema / lint / type / build
- unit / integration / property
- conformance / product-coproduct / natural-transformation
- model-check / counterexample-closed
- proof
- runtime-control
- waiver

#### 2.5 claim status vocabulary

Claim status は、PR / release summary で使う claim 単位の review 語彙です。claim に対する現時点の最も強い evidence state を示し、その producer が正しいかどうかを示すものではありません。

| Status | 意味 | Policy note |
| --- | --- | --- |
| `proved` | Lean / Kani / equivalence proof などの proof lane evidence が claim に scope 付きで紐付く。 | 最も強い evidence state。assumption と proof scope を残す。 |
| `model-checked` | model checking または counterexample exploration が明示された model scope を探索済み。 | bounded scope、model assumption、counterexample closure を記録する。 |
| `tested` | unit / integration / property / conformance / MBT などの behavior evidence が claim を支える。 | proof と表現しない。 |
| `runtime-mitigated` | runtime guard、circuit breaker、feature flag、alert、rollout guard、monitor などで operational risk を緩和済み。 | mitigation は proof / model checking ではない。 |
| `waived` | owner、reason、expiry、affected claim、evidence link を持つ期限付き例外として承認済み。 | risk を可視化し続ける。claim を satisfied に変換しない。 |
| `unresolved` | evidence が不足、古い、失敗、不十分、または未判断。 | 通常 PR では report-only の場合があるが、summary には unresolved count を残す。 |

`claim-level-summary/v1` は PR / release projection 用に `satisfied`、`failed`、`not-applicable` なども扱います。これらの projection state は上記6つの primary evidence state を置き換えるものではありません。

### 3. 補助要素

#### 3.1 前提条件（assumption）
保証の前提条件です。DB isolation、clock source、外部 SaaS の整合性など、モデル外の前提を明示します。

#### 3.2 運用時制御（runtime control）
proof や model-check で閉じない部分を、feature flag / alert / rollout / monitor で補う制御です。

#### 3.3 例外記録（waiver）
例外を許容する場合の記録です。owner / expires / reason / related claims を残します。

### 4. 現行実装との対応

現時点で main に実装済み:
- Context Pack v1 とその拡張マップ群
- verify-lite サマリー
- formal サマリー / formal aggregate
- policy-gate / change-package v1（既定フロー）
- assurance profile v1
- 報告専用（report-only）の `verify:assurance` サマリー生成
- `enforce-assurance` ラベル時の strict assurance enforcement
- PR / release / post-deploy summary への assurance 表示
- `claim-evidence-manifest/v1` がある場合の、policy-gate decision artifact 内の report-only な waiver-aware assurance section

未実装または段階導入中:
- change-package v2 preview 契約（schema / docs のみ）
- policy-gate の strict assurance-aware enforcement（既定は report-only のまま）

### 5. 運用上の原則

1. claim を書かずに「高保証」とだけ表現しない
2. `proved` / `model-checked` / `tested` / `runtime-mitigated` / `waived` / `unresolved` を混同しない
3. heavy assurance は high-risk change に限定し、通常の PR レーンを維持する
4. サマリー成果物を判断面の一次情報とし、raw log は補助とする
5. 前提条件（assumption）と trust boundary を残し、保証範囲を過大表現しない

### 6. 関連契約

main に存在する契約:
- `schema/context-pack-v1.schema.json`
- `schema/assurance-profile.schema.json`
- `schema/assurance-summary.schema.json`
- `schema/change-package.schema.json`
- `schema/change-package-v2.schema.json`
- `schema/claim-evidence-manifest.schema.json`
- `schema/policy-input-v1.schema.json`
- `schema/policy-decision-v1.schema.json`

段階導入中の契約:
- `schema/verify-lite-run-summary.schema.json`（将来拡張候補）
