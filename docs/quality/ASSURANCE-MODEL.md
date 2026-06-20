---
docRole: ssot
lastVerified: '2026-06-06'
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

PR and release summaries use a richer per-claim review vocabulary. The canonical `claim-evidence-manifest/v1.claims[].status` vocabulary remains `partial`, `satisfied`, `waived`, and `unresolved`; evidence strength is represented through evidence refs, achieved levels, and the projected states below, not by changing the manifest status enum.

| Status | Meaning | Policy note |
| --- | --- | --- |
| `proved` | Proof-lane evidence, such as Lean/Kani/equivalence proof, is linked and scoped to the claim. | Strongest evidence state; assumptions and proof scope must remain visible. |
| `model-checked` | Model checking or counterexample exploration has covered the stated model scope. | Record bounded scope, model assumptions, and any counterexample closure. |
| `tested` | Unit, integration, property, conformance, MBT, or equivalent behavior evidence supports the claim. | Do not describe this as proof. |
| `runtime-mitigated` | Runtime guard, circuit breaker, feature flag, alert, rollout guard, or monitor reduces operational risk. | Mitigation is not proof or model checking. |
| `waived` | A time-bounded exception was approved with `owner`, `reason`, `expires`, `relatedClaimIds`, `evidenceRefs`, and `sourceArtifactId` provenance. | Waiver keeps risk visible; it does not satisfy the claim. |
| `unresolved` | Evidence is missing, stale, failed, insufficient, or not yet judged. | Default PR behavior may be report-only, but summaries must preserve the unresolved count. |

`claim-level-summary/v1` also uses projection states such as `satisfied`, `failed`, and `not-applicable` for PR/release reporting. Those projection states do not replace the manifest claim-status vocabulary.

`change-package/v2.claims[].status` is a package / release-decision outcome field. It may retain `satisfied`, `failed`, and `not-applicable` package states for reviewable release packages, but those package states do not redefine `claim-evidence-manifest/v1` claim status or evidence-kind vocabulary.

Manifest and PR-summary displays must label manifest counts as manifest support status, not proof status. When a `change-package/v2` claim is imported, `tested` contributes behavior evidence, `model-checked` contributes model evidence, and `proved` contributes proof evidence. Imported `runtime-mitigated` and `not-applicable` package states remain `partial` manifest support unless another explicit contract migration changes the source vocabulary; imported `failed` package states remain `unresolved`. A waiver stays `waived` only with an explicit waiver reference and must never be displayed as `satisfied`.

`agentPrAssurance.metrics.required_lane_compliance.notApplicable` is separate from the claim-status vocabulary. It is only a metric-level denominator state for "no required lanes"; producers must not emit `not-applicable` as a manifest claim-status value unless the manifest schema and migration policy explicitly allow it.

### 3. Supporting elements

#### 3.1 Assumption
An assumption is a prerequisite for the guarantee. Typical examples include DB isolation, clock source behavior, or consistency guarantees of external SaaS dependencies.

#### 3.2 Runtime control
Runtime control compensates for areas that are not closed by proof or model checking, such as feature flags, alerts, rollout guards, and monitors.

#### 3.3 Waiver
A waiver is the record used when an exception is accepted. It should retain `owner`, `expires`, `reason`, `relatedClaimIds`, `evidenceRefs`, and `sourceArtifactId` provenance.

### 3.4 Escalation lanes

Escalation is driven by `policy/risk-policy.yml` rather than by the producer
agent. The default lane is report-only. `risk:high` changes promote missing
required lanes, missing evidence, Boundary Map drift, waiver metadata gaps, and
unresolved claims to manual reviewer disposition through human approvals,
required policy labels, and the plan artifact. `enforce-assurance` selects
strict blocking after Verify Lite artifacts are available. Critical-core
boundaries or explicit assurance profiles may choose manual approval or block
for their declared required lanes.

Waivers remain exceptions, not evidence upgrades. Missing `owner`, `reason`,
`expires`, `relatedClaimIds`, `evidenceRefs`, or `sourceArtifactId` provenance
is report-only in the default lane and blocking in strict assurance mode.

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
- `assurance-summary/v1.reviewSurface` for reviewer-facing aggregation of producer signals, Context Pack inputs, Boundary Map findings, claim evidence, waivers, policy decisions, residual risks, and recommended reviewer action
- policy-gate decision artifacts carry a report-only waiver-aware assurance section when `claim-evidence-manifest/v1` is available
- report-only agent PR assurance metrics are defined for claim coverage, unresolved claims, waiver expiry risk, required lane compliance, evidence completeness, agent regression signal, MTTR, and false block observation

`assurance-summary/v1.reviewSurface` is a review aid, not a merge decision. It keeps producer assertions separate from control-plane judgment and surfaces Boundary Map drift as design-boundary evidence. It preserves the distinction between tested and proved, waived and satisfied, and runtime-mitigated and proof.

Not yet implemented or still being phased in:
- change-package v2 preview contract (schema / docs only)
- strict assurance-aware enforcement directly inside `policy-gate` (the default mode remains report-only)

### 5. Operating principles

1. Do not describe something as “high assurance” without stating the claim.
2. Do not conflate `proved`, `model-checked`, `tested`, `runtime-mitigated`, `waived`, and `unresolved`.
3. Limit heavy assurance to high-risk changes and keep the normal PR lane fast.
4. Use summary artifacts as the primary input for judgment; raw logs are supporting evidence.
5. Retain assumptions and trust boundaries so that the guarantee scope is not overstated.
6. Treat agent PR assurance metrics as report-only judgment aids until policy explicitly promotes them; metric-level `notApplicable` does not change claim status vocabulary.

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
- `schema/quality-scorecard.schema.json`
- `schema/agentic-metrics.schema.json`

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

PR / release summary は、claim 単位の richer review vocabulary を使います。canonical な `claim-evidence-manifest/v1.claims[].status` vocabulary は `partial`、`satisfied`、`waived`、`unresolved` に限定します。evidence strength は manifest status enum の変更ではなく、evidence refs、achieved level、下記の projection state で表現します。

| Status | 意味 | Policy note |
| --- | --- | --- |
| `proved` | Lean / Kani / equivalence proof などの proof lane evidence が claim に scope 付きで紐付く。 | 最も強い evidence state。assumption と proof scope を残す。 |
| `model-checked` | model checking または counterexample exploration が明示された model scope を探索済み。 | bounded scope、model assumption、counterexample closure を記録する。 |
| `tested` | unit / integration / property / conformance / MBT などの behavior evidence が claim を支える。 | proof と表現しない。 |
| `runtime-mitigated` | runtime guard、circuit breaker、feature flag、alert、rollout guard、monitor などで operational risk を緩和済み。 | mitigation は proof / model checking ではない。 |
| `waived` | `owner`、`reason`、`expires`、`relatedClaimIds`、`evidenceRefs`、`sourceArtifactId` provenance を持つ期限付き例外として承認済み。 | risk を可視化し続ける。claim を satisfied に変換しない。 |
| `unresolved` | evidence が不足、古い、失敗、不十分、または未判断。 | 通常 PR では report-only の場合があるが、summary には unresolved count を残す。 |

`claim-level-summary/v1` は PR / release projection 用に `satisfied`、`failed`、`not-applicable` なども扱います。これらの projection state は manifest claim-status vocabulary を置き換えるものではありません。

`change-package/v2.claims[].status` は package / release-decision outcome field です。review 可能な release package のために `satisfied`、`failed`、`not-applicable` などの package state を保持できますが、それらは `claim-evidence-manifest/v1` の claim status や evidence-kind vocabulary を再定義しません。

Manifest と PR summary の表示では、manifest count を proof status ではなく manifest support status として明示します。`change-package/v2` claim を取り込む場合、`tested` は behavior evidence、`model-checked` は model evidence、`proved` は proof evidence として扱います。`runtime-mitigated` と `not-applicable` の package state は、source vocabulary を変更する明示的な contract migration がない限り `partial` manifest support のままにし、`failed` package state は `unresolved` のままにします。waiver は明示的な waiver reference がある場合だけ `waived` とし、`satisfied` として表示してはいけません。

`agentPrAssurance.metrics.required_lane_compliance.notApplicable` は claim status vocabulary とは別の概念です。「required lane がない」ことを表す metric-level denominator state に限られ、manifest schema と migration policy が明示的に許可するまで、producer は `not-applicable` を manifest claim-status value として emit してはいけません。

### 3. 補助要素

#### 3.1 前提条件（assumption）
保証の前提条件です。DB isolation、clock source、外部 SaaS の整合性など、モデル外の前提を明示します。

#### 3.2 運用時制御（runtime control）
proof や model-check で閉じない部分を、feature flag / alert / rollout / monitor で補う制御です。

#### 3.3 例外記録（waiver）
例外を許容する場合の記録です。`owner` / `expires` / `reason` / `relatedClaimIds` / `evidenceRefs` / `sourceArtifactId` provenance を残します。

### 3.4 escalation lane

Escalation は producer agent ではなく `policy/risk-policy.yml` によって決まります。
既定 lane は report-only です。`risk:high` 変更では required lane 不足、evidence 不足、
Boundary Map drift、waiver metadata gap、unresolved claim を、human approval、
required policy label、plan artifact による reviewer disposition へ昇格します。
`enforce-assurance` は Verify Lite artifact が揃った後に strict blocking を選択します。
critical-core boundary または明示的 assurance profile は、宣言された required lane に対して
manual approval または block を選択できます。

waiver は例外であり、evidence upgrade ではありません。`owner`、`reason`、`expires`、
`relatedClaimIds`、`evidenceRefs`、`sourceArtifactId` provenance が欠ける場合、既定 lane では
report-only、strict assurance mode では blocking です。

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
- producer signal、Context Pack input、Boundary Map finding、claim evidence、waiver、policy decision、residual risk、recommended reviewer action を reviewer 向けに集約する `assurance-summary/v1.reviewSurface`
- `claim-evidence-manifest/v1` がある場合の、policy-gate decision artifact 内の report-only な waiver-aware assurance section
- claim coverage、unresolved claim、waiver expiry risk、required lane compliance、evidence completeness、agent regression signal、MTTR、false block observation を対象にした report-only agent PR assurance metrics

`assurance-summary/v1.reviewSurface` は review 補助であり merge decision ではありません。producer assertion を control-plane judgment から分離し、Boundary Map drift を design-boundary evidence として表示します。`tested` と `proved`、`waived` と `satisfied`、`runtime-mitigated` と `proof` の区別を維持します。

未実装または段階導入中:
- change-package v2 preview 契約（schema / docs のみ）
- policy-gate の strict assurance-aware enforcement（既定は report-only のまま）

### 5. 運用上の原則

1. claim を書かずに「高保証」とだけ表現しない
2. `proved` / `model-checked` / `tested` / `runtime-mitigated` / `waived` / `unresolved` を混同しない
3. heavy assurance は high-risk change に限定し、通常の PR レーンを維持する
4. サマリー成果物を判断面の一次情報とし、raw log は補助とする
5. 前提条件（assumption）と trust boundary を残し、保証範囲を過大表現しない
6. agent PR assurance metrics は、明示的にpolicy昇格されるまでは report-only の判断補助として扱う。metric-level `notApplicable` は claim status vocabulary を変更しない

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
- `schema/quality-scorecard.schema.json`
- `schema/agentic-metrics.schema.json`

段階導入中の契約:
- `schema/verify-lite-run-summary.schema.json`（将来拡張候補）
