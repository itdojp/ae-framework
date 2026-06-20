---
docRole: ssot
lastVerified: '2026-06-20'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency
---

# Assurance Control Plane Policy

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This policy is the canonical product decision record for ae-framework as an agent-neutral assurance control plane. It is written for human maintainers and Codex-driven work so that future implementation issues strengthen judgment-side assurance instead of rebuilding a coding-agent harness. The product thesis is `Bring your own agent. Keep your assurance plane.`

Use this document with:

- `docs/product/ASSURANCE-CONTROL-PLANE.md` for the product overview.
- `docs/product/AGENT-NEUTRAL-ASSURANCE-ROADMAP.md` for the 90-day BYO-agent assurance rollout plan.
- `docs/quality/ASSURANCE-MODEL.md` for claim, assurance level, validation lane, evidence, assumption, waiver, and runtime-control terminology.
- `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md` for implementation-aligned architecture.
- `docs/architecture/ASSURANCE-CONTROL-PLANE-DETAILED-DESIGN.md` for detailed claim/evidence/policy/package design.
- `docs/reference/CONTRACT-CATALOG.md` for current schema, producer, and consumer mappings.
- `docs/agents/evidence-adapters.md` for raw producer output normalization into existing judgment artifacts.
- `docs/ci/agent-pr-assurance-metrics.md` for report-only agent PR quality metrics.
- `docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md` for the 2026-05 current-state audit.

### 2. Product boundary

#### 2.1 What ae-framework is

- An agent-neutral BYO-agent assurance control plane for agent-driven SDLC.
- A judgment-side contract layer for specifications, verification outputs, evidence artifacts, policy decisions, PR summaries, release summaries, and post-deploy assurance.
- A risk-based operating model that can add heavier verification only when a claim, risk profile, or policy requires it.
- A contract catalog and artifact validation surface that keeps producer outputs reviewable and comparable over time.

#### 2.2 What ae-framework is not

- It is not a replacement for Codex CLI, Claude Code, Copilot, Gemini-family tools, Cursor, or other coding agents.
- It is not an IDE plugin or universal agent runtime.
- It is not a hosted CI/CD service.
- It is not a requirement that every change has formal proof.
- It is not a claim that green CI alone proves high assurance.
- It is not a guarantee beyond the stated claim, evidence scope, assumptions, waivers, and runtime controls.

### 3. Required policy decisions

| Decision | Policy |
| --- | --- |
| Producer boundary | Codex, Claude Code, Copilot, Gemini-family tools, other coding agents, human maintainers, test runners, formal tools, conformance tools, and MCP servers are replaceable producers. |
| Control-plane ownership | ae-framework owns judgment-side contracts, evidence normalization, policy evaluation, and PR/release assurance summaries. |
| Risk-based verification | Heavy verification is conditional and risk-based, not universal. |
| Claim-based assurance | Assurance is evaluated per claim, not by repository-wide green status alone. |
| Claim status escalation | Ordinary unresolved claims may stay report-only, but `risk:high`, `enforce-assurance`, and critical core policy can escalate missing required lanes to block or manual approval. |
| Summary-first evidence | Summary artifacts are primary judgment inputs; raw logs are supporting evidence. |
| Distinct state layers | `claim-evidence-manifest/v1.claims[].status` remains `partial`, `satisfied`, `waived`, and `unresolved`, with evidence kind carried separately in `evidenceRefs[].kind`. Preview projection and packaging surfaces may summarize outcomes such as `proved`, `model-checked`, `tested`, `runtime-mitigated`, `failed`, and `not-applicable`, but they must not redefine the manifest claim-status vocabulary without explicit schema and policy migration. |
| Human override | Human override requires `owner`, `reason`, `expires`, `relatedClaimIds`, `evidenceRefs`, and `sourceArtifactId` provenance. |
| Contract evolution | Contract changes use compatibility windows, dual-write/dual-validate behavior, or explicit migration notes. |
| Enforcement default | New assurance evaluation should start report-only unless an explicit policy, label, or risk profile selects enforcement. |
| Policy-gate assurance findings | Producer or assurance-summary findings may be copied into `policy-gate-summary/v1` with count, severity, and source artifact path, but the default handling is report-only and does not block ordinary PRs. |

Escalation is policy-scoped, not producer-scoped. `policy/risk-policy.yml`
defines `assurance_escalation` so the same finding has a predictable outcome:
ordinary PRs keep missing evidence and agent findings report-only; `risk:high`
requires manual approval, policy-label convergence, and a plan artifact;
`enforce-assurance` blocks strict assurance failures; critical-core boundaries or
explicit assurance profiles can choose manual approval or blocking for their
declared required lanes. A waiver must retain `owner`, `reason`, `expires`,
`relatedClaimIds`, `evidenceRefs`, and `sourceArtifactId` provenance; it does not convert an unsupported claim into
`proved`, `tested`, or `satisfied`.

### 4. Canonical terminology

| Term | Meaning | Current references |
| --- | --- | --- |
| Producer agent | Agent or tool that creates code, specs, tests, verification output, or review artifacts. Producers include Codex, Claude Code, Copilot, Gemini-family tools, MCP tools, test runners, formal tools, human maintainers, and security producers. | `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`, `docs/integrations/CODEX-INTEGRATION.md` |
| Control plane | Layer that normalizes producer outputs into schema-backed evidence and policy decisions. | `docs/product/ASSURANCE-CONTROL-PLANE.md` |
| Policy plane | Policy-gate, risk labels, review topology, approvals, enforcement profiles, and release/post-deploy rules. | `docs/ci/OPT-IN-CONTROLS.md`, `docs/ci/pr-automation.md`, `.github/workflows/policy-gate.yml` |
| Evidence plane | Schemas, fixtures, generated JSON/Markdown summaries, and contract validation. | `docs/quality/ARTIFACTS-CONTRACT.md`, `docs/reference/CONTRACT-CATALOG.md` |
| Claim | Business, safety, security, or design statement that needs support from evidence. | `docs/quality/ASSURANCE-MODEL.md`, `schema/claim-evidence-manifest.schema.json` |
| Assurance level | Weight of evidence per claim, from `A0` through `A4`. | `docs/quality/ASSURANCE-MODEL.md`, `schema/assurance-profile.schema.json` |
| Validation lane | Independent verification route such as `spec`, `behavior`, `adversarial`, `model`, `proof`, or `runtime`. | `docs/quality/assurance-lanes.md` |
| Runtime control | Operational mitigation such as alert, feature flag, rollout guard, or runtime conformance monitor. It is not proof. | `docs/quality/ASSURANCE-MODEL.md` |
| Waiver / override | Time-bounded exception with `owner`, `reason`, `expires`, `relatedClaimIds`, `evidenceRefs`, and `sourceArtifactId` provenance. It does not turn an unsupported claim into a satisfied claim. | `schema/claim-evidence-manifest.schema.json`, `schema/change-package-v2.schema.json`, `schema/policy-decision-v1.schema.json` |
| Unresolved risk | Claim or finding whose evidence is missing, failed, stale, out of scope, or not strong enough for the target assurance level. | `docs/quality/assurance-profile.md`, `docs/security/security-assurance-lane.md` |
| Proof-carrying change package | Review/release package that links changed claims, evidence, assumptions, waivers, runtime controls, residual risks, and policy decisions. | `docs/reference/change-package-v2.md`, `schema/change-package-v2.schema.json` |

### 5. Evidence-state policy

A PR/release review state must not be upgraded beyond the supporting evidence. When writing `claim-evidence-manifest/v1`, use the manifest claim-status vocabulary and linked evidence refs instead of inventing new manifest enum values.

| State | Meaning | Not equivalent to |
| --- | --- | --- |
| `proved` | Machine-checked proof or equivalent proof-level evidence is linked and scoped. | A passing unit test. |
| `model-checked` | Model checking or counterexample exploration supports the modeled scope. | Proof for code outside the model. |
| `tested` | Unit, integration, property, MBT, or similar behavior evidence exists. | Formal proof. |
| `runtime-mitigated` | Runtime control reduces operational risk. | Proof or model checking. |
| `waived` | An owner accepted a time-bounded exception with `evidenceRefs` and `sourceArtifactId` provenance. | Satisfied claim. |
| `unresolved` | Required evidence is absent, stale, failed, insufficient, or intentionally out of current primary-contract scope. | Passing build. |
| `not-applicable` | Preview claim-level summary projection or `change-package/v2` package/release outcome for an explicitly out-of-scope/non-applicable claim. | A current `claim-evidence-manifest/v1.claims[].status` value or evidence kind. |

### 6. State-layer separation

These state vocabularies are intentionally separate:

1. **Primary manifest claim status**: `claim-evidence-manifest/v1.claims[].status` and current primary claim/evidence producers remain bounded to `partial`, `satisfied`, `waived`, and `unresolved`; evidence strength is carried by evidence refs, achieved levels, and summaries rather than by adding manifest status values.
2. **Claim-level summary projection states**: preview `claim-level-summary/v1` may report projection states such as `satisfied`, `failed`, and `not-applicable` for PR/release review, but those projection states do not become source manifest states.
3. **Change-package v2 packaging / release-decision states**: `change-package/v2.claims[].status` may preserve package-level outcomes such as `satisfied`, `failed`, and `not-applicable` when summarizing a review or release package. Those states must not be projected back into `claim-evidence-manifest/v1` or agent PR metric state without an explicit schema and policy migration.
4. **Metric-level denominator state**: `agentPrAssurance.metrics.required_lane_compliance.notApplicable` means there are no required lanes in the metric denominator. It is not a claim-level assurance state.

### 7. Valid and invalid wording examples

| Intent | Valid wording | Invalid wording |
| --- | --- | --- |
| Green CI | `verify-lite`, `policy-gate`, and `gate` passed for this PR. | This PR is high assurance because CI is green. |
| Claim evidence | Claim `no-negative-balance` is tested by unit and property lanes and remains below target `A3` until model evidence is available. | The balance invariant is proved by tests. |
| Runtime control | The rollout guard mitigates risk during deployment; the claim remains runtime-mitigated, not proved. | The alert proves the system is safe. |
| Waiver | Claim `audit-fields` is waived until 2026-06-30 by owner `security`, with `evidenceRefs`, `sourceArtifactId`, and follow-up issue. | The waived claim passes. |
| Formal scope | TLA evidence model-checks the state transition model under the assumptions listed in the summary. | Formal verification proves the whole product. |
| Producer boundary | Codex generated a change and ae-framework produced evidence for review. | ae-framework is the coding agent. |
| Change package | `change-package/v2` is a proof-carrying preview package linked to claim evidence and policy decisions. | v2 is the mandatory production package for every PR. |

### 8. Implementation guidance for Codex-driven work

For issues that touch assurance behavior:

1. Inspect current HEAD and current contracts before editing.
2. Prefer updating canonical docs or schemas over creating parallel concepts.
3. Keep producer-agent behavior separate from control-plane judgment behavior.
4. Add report-only behavior before enforcement unless the issue explicitly requires fail-closed semantics.
5. Preserve v1 compatibility or document migration when changing a consumed contract.
6. Add positive and negative fixtures when adding or tightening schemas.
7. Use summary artifacts for PR/release judgment and keep raw logs as supporting evidence.
8. Record residual risk when evidence is missing, waived, runtime-mitigated, or out of scope.

### 9. Contract change policy

Contract changes are safe when they follow at least one of these routes:

- Backward-compatible optional fields with tests and schema validation.
- Preview contract name or version with explicit docs.
- Dual-write and dual-validate period.
- Migration notes that identify producer, consumer, artifact path, and rollback plan.
- Policy-gate report-only period before enforcement.

Breaking changes require explicit migration notes in the relevant contract docs and PR summary.

### 10. Agent PR metrics policy

Agent PR assurance metrics are observability signals. They can be shown in quality scorecards, PR comments, release summaries, or `agentic-metrics` extensions, but their initial state is report-only.

Policy gates may consume these metrics for context, but a metric must not become a new block condition without an explicit policy change tied to risk labels, assurance profiles, or high-assurance critical core scope.

`agentPrAssurance.metrics.required_lane_compliance.notApplicable` is a metric-level denominator state for "no required lanes." It is not a claim-level `not-applicable` assurance state and does not authorize producers to emit new `claim-evidence-manifest/v1` claim-status values.

### 11. References

- Product overview: `docs/product/ASSURANCE-CONTROL-PLANE.md`
- Agent-neutral assurance roadmap: `docs/product/AGENT-NEUTRAL-ASSURANCE-ROADMAP.md`
- Assurance model: `docs/quality/ASSURANCE-MODEL.md`
- Current system overview: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- Detailed design: `docs/architecture/ASSURANCE-CONTROL-PLANE-DETAILED-DESIGN.md`
- Artifacts contract: `docs/quality/ARTIFACTS-CONTRACT.md`
- Contract catalog: `docs/reference/CONTRACT-CATALOG.md`
- Evidence adapters: `docs/agents/evidence-adapters.md`
- Change package v2: `docs/reference/change-package-v2.md`
- Codex integration: `docs/integrations/CODEX-INTEGRATION.md`
- Security Assurance Lane: `docs/security/security-assurance-lane.md`
- Agent PR assurance metrics: `docs/ci/agent-pr-assurance-metrics.md`
- Current-state audit: `docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md`

---

## 日本語

### 1. 目的

この文書は、ae-framework をエージェント協調型SDLCのための agent-neutral assurance control plane として扱うための canonical policy です。今後の Codex-driven work が agent harness を作る方向へ逸れず、判断側の契約・証跡・policy・PR/release assurance を強化するための判断基準を固定します。Product thesis は `Bring your own agent. Keep your assurance plane.` です。

### 2. 境界

#### 2.1 ae-framework が担うもの

- BYO-agent 前提の、エージェント非依存な assurance control plane。
- 仕様、検証出力、証跡 artifact、policy decision、PR/release summary、post-deploy assurance の判断側契約。
- claim と risk に応じて重い検証を選択する運用モデル。
- producer output を長期的に比較・レビュー可能にする contract catalog と artifact validation surface。

#### 2.2 ae-framework が担わないもの

- Codex CLI、Claude Code、Copilot、Gemini系tool、Cursor などの coding agent の代替。
- IDE plugin または汎用 agent runtime。
- ホスト型CI/CDサービス。
- すべての変更への formal proof 強制。
- green CI だけを根拠にした high assurance の宣言。
- claim、証跡範囲、assumption、waiver、runtime control を超えた保証。

### 3. 必須 policy decision

| Decision | Policy |
| --- | --- |
| Producer boundary | Codex、Claude Code、Copilot、Gemini系tool、その他coding agent、人間のmaintainer、test runner、formal tool、conformance tool、MCP server は交換可能な producer として扱う。 |
| Control-plane ownership | ae-framework は判断側 contract、evidence normalization、policy evaluation、PR/release assurance summary を担う。 |
| Risk-based verification | 重い検証は条件付き・risk-based であり、常時強制しない。 |
| Claim-based assurance | assurance は claim 単位で評価し、repository 全体の green status だけでは判断しない。 |
| Claim status escalation | 通常変更の unresolved claim は report-only に留める場合があるが、`risk:high`、`enforce-assurance`、critical core policy では required lane 不足を block または manual approval へ昇格できる。 |
| Summary-first evidence | summary artifact を主な判断入力とし、raw log は補助証跡とする。 |
| Distinct state layers | `claim-evidence-manifest/v1.claims[].status` は `partial`、`satisfied`、`waived`、`unresolved` に限定し、evidence kind は `evidenceRefs[].kind` に分離して保持する。preview projection や packaging surface は `proved`、`model-checked`、`tested`、`runtime-mitigated`、`failed`、`not-applicable` などの outcome を要約できるが、明示的な schema / policy migration なしに manifest claim-status vocabulary を再定義しない。 |
| Human override | human override には `owner`、`reason`、`expires`、`relatedClaimIds`、`evidenceRefs`、`sourceArtifactId` provenance を必要とする。 |
| Contract evolution | contract 変更には compatibility window、dual-write/dual-validate、または migration note を使う。 |
| Enforcement default | 新しい assurance evaluation は、明示的な policy / label / risk profile が enforcement を選択しない限り report-only から開始する。 |
| Policy-gate assurance findings | producer または assurance summary 由来の finding は `policy-gate-summary/v1` に count、severity、source artifact path 付きで転記できるが、既定は report-only であり通常PRをblockしない。 |

Escalation は producer ではなく policy で決まります。
`policy/risk-policy.yml` の `assurance_escalation` は、同じ finding に対して
予測可能な結果を定義します。通常 PR では evidence 不足や agent finding は
report-only に留めます。`risk:high` では manual approval、policy label の収束、
plan artifact を要求します。`enforce-assurance` では strict assurance failure を
block します。critical-core boundary または明示的 assurance profile は、宣言された
required lane について manual approval または blocking を選択できます。waiver は
`owner`、`reason`、`expires`、`relatedClaimIds`、`evidenceRefs`、`sourceArtifactId` provenance を保持する必要があり、
unsupported claim を `proved`、`tested`、`satisfied` に変換しません。

### 4. 用語

- **Producer agent**: code、spec、test、verification output、review artifact を生成する agent/tool。Codex、Claude Code、Copilot、Gemini系tool、MCP tool、人間、test runner、formal tool を含む。
- **Control plane**: producer output を schema-backed evidence と policy decision に正規化する層。
- **Policy plane**: policy-gate、risk label、review topology、approval、enforcement profile、release/post-deploy rule。
- **Evidence plane**: schema、fixture、生成された JSON/Markdown summary、contract validation。
- **Claim**: business / safety / security / design 上、証跡で支えるべき主張。
- **Assurance level**: claim 単位の証跡の重さ。`A0` から `A4`。
- **Validation lane**: `spec`、`behavior`、`adversarial`、`model`、`proof`、`runtime` などの独立検証経路。
- **Runtime control**: alert、feature flag、rollout guard、runtime conformance monitor などの運用時緩和。proof ではない。
- **Waiver / override**: `owner`、`reason`、`expires`、`relatedClaimIds`、`evidenceRefs`、`sourceArtifactId` provenance を持つ期限付き例外。satisfied claim ではない。
- **Unresolved risk**: 証跡が不足、失敗、古い、対象外、または target assurance level に足りない claim / finding。
- **Proof-carrying change package**: changed claim、evidence、assumption、waiver、runtime control、residual risk、policy decision を結び付ける review/release package。

### 5. Claim status policy

Claim status は claim 単位で評価し、PR / release summary では状態を混同しません。

| Status | 意味 | Policy handling |
| --- | --- | --- |
| `proved` | proof lane の machine-checked evidence が scope 付きで紐付く | supported として扱えるが assumption / scope を隠さない |
| `model-checked` | model checking が bounded scope / assumption の範囲で探索済み | model scope を超える claim は human review へ昇格 |
| `tested` | unit / integration / property / conformance などで検証済み | behavior evidence。proof と表現しない |
| `runtime-mitigated` | runtime guard / feature flag / alert などで緩和済み | warn / report-only が既定。critical core では manual approval または block へ昇格可能 |
| `waived` | `owner` / `reason` / `expires` / `relatedClaimIds` / `evidenceRefs` / `sourceArtifactId` 付きで期限付き免除 | metadata 不足・期限切れは block。satisfied claim ではない |
| `unresolved` | evidence 不足または未判断 | 通常変更では report-only 可。ただし `risk:high` / `enforce-assurance` / critical core では block または manual approval |
| `not-applicable` | 明示的に scope 外 / 非対象である claim の preview claim-level summary projection、または `change-package/v2` package / release outcome | 現行 `claim-evidence-manifest/v1.claims[].status` value や evidence kind ではない |

### 6. state layer の分離

次の state vocabulary は意図的に分離します。

1. **Primary manifest claim status**: `claim-evidence-manifest/v1.claims[].status` と現行 primary claim/evidence producer は `partial`、`satisfied`、`waived`、`unresolved` に限定します。evidence strength は、新しい manifest status value ではなく、evidence refs、achieved level、summary で表現します。
2. **Claim-level summary projection state**: preview `claim-level-summary/v1` は PR / release review 向けに `satisfied`、`failed`、`not-applicable` などの projection state を表示できますが、source manifest state にはしません。
3. **Change-package v2 packaging / release-decision state**: `change-package/v2.claims[].status` は review / release package の要約として `satisfied`、`failed`、`not-applicable` などの package-level outcome を保持できます。これらを `claim-evidence-manifest/v1` や agent PR metric state に戻すには、明示的な schema / policy migration が必要です。
4. **Metric-level denominator state**: `agentPrAssurance.metrics.required_lane_compliance.notApplicable` は metric denominator に required lane がないことを表します。claim-level assurance state ではありません。

### 7. 有効/無効な表現例

| Intent | 有効な表現 | 無効な表現 |
| --- | --- | --- |
| Green CI | `verify-lite`、`policy-gate`、`gate` がこの PR で通過した。 | CI が green なので high assurance である。 |
| Claim evidence | claim `no-negative-balance` は unit/property lane で tested。model evidence までは target `A3` 未満。 | テストにより balance invariant は proved である。 |
| Runtime control | rollout guard は deployment risk を緩和するが、claim は runtime-mitigated であり proved ではない。 | alert があるので安全性は証明済み。 |
| Waiver | claim `audit-fields` は owner、期限、`evidenceRefs`、`sourceArtifactId`、follow-up issue 付きで waived。 | waived claim は pass。 |
| Formal scope | TLA evidence は summary に記載された assumption の範囲で state transition model を model-check した。 | formal verification により製品全体が証明済み。 |
| Producer boundary | Codex が変更を生成し、ae-framework が review evidence を生成した。 | ae-framework は coding agent である。 |

### 8. Codex-driven work への指針

1. 編集前に current HEAD と current contracts を確認する。
2. 並列概念を増やす前に canonical docs / schemas を更新する。
3. producer agent の機能と control-plane judgment の機能を分離する。
4. 明示的な fail-closed 要件がない限り、enforcement より先に report-only を追加する。
5. 既存 contract を変更する場合は v1 compatibility または migration note を残す。
6. schema を追加・厳格化する場合は positive / negative fixture を追加する。
7. PR/release の判断には summary artifact を使い、raw log は補助証跡とする。
8. evidence が missing、waived、runtime-mitigated、out-of-scope の場合は、現行 contract では `unresolved` または waiver として residual risk を記録する。

### 9. Agent PR metrics policy

Agent PR assurance metrics は observability signal です。quality scorecard、PR comment、release summary、または `agentic-metrics` extension に表示できますが、初期状態は report-only です。

Policy gate は文脈情報としてこれらのmetricsを参照できます。ただし、risk label、assurance profile、high-assurance critical core scope に結びついた明示的なpolicy変更がない限り、新しいblock条件にはしません。

`agentPrAssurance.metrics.required_lane_compliance.notApplicable` は「required lane がない」ことを表す metric-level denominator state です。claim-level の `not-applicable` assurance state ではなく、producer に新しい `claim-evidence-manifest/v1` claim-status value の emit を許可するものではありません。
