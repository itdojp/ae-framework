---
docRole: ssot
lastVerified: '2026-05-08'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency
---

# Assurance Control Plane Policy

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This policy is the canonical product decision record for ae-framework as an assurance control plane. It is written for human maintainers and Codex-driven work so that future implementation issues strengthen judgment-side assurance instead of rebuilding a coding-agent harness.

Use this document with:

- `docs/product/ASSURANCE-CONTROL-PLANE.md` for the product overview.
- `docs/quality/ASSURANCE-MODEL.md` for claim, assurance level, validation lane, evidence, assumption, waiver, and runtime-control terminology.
- `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md` for implementation-aligned architecture.
- `docs/reference/CONTRACT-CATALOG.md` for current schema, producer, and consumer mappings.
- `docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md` for the 2026-05 current-state audit.

### 2. Product boundary

#### 2.1 What ae-framework is

- A BYO-agent assurance control plane.
- A judgment-side contract layer for specifications, verification outputs, evidence artifacts, policy decisions, PR summaries, release summaries, and post-deploy assurance.
- A risk-based operating model that can add heavier verification only when a claim, risk profile, or policy requires it.
- A contract catalog and artifact validation surface that keeps producer outputs reviewable and comparable over time.

#### 2.2 What ae-framework is not

- It is not a replacement for Codex CLI, Claude Code, Copilot, Cursor, or other coding agents.
- It is not an IDE plugin or universal agent runtime.
- It is not a requirement that every change has formal proof.
- It is not a claim that green CI alone proves high assurance.
- It is not a guarantee beyond the stated claim, evidence scope, assumptions, waivers, and runtime controls.

### 3. Required policy decisions

| Decision | Policy |
| --- | --- |
| Producer boundary | Coding agents, test runners, formal tools, conformance tools, and MCP servers are replaceable producers. |
| Control-plane ownership | ae-framework owns judgment-side contracts, evidence normalization, policy evaluation, and PR/release assurance summaries. |
| Risk-based verification | Heavy verification is conditional and risk-based, not universal. |
| Claim-based assurance | Assurance is evaluated per claim, not by repository-wide green status alone. |
| Summary-first evidence | Summary artifacts are primary judgment inputs; raw logs are supporting evidence. |
| Distinct evidence states | `proved`, `model-checked`, `tested`, `runtime-mitigated`, `waived`, `unresolved`, and `not-applicable` are distinct states. |
| Human override | Human override requires owner, reason, expiry, related claim IDs, and evidence link. |
| Contract evolution | Contract changes use compatibility windows, dual-write/dual-validate behavior, or explicit migration notes. |
| Enforcement default | New assurance evaluation should start report-only unless an explicit policy, label, or risk profile selects enforcement. |

### 4. Canonical terminology

| Term | Meaning | Current references |
| --- | --- | --- |
| Producer agent | Agent or tool that creates code, specs, tests, verification output, or review artifacts. Producers include Codex, Claude, Copilot, MCP tools, test runners, formal tools, and security producers. | `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`, `docs/integrations/CODEX-INTEGRATION.md` |
| Control plane | Layer that normalizes producer outputs into schema-backed evidence and policy decisions. | `docs/product/ASSURANCE-CONTROL-PLANE.md` |
| Policy plane | Policy-gate, risk labels, review topology, approvals, enforcement profiles, and release/post-deploy rules. | `docs/ci/OPT-IN-CONTROLS.md`, `docs/ci/pr-automation.md`, `.github/workflows/policy-gate.yml` |
| Evidence plane | Schemas, fixtures, generated JSON/Markdown summaries, and contract validation. | `docs/quality/ARTIFACTS-CONTRACT.md`, `docs/reference/CONTRACT-CATALOG.md` |
| Claim | Business, safety, security, or design statement that needs support from evidence. | `docs/quality/ASSURANCE-MODEL.md`, `schema/claim-evidence-manifest.schema.json` |
| Assurance level | Weight of evidence per claim, from `A0` through `A4`. | `docs/quality/ASSURANCE-MODEL.md`, `schema/assurance-profile.schema.json` |
| Validation lane | Independent verification route such as `spec`, `behavior`, `adversarial`, `model`, `proof`, or `runtime`. | `docs/quality/assurance-lanes.md` |
| Runtime control | Operational mitigation such as alert, feature flag, rollout guard, or runtime conformance monitor. It is not proof. | `docs/quality/ASSURANCE-MODEL.md` |
| Waiver / override | Time-bounded exception with owner, reason, expiry, claim links, and evidence reference. It does not turn an unsupported claim into a satisfied claim. | `schema/claim-evidence-manifest.schema.json`, `schema/change-package-v2.schema.json`, `schema/policy-decision-v1.schema.json` |
| Unresolved risk | Claim or finding whose evidence is missing, failed, stale, out of scope, or not strong enough for the target assurance level. | `docs/quality/assurance-profile.md`, `docs/security/security-assurance-lane.md` |
| Proof-carrying change package | Review/release package that links changed claims, evidence, assumptions, waivers, runtime controls, residual risks, and policy decisions. | `docs/reference/change-package-v2.md`, `schema/change-package-v2.schema.json` |

### 5. Evidence-state policy

A claim state must not be upgraded beyond the supporting evidence.

| State | Meaning | Not equivalent to |
| --- | --- | --- |
| `proved` | Machine-checked proof or equivalent proof-level evidence is linked and scoped. | A passing unit test. |
| `model-checked` | Model checking or counterexample exploration supports the modeled scope. | Proof for code outside the model. |
| `tested` | Unit, integration, property, MBT, or similar behavior evidence exists. | Formal proof. |
| `runtime-mitigated` | Runtime control reduces operational risk. | Proof or model checking. |
| `waived` | An owner accepted a time-bounded exception with evidence link. | Satisfied claim. |
| `unresolved` | Required evidence is absent, stale, failed, or insufficient. | Passing build. |
| `not-applicable` | Claim does not apply and the reason is recorded. | Missing evidence. |

### 6. Valid and invalid wording examples

| Intent | Valid wording | Invalid wording |
| --- | --- | --- |
| Green CI | `verify-lite`, `policy-gate`, and `gate` passed for this PR. | This PR is high assurance because CI is green. |
| Claim evidence | Claim `no-negative-balance` is tested by unit and property lanes and remains below target `A3` until model evidence is available. | The balance invariant is proved by tests. |
| Runtime control | The rollout guard mitigates risk during deployment; the claim remains runtime-mitigated, not proved. | The alert proves the system is safe. |
| Waiver | Claim `audit-fields` is waived until 2026-06-30 by owner `security`, with evidence link and follow-up issue. | The waived claim passes. |
| Formal scope | TLA evidence model-checks the state transition model under the assumptions listed in the summary. | Formal verification proves the whole product. |
| Producer boundary | Codex generated a change and ae-framework produced evidence for review. | ae-framework is the coding agent. |
| Change package | `change-package/v2` is a proof-carrying preview package linked to claim evidence and policy decisions. | v2 is the mandatory production package for every PR. |

### 7. Implementation guidance for Codex-driven work

For issues that touch assurance behavior:

1. Inspect current HEAD and current contracts before editing.
2. Prefer updating canonical docs or schemas over creating parallel concepts.
3. Keep producer-agent behavior separate from control-plane judgment behavior.
4. Add report-only behavior before enforcement unless the issue explicitly requires fail-closed semantics.
5. Preserve v1 compatibility or document migration when changing a consumed contract.
6. Add positive and negative fixtures when adding or tightening schemas.
7. Use summary artifacts for PR/release judgment and keep raw logs as supporting evidence.
8. Record residual risk when evidence is missing, waived, runtime-mitigated, or out of scope.

### 8. Contract change policy

Contract changes are safe when they follow at least one of these routes:

- Backward-compatible optional fields with tests and schema validation.
- Preview contract name or version with explicit docs.
- Dual-write and dual-validate period.
- Migration notes that identify producer, consumer, artifact path, and rollback plan.
- Policy-gate report-only period before enforcement.

Breaking changes require explicit migration notes in the relevant contract docs and PR summary.

### 9. References

- Product overview: `docs/product/ASSURANCE-CONTROL-PLANE.md`
- Assurance model: `docs/quality/ASSURANCE-MODEL.md`
- Current system overview: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- Artifacts contract: `docs/quality/ARTIFACTS-CONTRACT.md`
- Contract catalog: `docs/reference/CONTRACT-CATALOG.md`
- Change package v2: `docs/reference/change-package-v2.md`
- Codex integration: `docs/integrations/CODEX-INTEGRATION.md`
- Security Assurance Lane: `docs/security/security-assurance-lane.md`
- Current-state audit: `docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md`

---

## 日本語

### 1. 目的

この文書は、ae-framework を assurance control plane として扱うための canonical policy です。今後の Codex-driven work が agent harness を作る方向へ逸れず、判断側の契約・証跡・policy・PR/release assurance を強化するための判断基準を固定します。

### 2. 境界

#### 2.1 ae-framework が担うもの

- BYO-agent 前提の assurance control plane。
- 仕様、検証出力、証跡 artifact、policy decision、PR/release summary、post-deploy assurance の判断側契約。
- claim と risk に応じて重い検証を選択する運用モデル。
- producer output を長期的に比較・レビュー可能にする contract catalog と artifact validation surface。

#### 2.2 ae-framework が担わないもの

- Codex CLI、Claude Code、Copilot、Cursor などの coding agent の代替。
- IDE plugin または汎用 agent runtime。
- すべての変更への formal proof 強制。
- green CI だけを根拠にした high assurance の宣言。
- claim、証跡範囲、assumption、waiver、runtime control を超えた保証。

### 3. 必須 policy decision

| Decision | Policy |
| --- | --- |
| Producer boundary | coding agent、test runner、formal tool、conformance tool、MCP server は交換可能な producer として扱う。 |
| Control-plane ownership | ae-framework は判断側 contract、evidence normalization、policy evaluation、PR/release assurance summary を担う。 |
| Risk-based verification | 重い検証は条件付き・risk-based であり、常時強制しない。 |
| Claim-based assurance | assurance は claim 単位で評価し、repository 全体の green status だけでは判断しない。 |
| Summary-first evidence | summary artifact を主な判断入力とし、raw log は補助証跡とする。 |
| Distinct evidence states | `proved`、`model-checked`、`tested`、`runtime-mitigated`、`waived`、`unresolved`、`not-applicable` を混同しない。 |
| Human override | human override には owner、reason、expiry、related claim IDs、evidence link を必要とする。 |
| Contract evolution | contract 変更には compatibility window、dual-write/dual-validate、または migration note を使う。 |
| Enforcement default | 新しい assurance evaluation は、明示的な policy / label / risk profile が enforcement を選択しない限り report-only から開始する。 |

### 4. 用語

- **Producer agent**: code、spec、test、verification output、review artifact を生成する agent/tool。
- **Control plane**: producer output を schema-backed evidence と policy decision に正規化する層。
- **Policy plane**: policy-gate、risk label、review topology、approval、enforcement profile、release/post-deploy rule。
- **Evidence plane**: schema、fixture、生成された JSON/Markdown summary、contract validation。
- **Claim**: business / safety / security / design 上、証跡で支えるべき主張。
- **Assurance level**: claim 単位の証跡の重さ。`A0` から `A4`。
- **Validation lane**: `spec`、`behavior`、`adversarial`、`model`、`proof`、`runtime` などの独立検証経路。
- **Runtime control**: alert、feature flag、rollout guard、runtime conformance monitor などの運用時緩和。proof ではない。
- **Waiver / override**: owner、reason、expiry、claim link、evidence link を持つ期限付き例外。satisfied claim ではない。
- **Unresolved risk**: 証跡が不足、失敗、古い、対象外、または target assurance level に足りない claim / finding。
- **Proof-carrying change package**: changed claim、evidence、assumption、waiver、runtime control、residual risk、policy decision を結び付ける review/release package。

### 5. 有効/無効な表現例

| Intent | 有効な表現 | 無効な表現 |
| --- | --- | --- |
| Green CI | `verify-lite`、`policy-gate`、`gate` がこの PR で通過した。 | CI が green なので high assurance である。 |
| Claim evidence | claim `no-negative-balance` は unit/property lane で tested。model evidence までは target `A3` 未満。 | テストにより balance invariant は proved である。 |
| Runtime control | rollout guard は deployment risk を緩和するが、claim は runtime-mitigated であり proved ではない。 | alert があるので安全性は証明済み。 |
| Waiver | claim `audit-fields` は owner、期限、evidence link、follow-up issue 付きで waived。 | waived claim は pass。 |
| Formal scope | TLA evidence は summary に記載された assumption の範囲で state transition model を model-check した。 | formal verification により製品全体が証明済み。 |
| Producer boundary | Codex が変更を生成し、ae-framework が review evidence を生成した。 | ae-framework は coding agent である。 |

### 6. Codex-driven work への指針

1. 編集前に current HEAD と current contracts を確認する。
2. 並列概念を増やす前に canonical docs / schemas を更新する。
3. producer agent の機能と control-plane judgment の機能を分離する。
4. 明示的な fail-closed 要件がない限り、enforcement より先に report-only を追加する。
5. 既存 contract を変更する場合は v1 compatibility または migration note を残す。
6. schema を追加・厳格化する場合は positive / negative fixture を追加する。
7. PR/release の判断には summary artifact を使い、raw log は補助証跡とする。
8. evidence が missing、waived、runtime-mitigated、out-of-scope の場合は residual risk として記録する。
