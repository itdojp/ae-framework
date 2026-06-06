---
docRole: ssot
lastVerified: '2026-06-06'
owner: architecture-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# Assurance Control Plane Detailed Design

> Language / 言語: English | 日本語要約

---

## English

### 1. Purpose and scope

This document is the implementation-oriented detailed design for the ae-framework assurance control plane. It translates the product policy in `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` into concrete claim, evidence, achieved-level, waiver, policy-gate, and change-package contracts that can be implemented against current repository artifacts.

Use this design with:

- `docs/product/ASSURANCE-CONTROL-PLANE.md` for product positioning.
- `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` for policy decisions and terminology.
- `docs/quality/ASSURANCE-MODEL.md` for the base claim/level/lane vocabulary.
- `docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md` for the current-state inventory.
- `docs/reference/CONTRACT-CATALOG.md` and `docs/reference/change-package-v2.md` for schema and package references.

Baseline assumptions (as of `lastVerified: 2026-06-06`):

- Node.js engine: `>=20.11 <23` from `package.json`.
- pnpm package manager: `pnpm@10.0.0` from `package.json`.
- Primary CI platform: GitHub Actions under `.github/workflows/`.
- Canonical current claim manifest: `schema/claim-evidence-manifest.schema.json` with `schemaVersion: claim-evidence-manifest/v1`.
- Canonical current lane summary: `schema/assurance-summary.schema.json` with `schemaVersion: assurance-summary/v1`.
- Canonical current policy-gate summary: `schema/policy-gate-summary-v1.schema.json` with `schemaVersion: policy-gate-summary/v1`.
- Canonical current proof-carrying package preview: `schema/change-package-v2.schema.json` with `schemaVersion: change-package/v2`.
- Preview per-claim PR/release projection: `schema/claim-level-summary-v1.schema.json` with `schemaVersion: claim-level-summary/v1`.
- Preview temporary override record: `schema/temporary-override-v1.schema.json` with `schemaVersion: temporary-override/v1`.

### 2. Design goals and non-goals

#### 2.1 Goals

- Evaluate assurance per claim, not from repository-wide green status alone.
- Keep evidence states distinct from policy-gate results and from human waivers.
- Compute achieved assurance levels conservatively from available evidence.
- Make missing, failed, stale, waived, runtime-mitigated, and out-of-scope evidence explicit.
- Preserve backward compatibility for current v1 contracts while allowing preview/dual-write evolution.
- Provide enough detail for the follow-up schema, aggregator, policy-gate, change-package, integration, fixture, and cleanup issues.

#### 2.2 Non-goals

- This design does not require formal proof for every change.
- This design does not replace Codex, Claude Code, Copilot, Cursor, or other producer agents.
- This design does not introduce `not-applicable` as a current `claim-evidence-manifest/v1` claim status or evidence kind. `change-package/v2` may preserve `not-applicable` as a package/release outcome state, and `claim-level-summary/v1` may project it for PR/release review, but neither surface redefines the manifest claim-status vocabulary without explicit migration.
- This design does not make `change-package/v2` mandatory for all PRs in this slice; v2 remains a preview/dual-write path until policy selects enforcement.

### 3. Component responsibilities and I/O

| Component | Responsibility | Primary inputs | Primary outputs | Current implementation evidence |
| --- | --- | --- | --- | --- |
| Assurance profile producer | Declare target claims, required lanes, evidence kinds, criticality, and independent-source requirements. | `fixtures/assurance/sample.assurance-profile.json`, profile docs. | Profile JSON validated by `schema/assurance-profile.schema.json`. | `docs/quality/assurance-profile.md`, `tests/contracts/assurance-profile-contract.test.ts`. |
| Lane producers | Produce summary-grade evidence from spec, behavior, adversarial, model, proof, and runtime lanes. | Context Pack, Verify Lite, formal, conformance, quality, security, and trace artifacts. | Lane summaries, formal summaries, conformance results, quality scorecards, security artifacts. | `verify:lite`, `verify:assurance`, `formal:*`, `conformance:*`, `quality:scorecard:v1`, `security:*`. |
| Assurance summary aggregator | Normalize lane coverage per claim. | Assurance profile and lane artifacts. | `artifacts/assurance/assurance-summary.json` (`assurance-summary/v1`). | `scripts/assurance/aggregate-lanes.mjs`, `schema/assurance-summary.schema.json`. |
| Claim-evidence manifest builder | Normalize per-claim evidence, missing evidence, proof obligations, waivers, external IDs, and notes. | `assurance-summary/v1`, trace bundles, Verify Lite, quality scorecard, `change-package/v2`, security artifacts. | `artifacts/assurance/claim-evidence-manifest.json` and Markdown sidecar. | `scripts/assurance/build-claim-evidence-manifest.mjs`, `schema/claim-evidence-manifest.schema.json`. |
| Policy gate | Convert claim-evidence state into PR policy warnings or blocking errors. | PR metadata, risk labels, required checks, review state, claim-evidence manifest. | `policy-gate-summary/v1`, policy input/decision JSON, Markdown summary. | `.github/workflows/policy-gate.yml`, `scripts/ci/policy-gate.mjs`, `schema/policy-gate-summary-v1.schema.json`. |
| Change-package generator | Package intent, scope, risk, evidence, assurance, claims, proof obligations, waivers, runtime controls, and reproducibility. | PR metadata, policy decision, claim-evidence manifest, assurance summary. | `change-package/v1` and preview `change-package/v2` JSON/Markdown. | `scripts/change-package/generate.mjs`, `schema/change-package-v2.schema.json`. |
| PR/release summary renderers | Present summary-grade assurance to maintainers. | Policy-gate summaries, claim-evidence manifest, change package, quality/formal/security summaries. | PR summary and release summary Markdown/JSON. | `docs/quality/pr-summary.md`, `scripts/summary/render-pr-summary.mjs`, change-package Markdown renderer. |
| Producer agents and MCP tools | Generate candidate code, specs, tests, verification, or review artifacts. | Human task context and repository artifacts. | Producer-specific artifacts that enter lane producers or evidence manifests. | Codex/Claude/MCP docs and `src/mcp-server/*`. |

### 4. Data model

#### 4.1 Claim

A claim is the unit of assurance evaluation. Current manifests represent it with:

- `id`: stable claim identifier.
- `statement`: human-readable assertion.
- `criticality`: `low`, `medium`, `high`, or `critical`.
- `targetLevel`: desired assurance level `A0` through `A4`.
- `achievedLevel`: conservative current level `A0` through `A4`.
- `status`: current claim-support status, one of `partial`, `satisfied`, `waived`, or `unresolved` in `claim-evidence-manifest/v1`.
- `evidenceRefs`, `proofObligationRefs`, `missingEvidenceRefs`, `assumptionHandlingRefs`, `waiverRefs`, `externalIds`, and `notes`.

The claim identifier must remain stable across summary, manifest, policy, and package artifacts. Producers may add external identifiers, such as security-claim or security-finding IDs, but those identifiers must not replace the canonical claim ID.

#### 4.2 Requirement reference

A requirement reference links a claim to the upstream source that justifies the claim. Current contracts do not have a dedicated `requirementRef` object in the claim-evidence manifest. The compatible representation is:

- `externalIds[]` for security or external system identifiers.
- `evidenceRefs[].artifactPath` for specification, context-pack, or trace artifact links.
- `sourceArtifacts[]` for artifact-level provenance.
- `change-package/v2.claims[].artifactRefs[]` for package-level references.

A future schema slice may add an explicit requirement-reference field, but it should be additive and should keep these current references readable.

#### 4.3 Assurance level

Assurance levels are ordered: `A0 < A1 < A2 < A3 < A4`.

| Level | Design meaning | Current use |
| --- | --- | --- |
| `A0` | Unassessed or below meaningful evidence threshold. | Default fallback for missing/unknown inputs. |
| `A1` | Basic evidence exists, typically a single low-strength lane. | Low-risk or preliminary claims. |
| `A2` | Multiple routine evidence sources or stronger behavior evidence. | Common target for ordinary PR claims. |
| `A3` | Independent evidence with stronger model/proof/adversarial coverage. | Higher-risk or security-sensitive claims. |
| `A4` | Highest assurance target, requiring explicit proof/model scope and strong independence. | Exceptional critical claims only. |

A claim must not be reported at or above `targetLevel` unless its status is `satisfied` and no required evidence is missing. Waivers and runtime controls do not raise a claim to proof-level assurance.

#### 4.4 Validation lane

The current assurance-summary lanes are:

- `spec`
- `behavior`
- `adversarial`
- `model`
- `proof`
- `runtime`

The claim-evidence manifest maps these lanes to evidence kinds. Unknown lanes or text-derived artifacts fall back to `other` rather than being treated as proof.

#### 4.5 Evidence item and evidence state

An evidence item is a linkable artifact reference that supports, weakens, or qualifies a claim. Current claim-evidence entries use:

- `kind`: `spec`, `behavior`, `adversarial`, `model`, `proof`, `runtime`, `quality`, `trace`, `policy`, `manual`, or `other`.
- `artifactPath`: artifact or artifact pointer.
- `sourceArtifactId`: source artifact provenance.
- `description`: concise evidence description.

Current support outcomes and contract representations are:

| State | Meaning | Current representation |
| --- | --- | --- |
| `proved` | Proof-level evidence is linked and scoped. | `claim-evidence-manifest/v1.claims[].status=satisfied` with proof evidence refs when applicable; `change-package/v2.claims[].status`; proof evidence/proof obligation records. |
| `model-checked` | Model checking supports the modeled scope and assumptions. | Manifest claim status remains `satisfied`/`partial`/`unresolved` based on support; `change-package/v2.claims[].status`; formal/model artifact references. |
| `tested` | Behavior evidence supports the claim. | Manifest claim status remains `satisfied`/`partial`/`unresolved` based on support; `change-package/v2.claims[].status`; behavior/test evidence references. |
| `runtime-mitigated` | Runtime controls reduce operational risk. | Runtime evidence refs plus manifest `partial`/`unresolved` or qualified `satisfied` as policy permits; `change-package/v2.claims[].status`; runtime evidence and `runtimeControls`. |
| `waived` | Human exception exists and is traceable. | `claim-evidence-manifest/v1.claims[].status=waived` plus `waiverRefs`; `change-package/v2.claims[].status=waived`. |
| `unresolved` | Evidence is missing, failed, stale, insufficient, out of scope, or not accepted. | `claim-evidence-manifest/v1.claims[].status=unresolved`/`partial`, `missingEvidenceRefs`, policy result `block` or `report-only`. |

`not-applicable` is intentionally not part of the current `claim-evidence-manifest/v1.claims[].status` or evidence-kind vocabulary. `change-package/v2` can preserve it as an explicit package/release outcome state, and preview `claim-level-summary/v1` can project it for PR/release review and migration testing. Producers must not project that package/projection state back into `claim-evidence-manifest/v1` or agent PR metrics until promotion is explicit.

#### 4.6 Evidence manifest

The claim-evidence manifest is the canonical current per-claim normalization artifact:

- Schema: `schema/claim-evidence-manifest.schema.json`.
- Producer: `pnpm run claim-evidence:generate`.
- Default output: `artifacts/assurance/claim-evidence-manifest.json` plus Markdown sidecar.
- Summary counters: `totalClaims`, `fullySupported`, `partiallySupported`, `waived`, and `unresolved`.

The manifest is the handoff boundary from evidence aggregation to policy and packaging. Downstream consumers must not infer satisfied claims from raw logs when the manifest marks missing evidence or unresolved status.

#### 4.7 Assumption

An assumption is a condition under which evidence is valid. Current representations include:

- `assurance-summary/v1.claims[].assumptionHandling[]` for finding-level handling.
- `claim-evidence-manifest/v1.claims[].assumptionHandlingRefs[]` for normalized references.
- `change-package/v2.assumptions[]` for package-level assumptions.
- Formal summaries and security-assurance outputs for model or threat assumptions.

Assumptions must remain visible in PR/release summaries. A formal or model-checking result is valid only for the stated modeled scope and assumptions.

#### 4.8 Waiver / override

A waiver is a time-bounded human exception. The current compatible representation is `schema/temporary-override-v1.schema.json` for preview override records plus waiver references in claim-evidence, policy, and change-package artifacts. It requires or derives:

- owner
- reason
- expiry date
- related claim IDs
- source evidence link or source artifact ID
- status such as `active`, `expiringSoon`, `expired`, `orphan`, or `unknown`

A waived claim is distinguishable from a satisfied claim. Active waivers can allow report-only or waived policy results, but expired or orphan waivers are blocking in strict assurance mode.

#### 4.9 Runtime control

A runtime control is an operational mitigation such as an alert, feature flag, rollout guard, monitor, or runtime conformance check. It is evidence of operational risk reduction, not proof. Current representations include:

- `runtime` lane/evidence kind in assurance summaries and claim-evidence manifests.
- `change-package/v2.runtimeControls.alerts[]` and `featureFlags[]`.
- `change-package/v2.claims[].status=runtime-mitigated`.

Runtime controls may justify `runtime-mitigated` or residual-risk wording, but they must not be promoted to `proved` or `model-checked`.

#### 4.10 Gate evaluation

A gate evaluation is the policy decision over claims, waivers, PR metadata, review topology, and checks. Current policy-gate assurance fields use:

- `mode`: `report-only` or `strict`.
- `result`: `pass`, `waived`, `report-only`, or `block`.
- `claims[]`: per-claim `result`, status, evidence refs, missing evidence refs, and waiver refs.
- `waivers[]`: flattened waiver status and ownership data.
- `warnings[]` and `errors[]`.

The default mode is report-only. Strict mode turns blocking assurance findings into policy errors.

#### 4.11 Change package

`change-package/v2` is the preview proof-carrying package. It groups:

- source and intent
- scope and risk
- evidence and reproducibility
- rollout and monitoring plans
- assurance target/achieved/status
- claims, assumptions, proof obligations, counterexamples, trust boundary, runtime controls, and waivers

The v2 package consumes claim-evidence and policy artifacts; it is not the source of truth for raw evidence. Until v2 is selected as mandatory by policy, generators should preserve v1 compatibility or dual-write behavior.

#### 4.12 PR/release summary

A PR or release summary is a human-facing projection of the contracts above. The preview schema is `schema/claim-level-summary-v1.schema.json`, and the current deterministic preview producer is `scripts/assurance/aggregate-claim-levels.mjs` (`pnpm run claim-level-summary:generate`). The producer consumes `claim-evidence-manifest/v1`, `policy-gate-summary/v1`, optional `change-package/v2`, and optional `temporary-override/v1` records, preserving the current primary artifact state sets while projecting the richer PR/release review states. It should surface:

- target and achieved assurance level
- satisfied, tested, model-checked, proved, runtime-mitigated, waived, unresolved, failed, and not-applicable claim counts
- blocking and report-only policy outcomes
- active/expired/orphan waivers
- runtime-mitigated claims
- assumptions and residual risks
- artifact paths needed to reproduce the judgment

Summaries must avoid wording that claims proof beyond the linked evidence scope.

### 5. Achieved-level aggregation semantics

#### 5.1 Ordering and floor/ceiling

- Levels are ordered `A0` to `A4`.
- `targetLevel` is the claim's requested level.
- `achievedLevel` is the maximum level justified after all evidence and negative evidence are considered.
- `achievedLevel` must not exceed `targetLevel` for an unsatisfied, unresolved, or partially supported claim.
- `A0` is the safe fallback when no reliable evidence exists.

#### 5.2 Current source semantics

| Source | Current derivation rule | Design interpretation |
| --- | --- | --- |
| `assurance-summary/v1` | `status=satisfied` yields achieved level at target; `status=warning` or non-empty `missingLanes` / `missingEvidenceKinds` derives below target. | Lane aggregation is conservative and missing lanes or missing evidence kinds reduce the achieved level. |
| `claim-evidence-manifest/v1` | `status=satisfied` is normalized to at least target; `partial` and `unresolved` are kept below target; `waived` requires waiver refs. | Manifest is the canonical per-claim support state. |
| `change-package/v2` | Top-level `assurance.achievedLevel` and `assurance.status` are imported, while proof obligations, counterexamples, and waivers can downgrade or qualify claims. | Package-level assurance must be reconciled with manifest evidence, not blindly trusted. |
| Policy-gate assurance | `pass`, `waived`, `report-only`, and `block` are policy outcomes over claim state. | Policy result is not an assurance level; it controls workflow behavior. |

#### 5.3 Aggregation rules

1. Start from the claim's `targetLevel` and required lanes/evidence kinds.
2. Normalize all linked evidence into evidence kinds and source artifacts.
3. Mark every missing required lane or evidence kind in `missingEvidenceRefs`.
4. If a counterexample, failed proof obligation, failed required check, stale artifact, or rejected review invalidates evidence, keep or move the claim to `partial` or `unresolved` and keep achieved level below target.
5. If all required evidence is present and no unresolved blocker exists, the claim may be `satisfied` and achieved level can reach target.
6. If evidence supports only a weaker level, achieved level remains at the weaker level even when CI is green.
7. If a claim is waived, keep waiver details and do not count it as satisfied.
8. If a claim is runtime-mitigated, record runtime control evidence and residual risk; do not treat it as proof/model-checking evidence.
9. When multiple sources disagree, choose the more conservative claim status in this order: `unresolved` > `waived` > `partial` > `satisfied`, while preserving all evidence and notes.
10. When a current primary schema lacks a precise state, represent it as `unresolved` or `partial` with a note/missing-evidence reference rather than introducing an undeclared enum value. Use `claim-level-summary/v1` only as a preview projection until producers and consumers are promoted together.

### 6. Failure-mode representation

| Condition | Current representation | Policy behavior |
| --- | --- | --- |
| Missing evidence | `missingEvidenceRefs[]`, missing source artifact, `partial`/`unresolved` claim status. | Warning in report-only; `block` in strict mode when the normalized claim result is blocking. |
| Failed evidence | `unresolved` or `partial` claim status, missing evidence reason, policy warning/error, or failed check evidence. | Report-only warning by default; strict mode blocks if mapped to `block`. |
| Stale evidence | Current contracts do not have a dedicated stale field. Use `unresolved`/`partial`, notes, warnings, or missing evidence until freshness metadata is added. | Report-only by default; strict mode can block once schema/policy defines freshness checks. |
| Waived evidence | `waiverRefs[]` and claim status `waived`; policy waiver status flattened as active/expiring/expired/orphan/unknown. | Active/expiring waivers produce `waived`; expired/orphan waivers block in strict mode. |
| Runtime mitigation | Runtime evidence refs, runtime controls, or `runtime-mitigated` change-package claim status. | Does not satisfy proof/model obligations; may reduce residual operational risk. |
| Out of scope / not applicable | Manifest claim status remains omitted non-claim, `unresolved` with note, or waiver/residual risk. `change-package/v2` may record explicit `not-applicable` as a package/release outcome with reviewable rationale. | Report-only unless a future schema/policy migration promotes the state into primary evidence enforcement. |

### 7. Policy-gate semantics

#### 7.1 Mode selection

- `report-only` is the default and is selected when no explicit assurance mode is configured.
- `strict` is selected only by explicit policy configuration, environment variable, label/risk profile, or a future documented policy route.
- Invalid assurance mode values fall back to `report-only` with a warning.

#### 7.2 Result mapping

| Normalized claim state | Claim policy result | Gate result contribution |
| --- | --- | --- |
| `satisfied` with no missing evidence | `pass` | Can contribute to gate `pass`. |
| `partial` | `report-only` | Warning in report-only; not treated as satisfied. |
| `unresolved` | `block` | Warning in report-only; error in strict mode. |
| `waived` with active/expiring waiver | `waived` | Distinct from pass; visible in summaries. |
| `waived` with expired/orphan waiver | `block` | Error in strict mode. |
| Manifest missing | gate `report-only` with warning | Does not block by default. |

#### 7.3 Enforcement behavior

- Report-only mode must not block normal PR flow solely because assurance evidence is missing or partial.
- Strict mode must fail when assurance evaluation result is `block`.
- Strict mode may allow `waived`, but the waiver must be visible and must include owner, reason, expiry, and related claim IDs.
- Security high/critical open findings and findings needing human review remain warnings unless a specific policy maps them to blocking errors.

### 8. Migration strategy from current contracts

1. Keep `assurance-summary/v1`, `claim-evidence-manifest/v1`, `policy-gate-summary/v1`, and `change-package/v2` readable by current consumers.
2. Prefer additive optional fields for requirement references, freshness metadata, or per-claim summary fields.
3. Use preview names or versioned schema IDs for breaking changes.
4. Dual-write and dual-validate when promoting preview artifacts to default production outputs.
5. Keep Markdown sidecars during migration so human review does not depend on raw JSON.
6. Document producer, consumer, artifact path, validation command, and rollback plan for every schema change.
7. Do not emit `not-applicable` as a `claim-evidence-manifest/v1` claim status or evidence kind until the schema, fixtures, docs, producer, policy-gate, and summary consumers accept that promotion. `change-package/v2` may continue to carry it as a package/release outcome state.

### 9. Test and fixture strategy

| Layer | Required test/fixture coverage |
| --- | --- |
| Schema | Positive and negative JSON fixtures for each schema change; `pnpm run check:schemas`. |
| Contract tests | Contract tests for `assurance-summary`, `claim-evidence-manifest`, `policy-gate-summary`, and `change-package-v2`. |
| Aggregator | Unit tests for missing evidence, partial evidence, waived claims, runtime-mitigated claims, proof obligations, counterexamples, and external IDs. |
| Policy gate | Tests for report-only versus strict, expired/orphan waivers, manifest missing, unresolved claims, and all-pass claims. |
| Change package | Tests for v1 compatibility, v2 preview generation, dual-write, assurance imports, proof obligations, runtime controls, and waivers. |
| E2E fixture | Extend `fixtures/assurance-e2e/inventory-waiver` rather than creating an unrelated scenario first. Golden JSON and Markdown should be portable across worktrees. |
| Docs | `pnpm -s run check:doc-consistency` for frontmatter, canonical references, and generated doc consistency. |

Suggested validation for docs-only design changes:

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
git diff --check
```

### 10. Follow-up implementation map

| Follow-up issue | Design dependency |
| --- | --- |
| #3306 schema stabilization | Additive or preview schema fields must follow the model and migration rules in this design. |
| #3307 per-claim achieved-level summary | Use the manifest as canonical input and expose achieved-level, missing evidence, waivers, runtime mitigation, and residual risk compactly. |
| #3308 assurance-aware policy gate | Implement report-only/strict mode behavior without treating waivers or runtime controls as proof. |
| #3309 proof-carrying change package | Keep `change-package/v2` preview/dual-write compatible and surface policy/claim evidence links. |
| #3310 producer-agent runbook | Treat Codex/Claude/MCP as replaceable producers that emit or trigger artifacts consumed by this design. |
| #3311 E2E fixture | Cover satisfied, partial, waived, runtime-mitigated, and unresolved claims using current schemas. |
| #3312 cleanup | Mark obsolete/duplicate routes only after canonical contracts above are linked and validated. |

---

## 日本語要約

この文書は、ae-framework を assurance control plane として実装するための詳細設計である。`claim-evidence-manifest/v1`、`assurance-summary/v1`、`policy-gate-summary/v1`、`change-package/v2` を現行の前提として、claim 単位の evidence、achieved level、waiver、runtime control、policy-gate、PR/release summary の責務と入出力を定義する。

主要な設計判断は次のとおりである。

- assurance は repository 全体の green status ではなく claim 単位で評価する。
- `A0` から `A4` までの achieved level は、利用可能な evidence を超えて上げない。
- waiver は satisfied claim ではなく、owner、reason、expiry、related claim ID、evidence link を持つ期限付き例外として扱う。
- runtime control は operational risk の緩和であり、proof / model checking ではない。
- 現行 `claim-evidence-manifest/v1.claims[].status` が emit できる value は `partial`、`satisfied`、`waived`、`unresolved` であり、evidence kind は `evidenceRefs[].kind` に分離する。
- `not-applicable` は `claim-evidence-manifest/v1` の claim status や evidence kind ではない。`change-package/v2` では package / release outcome state として保持でき、`claim-level-summary/v1` では PR / release projection として表示できるが、manifest 側へ戻すには明示的な schema / policy migration が必要である。
- policy-gate は既定で `report-only` とし、明示的な policy がある場合のみ `strict` enforcement を選択する。
- schema 変更は additive、preview version、または dual-write / dual-validate で移行する。

この設計は #3306 以降の schema、per-claim summary、policy-gate、change-package、producer-agent runbook、E2E fixture、cleanup の実装基準として使う。
