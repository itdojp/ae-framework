---
docRole: derived
canonicalSource:
  - docs/product/ASSURANCE-CONTROL-PLANE.md
  - docs/quality/ASSURANCE-MODEL.md
  - docs/quality/ARTIFACTS-CONTRACT.md
  - docs/reference/CONTRACT-CATALOG.md
  - docs/reference/change-package-v2.md
lastVerified: '2026-05-08'
---

# Assurance Control Plane Current-State Report

> Language / 言語: English | 日本語

---

## English

### 1. Executive summary

This report records the current `main` state at commit `cb307e05` (`feat(security): generate audit prompt packs (#3301)`). The repository already contains a substantial assurance-control-plane implementation: product positioning, assurance terminology, Context Pack checks, Verify Lite summaries, formal and conformance producers, quality scorecards, policy-gate outputs, claim-evidence manifests, change-package v2, PR-summary inputs, and Security Assurance Lane producers.

The current gap is not a lack of individual producers. The main gap is convergence: several contracts and docs exist, but the next work should make the canonical policy, detailed design, schema boundaries, report-only versus enforcement semantics, and PR/release package flow easier to follow from one route.

Recommended next slice: start with Issue #3304 and converge policy/terminology around the existing `docs/product/ASSURANCE-CONTROL-PLANE.md` and `docs/quality/ASSURANCE-MODEL.md` before creating new schema or enforcement behavior. This is the smallest low-risk step because it reduces duplication and over-claiming without changing CI behavior.

### 2. Inspection baseline

Inspection was performed before editing this report.

| Check | Evidence |
| --- | --- |
| Working tree | `git status --short` was empty in worktree `ae-framework-3303-current-state` before editing. |
| Current commit | `git rev-parse --short HEAD` = `cb307e05`. |
| Recent history | `git log --oneline -n 20` shows recent security-assurance and testing work from #3274 through #3301. |
| Package scripts | `cat package.json` confirmed assurance, claim-evidence, policy-gate, change-package, Context Pack, conformance, formal, Codex/MCP, schema, and doc-consistency scripts. |
| Docs inspected | `docs/product/`, `docs/quality/`, `docs/architecture/`, `docs/integrations/`, `docs/reference/`, `docs/agents/`, `docs/ci/`, `docs/verify/`, and `docs/security/`. |
| Contracts inspected | `schema/` contains assurance, claim-evidence, policy, policy-gate, change-package, quality-scorecard, verify-lite, formal, conformance, and security-assurance schemas. |
| Scripts and tests inspected | `scripts/`, `src/`, `tests/`, `.github/workflows/`, `fixtures/`, `samples/`, and `artifacts/` were searched for assurance-control-plane terms and files. |

### 3. Recent repository changes relevant to assurance

The last 20 commits on `main` show the repo is actively extending assurance evidence and test coverage:

| Commit | Relevance |
| --- | --- |
| `cb307e05` | Adds Security Assurance Lane audit prompt packs (#3301). |
| `2c396e89` | Adds assumption-aware security claim review handling (#3300). |
| `7265908a` | Adds entrypoint-map evidence for trust-boundary review (#3299). |
| `45405340` | Adds symbol-index input for code map (#3298). |
| `96b55041` | Preserves original security IDs in claim-evidence manifests (#3297). |
| `fb2fbc3a` | Adds testing inventory freshness reporting (#3291). |
| `1835daf0` | Adds agent MCP smoke lane (#3290). |
| `937c23fa` | Adds package app smoke lane (#3289). |
| `e9c4d088` | Covers CLI command boundary regressions (#3288). |
| `a866564d` | Covers security assurance CLI boundaries (#3287). |
| `6d8330fd` | Documents test portfolio baseline (#3286). |
| `944fc818` | Adds Security Assurance Lane overview (#3278). |
| `06f5af56` | Adds Codex Security Assurance Lane runbook (#3277). |
| `0da06ed9` | Adds security assurance fixture golden scenario (#3276). |
| `936228f7` and related commits | Integrate security findings into assurance artifacts (#3275). |
| `438c3345` | Adds rule-based security review producer (#3274). |

### 4. Current positioning and architecture

Current positioning is already documented as BYO-agent plus assurance control plane:

- `docs/product/ASSURANCE-CONTROL-PLANE.md` defines ae-framework as the layer above producer agents and verification tools that keeps specification, verification, evidence, policy/PR gates, and release judgment under consistent contracts.
- `docs/quality/ASSURANCE-MODEL.md` defines claim, assurance level, validation lane, evidence kind, assumption, waiver, and runtime control.
- `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md` is cited as an implementation-aligned system overview by `docs/README.md`.
- `docs/reference/CONTRACT-CATALOG.md` maps current contracts to schemas, producers, and consumers.
- `docs/security/security-assurance-lane.md` extends the model with security-specific claims, findings, code maps, reviews, assumption handling, and prompt packs.

The architecture is therefore better described as a federated set of evidence producers and judgment-side contracts than as a single monolithic runner.

### 5. Capability inventory

Status meanings used below:

- `ready`: executable contract, producer, consumer, fixture, and test or workflow evidence are present for the stated scope.
- `partial`: useful implementation exists, but coverage or integration is not complete enough to call the whole capability ready.
- `preview`: implemented behind opt-in, dual-write, report-only, or compatibility behavior.
- `missing`: no direct implementation was found for the stated capability.
- `obsolete`: superseded or legacy behavior remains and should be marked rather than deleted immediately.
- `duplicate`: multiple routes or names exist and need canonicalization.

| Capability | Status | Evidence from current HEAD | Gap / next action |
| --- | --- | --- | --- |
| Assurance-control-plane product positioning | ready | `docs/product/ASSURANCE-CONTROL-PLANE.md`; `docs/quality/ASSURANCE-MODEL.md`; the root `../../README.md` links to the product doc. | #3304 should converge policy wording and avoid creating a competing policy doc unless it explicitly supersedes the current product doc. |
| Context Pack structural validation | ready | Package scripts `context-pack:validate`, `context-pack:verify-functor`, `context-pack:verify-natural-transformation`, `context-pack:verify-product-coproduct`, `context-pack:e2e-fixture`; `fixtures/context-pack/e2e/evidence/*`; docs under `docs/agents/context-pack.md` and `docs/guides/context-pack-*`. | Link Context Pack evidence more directly into claim-level aggregation in #3307 if current artifact routing is insufficient. |
| Verify Lite summaries and workflow | ready | `.github/workflows/verify-lite.yml`; `scripts/ci/verify-lite.sh`; `scripts/ci/write-verify-lite-summary.mjs`; `scripts/ci/render-verify-lite-summary.mjs`; `schema/verify-lite-run-summary.schema.json`; `tests/scripts/run-verify-lite-local.test.ts`; `tests/unit/ci/write-verify-lite-summary.test.ts`. | Keep as a core input; do not rewrite for #3303. |
| Formal summaries | ready | `schema/formal-summary-v1.schema.json`; `schema/formal-summary-v2.schema.json`; `scripts/formal/aggregate-formal.mjs`; `scripts/formal/print-summary.mjs`; `.github/workflows/formal-aggregate.yml`; `fixtures/formal/sample.formal-summary-v2.json`; `tests/unit/ci/validate-formal-summary-v2.test.ts`. | Formal evidence should state model scope and assumptions in #3305/#3307. |
| Conformance summaries | partial | `schema/conformance-verify-result.schema.json`; scripts `conformance:verify:sample`, `conformance:report`, `verify:conformance`; `src/conformance/*`; `tests/conformance/*`; `fixtures/conformance/*`; `samples/conformance/*`. | Conformance exists as producer evidence, but its canonical claim-level mapping should be clarified in #3305/#3307. |
| Quality scorecard | ready | `schema/quality-scorecard.schema.json`; package scripts `quality:scorecard:v1` and `quality:scorecard:validate`; `scripts/quality/build-quality-scorecard.mjs`; `scripts/ci/validate-quality-scorecard.mjs`; `fixtures/quality/sample.quality-scorecard.json`; `tests/scripts/build-quality-scorecard.test.ts`; `tests/contracts/quality-scorecard-contract.test.ts`. | Legacy `quality:scorecard` still points to `scripts/quality-scorecard-generator.js`; canonical route should be made explicit in #3312. |
| Policy gate baseline | ready | `.github/workflows/policy-gate.yml`; `scripts/ci/policy-gate.mjs`; `scripts/ci/policy-shadow-compare.mjs`; `schema/policy-input-v1.schema.json`; `schema/policy-decision-v1.schema.json`; `schema/policy-gate-summary-v1.schema.json`; `fixtures/policy-gate/sample.policy-gate-summary-v1.json`; `tests/unit/ci/policy-gate.test.ts`. | Assurance-aware enforcement is not fully converged; #3308 should preserve report-only behavior unless explicit enforcement is selected. |
| Assurance summary v1 | ready | `schema/assurance-summary.schema.json`; `fixtures/assurance/sample.assurance-summary.json`; `scripts/assurance/aggregate-lanes.mjs`; `scripts/ci/validate-assurance-summary.mjs`; `tests/contracts/assurance-summary-contract.test.ts`; `tests/unit/ci/validate-assurance-summary.test.ts`. | Document exact producer inputs and confidence boundaries in #3305. |
| Claim-evidence manifest and achieved-level sidecar | partial | `schema/claim-evidence-manifest.schema.json`; package script `claim-evidence:generate`; `scripts/assurance/build-claim-evidence-manifest.mjs`; `fixtures/assurance/sample.claim-evidence-manifest.json`; `tests/scripts/claim-evidence-manifest.test.ts`; `tests/contracts/claim-evidence-manifest-contract.test.ts`; `docs/quality/assurance-profile.md` describes report-only achieved-level summary behavior. | #3307 should close the gap between sidecar generation and a stable per-claim summary artifact/Markdown output for PR judgment. |
| Waiver handling | partial | `docs/quality/ASSURANCE-MODEL.md`; `schema/claim-evidence-manifest.schema.json`; `schema/change-package-v2.schema.json`; `schema/policy-decision-v1.schema.json`; `schema/policy-gate-summary-v1.schema.json`; `fixtures/assurance-e2e/inventory-waiver/*`; `scripts/change-package/validate.mjs`; `scripts/assurance/build-claim-evidence-manifest.mjs`. | Waivers exist in multiple contracts, but a canonical temporary-override contract and enforcement semantics remain to be specified in #3305/#3306/#3308. |
| Change package v1/v2 | preview | `schema/change-package.schema.json`; `schema/change-package-v2.schema.json`; `docs/reference/change-package-v2.md`; package scripts `change-package:generate`, `change-package:generate:v2`, `change-package:generate:dual`, `change-package:validate:v2`; `fixtures/change-package/*`; `tests/contracts/change-package-v2-contract.test.ts`; `tests/unit/ci/change-package-generate.test.ts`. | v2 is opt-in/dual-write. #3309 should stabilize the proof-carrying package path without breaking v1. |
| PR summary consumption | partial | `scripts/summary/render-pr-summary.mjs`; `docs/quality/pr-summary.md`; `docs/quality/pr-summary-tool.md`; PR summary docs mention assurance summary, claim-evidence manifest, quality scorecard, formal aggregate, and change-package v2 inputs. | UX should clearly surface evidence-backed, waived, runtime-mitigated, unresolved, failed, and not-applicable states in #3309. |
| Codex integration | partial | `docs/integrations/CODEX-INTEGRATION.md`; `docs/integrations/CODEX-CONTINUATION-CONTRACT.md`; `docs/integrations/CODEX-SECURITY-AUDIT.md`; `docs/integrations/QUICK-START-CODEX.md`; scripts under `scripts/codex/`; package scripts `codex:*`; `fixtures/codex/*`; `tests/codex/*`. | #3310 should provide one assurance-control-plane runbook that treats Codex as a producer and lists expected evidence artifacts. |
| Claude / agent integration docs | partial | `docs/integrations/CLAUDE-CODE-INTEGRATION-GUIDE.md`; `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`; `docs/agents/*`; `docs/agents/recipes/*`; `tests/agents/agent-mcp-boundary-smoke.test.ts`; recent commit `1835daf0`. | #3310 should separate optional harness guidance from required assurance-control-plane contracts. |
| MCP servers | partial | Package scripts `codex:mcp:*`, `mcp:*`, `formal-agent`; `src/mcp-server/*`; `samples/codex-mcp-config.json`; `samples/codex-mcp-config.yaml`; `tests/services/mcp-server.test.ts`; `tests/agents/agent-mcp-boundary-smoke.test.ts`. | MCP is an integration surface; it is not yet the canonical assurance evidence flow. Cover in #3310. |
| Spec & Verification Kit | partial | `docs/reference/SPEC-VERIFICATION-KIT-MIN.md`; `docs/reference/SPEC-VERIFICATION-KIT-EXTENSIONS.md`; `docs/verify/FORMAL-CHECKS.md`; Context Pack and formal scripts. | Tie kit outputs to claim/evidence contracts in #3305/#3307. |
| Security Assurance Lane | ready | `docs/security/security-assurance-lane.md`; `docs/integrations/CODEX-SECURITY-AUDIT.md`; schemas `security-*-v1`; CLI scripts `security:import-speca`, `security:extract-claims`, `security:map-code`, `security:proof-audit`, `security:review`, `security:audit-prompt`; `fixtures/security-assurance/*`; `scripts/security/run-security-assurance-fixture.mjs`; `tests/contracts/security-assurance-contract.test.ts`; `tests/unit/security-assurance/*`. | Good exemplar for #3311 end-to-end fixture design. |
| End-to-end assurance fixture | ready | `fixtures/assurance-e2e/inventory-waiver/*`; package script `assurance:e2e`; `scripts/assurance/run-e2e-scenario.mjs`; `tests/scripts/assurance-e2e-scenario.test.ts`. | #3311 can extend this fixture rather than starting from scratch. |
| Current-state reporting | partial | This report adds `docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md`. | Optional machine-readable `artifacts/assurance-control-plane/current-state.json` was not created in this slice. |
| Legacy or competing quality scorecard route | duplicate | `docs/quality/quality-scorecard.md` states legacy `quality:scorecard` still points to `scripts/quality-scorecard-generator.js`, while `quality:scorecard:v1` points to `scripts/quality/build-quality-scorecard.mjs`. | #3312 should mark the canonical route and preserve compatibility. |
| Legacy formal summary path | obsolete | `docs/quality/pr-summary.md`, `docs/quality/pr-summary-tool.md`, and `docs/quality/counterexample-gwt.md` retain legacy `formal/summary.json` compatibility references. | #3312 should mark the replacement path rather than deleting compatibility without migration. |

### 6. Command / artifact / schema / workflow map

| Area | Command or workflow | Primary artifacts | Schema / contract | Tests or validation evidence |
| --- | --- | --- | --- | --- |
| Context Pack | `pnpm run context-pack:validate`, `pnpm run context-pack:verify-functor`, `pnpm run context-pack:verify-natural-transformation`, `pnpm run context-pack:verify-product-coproduct` | Context Pack reports and fixture evidence | Context Pack docs and fixture conventions | Context Pack fixture scripts and docs under `docs/agents/` / `docs/guides/` |
| Verify Lite | `pnpm run verify:lite`, `.github/workflows/verify-lite.yml` | `artifacts/verify-lite/verify-lite-run-summary.json` | `schema/verify-lite-run-summary.schema.json` | `tests/scripts/run-verify-lite-local.test.ts`, `tests/unit/ci/write-verify-lite-summary.test.ts` |
| Assurance summary | `pnpm run verify:assurance` | `artifacts/assurance/assurance-summary.json` | `schema/assurance-summary.schema.json` | `tests/contracts/assurance-summary-contract.test.ts`, `tests/unit/ci/validate-assurance-summary.test.ts` |
| Claim evidence | `pnpm run claim-evidence:generate` | `artifacts/assurance/claim-evidence-manifest.json`, Markdown sidecar | `schema/claim-evidence-manifest.schema.json` | `tests/contracts/claim-evidence-manifest-contract.test.ts`, `tests/scripts/claim-evidence-manifest.test.ts` |
| Formal aggregate | `pnpm run formal:summary`, `.github/workflows/formal-aggregate.yml` | Formal aggregate / summary JSON | `schema/formal-summary-v1.schema.json`, `schema/formal-summary-v2.schema.json` | `tests/unit/ci/validate-formal-summary-v2.test.ts`, `tests/formal/*` |
| Conformance | `pnpm run conformance:verify:sample`, `pnpm run conformance:report` | Conformance verify result and reports | `schema/conformance-verify-result.schema.json` | `tests/conformance/*`, `tests/unit/cli/conformance-ingest.test.ts` |
| Quality scorecard | `pnpm run quality:scorecard:v1`, `pnpm run quality:scorecard:validate` | `artifacts/quality/quality-scorecard.json` | `schema/quality-scorecard.schema.json` | `tests/contracts/quality-scorecard-contract.test.ts`, `tests/scripts/build-quality-scorecard.test.ts` |
| Policy gate | `.github/workflows/policy-gate.yml`, `scripts/ci/policy-gate.mjs` | `artifacts/ci/policy-input-v1.json`, `policy-decision-js-v1.json`, `policy-gate-summary.json` | `schema/policy-input-v1.schema.json`, `schema/policy-decision-v1.schema.json`, `schema/policy-gate-summary-v1.schema.json` | `tests/unit/ci/policy-gate.test.ts`, `tests/unit/ci/policy-shadow-compare.test.ts` |
| Change package | `pnpm run change-package:generate`, `pnpm run change-package:generate:v2`, `pnpm run change-package:validate:v2` | `artifacts/change-package/change-package.json`, `change-package-v2.json`, Markdown summary | `schema/change-package.schema.json`, `schema/change-package-v2.schema.json` | `tests/contracts/change-package-v2-contract.test.ts`, `tests/unit/ci/change-package-*.test.ts` |
| Security assurance | `pnpm run test:security-assurance`, package scripts with the `security:` prefix | Security claims, threat model, audit scope, findings, review, prompt pack, summaries | `schema/security-*-v1.schema.json` | `tests/contracts/security-assurance-contract.test.ts`, `tests/unit/security-assurance/*` |
| Agent / Codex / MCP | package scripts with the `codex:` and `mcp:` prefixes | Codex responses, MCP interactions, prompt packs | `fixtures/codex/*`, `docs/integrations/schemas/*` | `tests/codex/*`, `tests/agents/agent-mcp-boundary-smoke.test.ts`, `tests/services/mcp-server.test.ts` |

### 7. Gap and duplication table

| Topic | Classification | Current evidence | Risk if left unresolved | Suggested owner issue |
| --- | --- | --- | --- | --- |
| Canonical assurance-control-plane policy route | partial | `docs/product/ASSURANCE-CONTROL-PLANE.md` and `docs/quality/ASSURANCE-MODEL.md` both define core concepts. | Future issues may create another policy doc and fragment terminology. | #3304 |
| Detailed design for claim/evidence/achieved-level/policy package | missing | Pieces exist in product, quality, schemas, scripts, and reference docs, but no single detailed architecture doc was found. | Implementations may infer different semantics for missing, stale, waived, runtime-mitigated, or not-applicable evidence. | #3305 |
| Temporary override / waiver contract | partial | Waiver fields exist in claim-evidence, change-package v2, policy input/decision/summary, and assurance model docs. | Enforcement may treat waived as satisfied or omit required owner/reason/expiry links. | #3305, #3306, #3308 |
| Per-claim achieved-level artifact and PR Markdown | partial | Claim-evidence manifest includes `achievedLevel` and Markdown rendering; a separate stable summary artifact is not yet canonical. | PR reviewers may need to inspect multiple artifacts instead of a compact claim-level judgment summary. | #3307 |
| Assurance-aware policy-gate enforcement | partial | Policy gate carries report-only assurance sections and waiver-aware decisions. | Enabling enforcement without clear mode boundaries could break normal PR flow. | #3308 |
| Change-package v2 production path | preview | v2 schema, docs, generator, dual-write, strict validation, and fixtures exist. | Reviewers may confuse preview v2 with default production v1. | #3309 |
| Agent integration runbook | partial | Codex, Claude, MCP, and agent docs exist across several directories. | Producer agents may be treated as the product boundary instead of evidence producers. | #3310 |
| E2E assurance fixture | ready but extendable | `fixtures/assurance-e2e/inventory-waiver` exists and includes non-green waiver-aware cases. | New schema/policy work may not be validated end-to-end if this fixture is not extended. | #3311 |
| Legacy scorecard route | duplicate | `quality:scorecard` and `quality:scorecard:v1` coexist. | Operators may invoke the legacy route by accident. | #3312 |
| Legacy formal summary path | obsolete compatibility | Legacy `formal/summary.json` is retained in PR summary docs as a fallback. | Compatibility language may be mistaken for the preferred contract. | #3312 |

### 8. Over-claiming risk table

| Risk | Current state | Control to apply in follow-up issues |
| --- | --- | --- |
| Treating green CI as high assurance | Docs already distinguish assurance levels and verification lanes. | Keep the distinction explicit in #3304 and #3305. |
| Treating runtime mitigation as proof | `docs/quality/ASSURANCE-MODEL.md` separates runtime controls from proof/model-check evidence. | Ensure #3305 and #3309 preserve separate rendered states. |
| Treating waived claims as satisfied claims | Schemas and generators carry `waived` states and waiver refs. | #3308 should fail closed only in explicit enforcement mode and should render waivers separately. |
| Treating change-package v2 as default production contract | `docs/reference/change-package-v2.md` says v1 remains default and v2 is opt-in/dual-write. | #3309 should retain compatibility or document migration windows. |
| Treating producer agents as ae-framework runtime | Integration docs exist, but routes are distributed. | #3310 should state producer/control-plane boundaries in a single runbook. |
| Treating formal summary as full proof | Formal summary schemas and docs exist, but model scope assumptions must be explicit. | #3305/#3307 should require scope/assumption links for model/proof evidence. |
| Treating security assumption findings as confirmed vulnerabilities | Security Assurance Lane docs and prompt pack work separate candidate findings and assumption handling. | Reuse that pattern for general claim evidence in #3307/#3309. |

### 9. Recommended smallest next implementation slice

Proceed with #3304 as a docs-only convergence PR:

1. Update or extend `docs/product/ASSURANCE-CONTROL-PLANE.md` rather than creating a competing product policy unless a new file is clearly marked as canonical.
2. Cross-link `docs/quality/ASSURANCE-MODEL.md`, `docs/quality/ARTIFACTS-CONTRACT.md`, `docs/reference/CONTRACT-CATALOG.md`, and this report.
3. Add explicit valid/invalid wording examples to avoid over-claiming.
4. Keep validation to `pnpm -s run check:doc-consistency` unless broader changes are made.

Rationale: the current repo already has executable contracts. Clarifying policy and terminology first reduces duplication risk for schema, policy-gate, and change-package work.

### 10. Suggested child issue updates based on current state

| Issue | Suggested adjustment |
| --- | --- |
| #3304 | Treat `docs/product/ASSURANCE-CONTROL-PLANE.md` and `docs/quality/ASSURANCE-MODEL.md` as the current canonical starting point. Add policy examples and cross-links rather than duplicating content. |
| #3305 | Create a detailed design that references existing schemas and scripts. Focus on semantics that are currently spread across docs and code. |
| #3306 | Reuse `schema/assurance-summary.schema.json`, `schema/claim-evidence-manifest.schema.json`, `schema/policy-*.schema.json`, and `schema/change-package-v2.schema.json`. Add new schema only where a real gap remains. |
| #3307 | Extend the existing claim-evidence generation path before adding a separate aggregator. Keep output deterministic and PR-reviewable. |
| #3308 | Preserve current policy-gate behavior as compatible report-only by default; make fail-closed behavior explicit and opt-in. |
| #3309 | Stabilize v2 as proof-carrying package while preserving v1 compatibility or dual validation. |
| #3310 | Build one runbook from existing Codex, Claude, MCP, and Security Assurance Lane docs. Make agents producers, not required runtime dependencies. |
| #3311 | Reuse `fixtures/assurance-e2e/inventory-waiver` and security-assurance fixtures as proven examples. |
| #3312 | Mark canonical versus legacy routes for scorecard, formal summary fallback, and duplicated judgment docs before deleting anything. |

### 11. 日本語要約

現行 `main` には、assurance control plane の主要部品が既に多数存在します。特に、Verify Lite、assurance summary、claim-evidence manifest、policy gate、quality scorecard、change-package v2、Security Assurance Lane は、schema・fixture・script・test の形で確認できます。

ただし、設計と運用導線は複数文書に分散しています。次に実装を増やす前に、#3304 で policy / terminology を収束させ、#3305 で詳細設計を固定するのが最小リスクです。
