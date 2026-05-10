---
docRole: derived
canonicalSource:
  - docs/product/ASSURANCE-CONTROL-PLANE.md
  - docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md
  - docs/architecture/ASSURANCE-CONTROL-PLANE-DETAILED-DESIGN.md
  - docs/quality/ASSURANCE-MODEL.md
  - docs/quality/ARTIFACTS-CONTRACT.md
  - docs/reference/CONTRACT-CATALOG.md
  - docs/reference/SCHEMA-GOVERNANCE.md
  - docs/reference/change-package-v2.md
lastVerified: '2026-05-10'
---

# Assurance Control Plane Current-State Report

> Language / 言語: English | 日本語

---

## English

### 1. Executive summary

This report records the post-roadmap `main` state at full commit `a4245f693bff38229bf6431f27fbf3d20266d259` (`test(assurance): assert canonical route scenario (#3338)`). It replaces the older inspection baseline `cb307e05` from the pre-roadmap audit and treats Issues #3302-#3312 / PRs #3313-#3322 as completed historical work.

The repository now contains an assurance control plane for agent-driven SDLC rather than a coding-agent runtime: policy and detailed-design docs, contract catalog, canonical-route guidance, schema governance, claim and evidence producers, policy-gate summaries, change-package v1/v2 flows, PR summary rendering, E2E fixtures, and Security Assurance Lane producers.

The current work is no longer to invent the roadmap. The current work is governance and maintenance: keep canonical routes discoverable, preserve compatibility until consumer tests prove migration safety, surface migration notes for contract changes, and keep current-state reporting anchored to the inspected HEAD.

No separate `docs/reports/ASSURANCE-CONTROL-PLANE-REPO-SNAPSHOT.md` is introduced in this refresh. This report is the canonical repository snapshot for the assurance control plane because it already records the HEAD, command inventory, contract inventory, route state, and residual follow-up guidance in one derived document.

### 2. Inspection baseline

Inspection was performed before editing this report in worktree `ae-framework-3323-current-state-refresh`.

| Check | Evidence |
| --- | --- |
| Working tree | `git status --short --branch` showed branch `docs/3323-current-state-refresh` based on `origin/main` before content changes. |
| Current commit | `git rev-parse HEAD` = `a4245f693bff38229bf6431f27fbf3d20266d259`. |
| Recent history | `git log --oneline -n 25` shows the completed roadmap sequence #3313-#3322 followed by post-roadmap hardening #3333-#3338. |
| Package scripts | `cat package.json` / script inventory confirmed assurance, claim-evidence, claim-level-summary, policy-gate, change-package, quality scorecard, Security Assurance Lane, schema, and doc-consistency commands. |
| Docs inspected | `docs/product/`, `docs/architecture/`, `docs/quality/`, `docs/reference/`, `docs/reports/`, `docs/integrations/`, `docs/agents/`, `docs/ci/`, `docs/verify/`, and `docs/security/`. |
| Contracts inspected | `schema/` contains assurance, claim, policy, policy-gate, change-package, quality-scorecard, verify-lite, formal, conformance, temporary-override, and security-assurance schemas. |
| Scripts and tests inspected | `scripts/`, `src/`, `tests/`, `.github/workflows/`, `fixtures/`, and `samples/` were searched for assurance-control-plane entry points and evidence routes. |

### 3. Completed assurance-control-plane roadmap evidence

The completed roadmap is now historical baseline evidence, not planned work:

| Merge | Relevance |
| --- | --- |
| #3313 / `58d5b9c8` | Added the first assurance-control-plane current-state audit. |
| #3314 / `188bbc82` | Defined the assurance-control-plane policy. |
| #3315 / `3cadc892` | Added detailed design for claim, evidence, achieved-level, policy, waiver, and package semantics. |
| #3316 / `2427eb9c` | Stabilized preview claim-summary schemas. |
| #3317 / `6bbe479c` | Added deterministic claim-level summary generation. |
| #3318 / `c80fdd24` | Added assurance-aware policy-gate modes while preserving report-only defaults. |
| #3319 / `9c3c6ecf` | Stabilized proof-carrying change-package v2 behavior. |
| #3320 / `737e50c6` | Added the assurance agent runbook. |
| #3321 / `5d3e9dd1` | Extended the E2E assurance validation fixture. |
| #3322 / `dc518ddb` | Marked canonical and legacy assurance routes. |

### 4. Post-roadmap hardening evidence

Post-roadmap hardening has also landed on `main`:

| Merge | Relevance |
| --- | --- |
| #3333 / `a0308acc` | Wrapped the legacy quality-scorecard route and added compatibility coverage. |
| #3334 / `74ccadaf` | Made PR summary formal evidence prefer canonical aggregate artifacts over legacy fallback paths. |
| #3335 / `a3d4e968` | Derived counterexample GWT output from canonical formal evidence. |
| #3336 / `95e98b00` | Added a schema-governance consistency check and governance documentation. |
| #3337 / `c725be7a` | Added `contractMigrationNotes` support in change-package v2 generation and PR summary rendering. |
| #3338 / `a4245f69` | Added a canonical-route regression over the assurance E2E fixture. |

### 5. Current positioning and architecture

Current positioning is documented as a BYO-agent assurance control plane:

- `docs/product/ASSURANCE-CONTROL-PLANE.md` positions ae-framework as a control plane above producer agents and verification tools.
- `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` is the SSOT policy for BYO-agent boundaries, claim-based assurance, evidence-state wording, report-only defaults, and contract evolution.
- `docs/architecture/ASSURANCE-CONTROL-PLANE-DETAILED-DESIGN.md` defines claim/evidence/achieved-level/waiver/policy/change-package semantics.
- `docs/reference/CONTRACT-CATALOG.md` maps contracts to schemas, producers, consumers, and validation evidence.
- `docs/reference/ASSURANCE-CANONICAL-ROUTES.md` distinguishes canonical routes from compatibility or preview routes.
- `docs/reference/SCHEMA-GOVERNANCE.md` defines schema-governance requirements and is checked by `pnpm run check:assurance-contract-governance`.
- `docs/security/security-assurance-lane.md` extends the model for security claims, findings, code maps, reviews, and audit prompt packs.

The architecture is best described as federated evidence producers plus contract-governed judgment and release artifacts. Producer agents remain replaceable inputs; the control-plane contracts are the durable boundary.

### 6. Capability inventory

Status meanings used below:

- `ready`: executable contract, producer, consumer, fixture, and test or workflow evidence are present for the stated scope.
- `partial`: useful implementation exists, but coverage or integration is not complete enough to call the whole capability ready.
- `preview`: implemented behind opt-in, dual-write, report-only, or compatibility behavior.
- `compatibility`: intentionally retained legacy behavior with a canonical replacement or preferred route.
- `missing`: no direct implementation was found for the stated capability.

| Capability | Status | Evidence from current HEAD | Residual guidance |
| --- | --- | --- | --- |
| Product and policy positioning | ready | `docs/product/ASSURANCE-CONTROL-PLANE.md`; `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md`; `docs/architecture/ASSURANCE-CONTROL-PLANE-DETAILED-DESIGN.md`; `docs/quality/ASSURANCE-MODEL.md`. | Keep new docs linked to these SSOT files rather than creating a competing policy route. |
| Contract catalog and governance | ready | `docs/reference/CONTRACT-CATALOG.md`; `docs/reference/SCHEMA-GOVERNANCE.md`; package script `check:assurance-contract-governance`; `scripts/assurance/check-contract-governance.mjs`; `tests/unit/assurance/check-contract-governance.test.ts`. | Keep governance checks docs/check-only unless a separate enforcement issue changes policy. |
| Canonical route map | ready | `docs/reference/ASSURANCE-CANONICAL-ROUTES.md`; `fixtures/assurance-e2e/inventory-waiver/README.md`; `tests/scripts/assurance-e2e-scenario.test.ts`. | Treat compatibility language as migration support, not as canonical-route preference. |
| Context Pack structural validation | ready | Package scripts `context-pack:validate`, `context-pack:verify-functor`, `context-pack:verify-natural-transformation`, `context-pack:verify-product-coproduct`, `context-pack:verify-boundary-map`; fixture evidence under `fixtures/context-pack/`. | Keep Context Pack as producer evidence; route judgment through claim/evidence artifacts. |
| Verify Lite summaries and workflow | ready | `.github/workflows/verify-lite.yml`; `scripts/ci/verify-lite.sh`; `scripts/ci/write-verify-lite-summary.mjs`; `schema/verify-lite-run-summary.schema.json`; related tests under `tests/scripts/` and `tests/unit/ci/`. | Continue using Verify Lite as one evidence producer, not as a complete assurance claim by itself. |
| Formal summaries | ready | `schema/formal-summary-v1.schema.json`; `schema/formal-summary-v2.schema.json`; `scripts/formal/aggregate-formal.mjs`; `scripts/formal/print-summary.mjs`; `.github/workflows/formal-aggregate.yml`; formal fixtures and validation tests. | Canonical summary consumption should prefer aggregate formal artifacts; legacy `formal/summary.json` remains compatibility-only. |
| Conformance summaries | partial | `schema/conformance-verify-result.schema.json`; `src/conformance/*`; `tests/conformance/*`; `fixtures/conformance/*`; package scripts `conformance:verify:sample`, `conformance:report`, and `verify:conformance`. | Keep mapping into claim-level summaries explicit when conformance evidence is used for release judgment. |
| Quality scorecard | ready | Canonical v1 route: `quality:scorecard:v1`, `scripts/quality/build-quality-scorecard.mjs`, `schema/quality-scorecard.schema.json`, `tests/scripts/build-quality-scorecard.test.ts`, and `tests/contracts/quality-scorecard-contract.test.ts`; compatibility wrapper: `quality:scorecard`. | Prefer v1 route in new docs and tooling; keep legacy wrapper until downstream consumer coverage permits removal. |
| Policy gate baseline | ready | `.github/workflows/policy-gate.yml`; `scripts/ci/policy-gate.mjs`; `schema/policy-input-v1.schema.json`; `schema/policy-decision-v1.schema.json`; `schema/policy-gate-summary-v1.schema.json`; policy-gate tests. | Default assurance behavior remains report-only unless explicit enforcement mode is selected. |
| Assurance summary | ready | `schema/assurance-summary.schema.json`; `fixtures/assurance/sample.assurance-summary.json`; `scripts/assurance/aggregate-lanes.mjs`; package script `verify:assurance`; contract/unit tests. | Keep evidence scope and confidence boundaries visible in rendered summaries. |
| Claim evidence and claim-level summary | ready | `schema/claim-evidence-manifest.schema.json`; `schema/claim-level-summary-v1.schema.json`; package scripts `claim-evidence:generate` and `claim-level-summary:generate`; `scripts/assurance/build-claim-evidence-manifest.mjs`; `scripts/assurance/aggregate-claim-levels.mjs`; fixtures and tests. | `claim-level-summary/v1` remains the review projection for richer state rendering; do not silently change primary emitted state sets. |
| Waiver and temporary override handling | preview | `schema/temporary-override-v1.schema.json`; waiver fields in claim-evidence, policy, and change-package schemas; `fixtures/assurance-e2e/inventory-waiver/*`; E2E tests. | Waived claims are not satisfied claims; render owner/reason/expiry and preserve report-only boundaries. |
| Change package v1/v2 | preview | `schema/change-package.schema.json`; `schema/change-package-v2.schema.json`; `docs/reference/change-package-v2.md`; package scripts `change-package:generate`, `change-package:generate:v2`, `change-package:generate:dual`, `change-package:validate:v2`; fixtures and contract/unit tests. | v2 is proof-carrying and dual-write capable; do not make it mandatory for all PRs without a separate policy change. |
| Contract migration notes | ready | `schema/change-package-v2.schema.json` optional `contractMigrationNotes`; `scripts/change-package/generate.mjs`; `scripts/summary/render-pr-summary.mjs`; `docs/reference/change-package-v2.md`; `docs/quality/pr-summary.md`; related tests. | Contract-impacting PRs should include explicit migration notes and consumer-impact information. |
| PR summary consumption | partial | `scripts/summary/render-pr-summary.mjs`; `docs/quality/pr-summary.md`; `docs/quality/pr-summary-tool.md`; change-package v2, formal aggregate, claim-level summary, and quality scorecard inputs. | Keep rendering conservative: show non-green states, waivers, residual risks, and migration notes separately from satisfied evidence. |
| Codex / agent integration | partial | `docs/integrations/CODEX-INTEGRATION.md`; `docs/integrations/CODEX-CONTINUATION-CONTRACT.md`; `docs/integrations/CODEX-SECURITY-AUDIT.md`; `docs/integrations/QUICK-START-CODEX.md`; `docs/agents/*`; `tests/agents/agent-mcp-boundary-smoke.test.ts`; package scripts with `codex:` and `mcp:` prefixes. | Treat agents as producer surfaces, not as the product boundary. |
| Security Assurance Lane | ready | `docs/security/security-assurance-lane.md`; schemas `security-*-v1`; package scripts `security:import-speca`, `security:extract-claims`, `security:map-code`, `security:proof-audit`, `security:review`, and `security:audit-prompt`; fixtures and tests. | Security assumptions, candidate findings, and confirmed vulnerabilities must remain distinct. |
| End-to-end assurance fixture | ready | `fixtures/assurance-e2e/inventory-waiver/*`; package script `assurance:e2e`; `scripts/assurance/run-e2e-scenario.mjs`; `tests/scripts/assurance-e2e-scenario.test.ts`. | Use this fixture for smoke-level canonical-route regression; do not make heavy formal verification part of the smoke scenario. |
| Current-state reporting | ready | This file records branch/HEAD evidence and supersedes the older `cb307e05` baseline. | Refresh when control-plane route semantics or contract states materially change. |

### 7. Command / artifact / schema / workflow map

| Area | Command or workflow | Primary artifacts | Schema / contract | Tests or validation evidence |
| --- | --- | --- | --- | --- |
| Context Pack | `pnpm run context-pack:validate`; `pnpm run context-pack:verify-*` | Context Pack reports and fixture evidence | Context Pack docs and fixture conventions | Context Pack fixture scripts and docs under `docs/agents/` / `docs/guides/` |
| Verify Lite | `pnpm run verify:lite`; `.github/workflows/verify-lite.yml` | `artifacts/verify-lite/verify-lite-run-summary.json` | `schema/verify-lite-run-summary.schema.json` | `tests/scripts/run-verify-lite-local.test.ts`; `tests/unit/ci/write-verify-lite-summary.test.ts` |
| Assurance summary | `pnpm run verify:assurance` | `artifacts/assurance/assurance-summary.json` | `schema/assurance-summary.schema.json` | `tests/contracts/assurance-summary-contract.test.ts`; `tests/unit/ci/validate-assurance-summary.test.ts` |
| Claim evidence | `pnpm run claim-evidence:generate` | `artifacts/assurance/claim-evidence-manifest.json`; Markdown sidecar | `schema/claim-evidence-manifest.schema.json` | `tests/contracts/claim-evidence-manifest-contract.test.ts`; `tests/scripts/claim-evidence-manifest.test.ts` |
| Claim-level summary | `pnpm run claim-level-summary:generate` | `artifacts/assurance/claim-level-summary.json`; review Markdown | `schema/claim-level-summary-v1.schema.json` | `tests/scripts/claim-level-summary.test.ts`; assurance-control-plane contract tests |
| Formal aggregate | `pnpm run formal:summary`; `.github/workflows/formal-aggregate.yml` | Formal aggregate / summary JSON | `schema/formal-summary-v1.schema.json`; `schema/formal-summary-v2.schema.json` | `tests/unit/ci/validate-formal-summary-v2.test.ts`; formal tests |
| Conformance | `pnpm run conformance:verify:sample`; `pnpm run conformance:report` | Conformance verify result and reports | `schema/conformance-verify-result.schema.json` | `tests/conformance/*`; `tests/unit/cli/conformance-ingest.test.ts` |
| Quality scorecard | `pnpm run quality:scorecard:v1`; `pnpm run quality:scorecard:validate` | `artifacts/quality/quality-scorecard.json` | `schema/quality-scorecard.schema.json` | `tests/contracts/quality-scorecard-contract.test.ts`; `tests/scripts/build-quality-scorecard.test.ts` |
| Policy gate | `.github/workflows/policy-gate.yml`; `scripts/ci/policy-gate.mjs` | `artifacts/ci/policy-input-v1.json`; `artifacts/ci/policy-decision-js-v1.json`; `artifacts/ci/policy-gate-summary.json` | `schema/policy-input-v1.schema.json`; `schema/policy-decision-v1.schema.json`; `schema/policy-gate-summary-v1.schema.json` | `tests/unit/ci/policy-gate.test.ts`; `tests/unit/ci/policy-shadow-compare.test.ts` |
| Change package | `pnpm run change-package:generate`; `pnpm run change-package:generate:v2`; `pnpm run change-package:validate:v2` | `artifacts/change-package/change-package.json`; `artifacts/change-package/change-package-v2.json`; `artifacts/change-package/change-package-v2.md` | `schema/change-package.schema.json`; `schema/change-package-v2.schema.json` | `tests/contracts/change-package-v2-contract.test.ts`; `tests/unit/ci/change-package-*.test.ts` |
| Contract governance | `pnpm run check:assurance-contract-governance` | Governance check output | `docs/reference/SCHEMA-GOVERNANCE.md`; contract catalog conventions | `tests/unit/assurance/check-contract-governance.test.ts` |
| Security assurance | `pnpm run test:security-assurance`; package scripts with `security:` prefix | Security claims, findings, code map, review, prompt pack, summaries | `schema/security-*-v1.schema.json` | `tests/contracts/security-assurance-contract.test.ts`; `tests/unit/security-assurance/*` |
| Agent / Codex / MCP | package scripts with `codex:` and `mcp:` prefixes | Codex responses, MCP interactions, prompt packs | `fixtures/codex/*`; integration schemas | `tests/codex/*`; `tests/agents/agent-mcp-boundary-smoke.test.ts`; `tests/services/mcp-server.test.ts` |

### 8. Canonical-route and compatibility table

| Topic | Current route state | Evidence | Residual risk / control |
| --- | --- | --- | --- |
| Quality scorecard | Canonical v1 route with legacy wrapper retained. | `docs/reference/ASSURANCE-CANONICAL-ROUTES.md`; `quality:scorecard:v1`; `quality:scorecard`; #3333. | Do not remove the wrapper until consumer-path tests and migration guidance are explicit. |
| Formal summary consumption | Canonical aggregate formal evidence preferred; legacy fallback retained. | `scripts/summary/render-pr-summary.mjs`; `docs/quality/pr-summary.md`; #3334. | Render compatibility as fallback, not as preferred proof route. |
| Counterexample GWT | Derived from canonical formal counterexample evidence. | `docs/quality/counterexample-gwt.md`; #3335. | Keep model scope and source artifact references visible. |
| Change package | v1 production route plus proof-carrying v2 preview / dual-write route. | `docs/reference/change-package-v2.md`; `schema/change-package-v2.schema.json`; #3337. | Explicit migration notes are required for contract-impacting changes. |
| Assurance E2E smoke route | `claim-level-summary/v1 -> policy-decision/v1 -> change-package/v2` for the inventory-waiver scenario. | `fixtures/assurance-e2e/inventory-waiver/README.md`; `tests/scripts/assurance-e2e-scenario.test.ts`; #3338. | Keep the smoke deterministic and non-heavy; it is not a full formal verification run. |

### 9. Over-claiming risk table

| Risk | Current state | Control to preserve |
| --- | --- | --- |
| Treating green CI as high assurance | Docs and summaries distinguish verification lanes, assurance levels, and evidence states. | Keep PR/release summaries from equating pass/fail CI with achieved assurance level. |
| Treating runtime mitigation as proof | The assurance model and change-package v2 distinguish runtime controls from proof/model-check evidence. | Render runtime controls and residual risks separately. |
| Treating waived claims as satisfied claims | E2E fixtures include waived and report-only states; generated change-package v2 now includes policy decision context. | Surface waiver owner/reason/expiry and avoid counting waived as satisfied. |
| Treating preview contracts as mandatory production contracts | `change-package/v2`, `claim-level-summary/v1`, and `temporary-override/v1` are preview or dual-write where documented. | Require separate policy issues for enforcement or default-production promotion. |
| Treating compatibility routes as canonical | Canonical route docs and regression tests distinguish preferred routes from legacy fallbacks. | Keep compatibility text until consumer-path tests justify removal. |
| Treating producer agents as the product boundary | Integration docs and policy frame agents as producers. | Keep durable contracts at the control-plane boundary. |
| Treating security assumption findings as confirmed vulnerabilities | Security Assurance Lane keeps assumptions, candidate findings, and reviews distinct. | Preserve those distinctions when mapping security artifacts into claim evidence. |

### 10. Current follow-up guidance

The next work should be narrowly scoped maintenance rather than another broad roadmap:

1. Keep `docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md` as the canonical snapshot and refresh it when HEAD evidence materially changes.
2. Keep `docs/reference/SCHEMA-GOVERNANCE.md` and `pnpm run check:assurance-contract-governance` aligned with new assurance schemas.
3. Continue preferring canonical route tests before changing compatibility behavior.
4. Require explicit `contractMigrationNotes` and consumer-impact text for assurance contract changes.
5. Avoid treating report-only policy-gate output as enforcement unless a dedicated policy issue changes the mode.

### 11. 日本語要約

このレポートは、`main` の `a4245f693bff38229bf6431f27fbf3d20266d259` を対象に、assurance control plane の現状を再記録します。以前の `cb307e05` ベースラインは現行状態ではなく、#3302〜#3312 / PR #3313〜#3322 は完了済みの履歴として扱います。

現在のリポジトリには、policy、detailed design、contract catalog、canonical route、schema governance、claim/evidence producer、policy-gate summary、change-package v1/v2、PR summary、E2E fixture、Security Assurance Lane が存在します。今後の主眼は、新しい大規模ロードマップの作成ではなく、正準導線の維持、互換導線の安全な移行、契約変更時の migration note、current-state report の鮮度維持です。

別ファイルの repository snapshot は追加していません。本レポートが、HEAD、command inventory、contract inventory、route state、残余フォローアップをまとめて記録する canonical snapshot として機能します。
