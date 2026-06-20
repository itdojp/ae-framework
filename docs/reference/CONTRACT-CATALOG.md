---
docRole: ssot
lastVerified: '2026-06-20'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Contract Catalog (Issue #2406 Foundation)

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This document is the baseline inventory created for Issue #2406. It classifies the current `schema/*.schema.json` set by contract role and serves as the starting point for later `schemaVersion` unification and dual-write / dual-validate operations.

### 2. Contract domains (primary role)

- `input`: contracts supplied before execution, such as requirement bundles, configuration, or model definitions
- `decision`: contracts emitted as execution judgements, such as pass/fail, block reasons, or priority
- `evidence`: audit, reproducibility, and observability artifacts, such as summaries, reports, and metrics
- `operation`: contracts that control execution planning and orchestration, such as plans, manifests, and packages

Some schemas are dual-role. This catalog records the primary role used in the current implementation.

### 3. Schema inventory (snapshot: 2026-06-05)

#### 3.1 input

- `schema/assurance-profile.schema.json`
- `schema/codex-task-request.schema.json`
- `schema/context-bundle.schema.json`
- `schema/discovery-pack-v1.schema.json`
- `schema/context-pack-v1.schema.json`
- `schema/context-pack-boundary-map.schema.json`
- `schema/context-pack-functor-map.schema.json`
- `schema/context-pack-natural-transformation.schema.json`
- `schema/context-pack-phase5-templates.schema.json`
- `schema/context-pack-product-coproduct.schema.json`
- `schema/context-pack-suggestions.schema.json`
- `schema/ae-handoff.schema.json`
- `schema/flow.schema.json`
- `schema/formal-plan.schema.json`
- `schema/issue-traceability-map.schema.json`
- `schema/policy-input-v1.schema.json`
- `schema/security-audit-scope-v1.schema.json`
- `schema/security-claim-v1.schema.json`
- `schema/security-threat-model-v1.schema.json`
- `schema/release-policy.schema.json`
- `schema/state-machine.schema.json`
- `schema/trace-map.schema.json`

#### 3.2 decision

- `schema/codex-task-response.schema.json`
- `schema/conformance-report.schema.json`
- `schema/conformance-verify-result.schema.json`
- `schema/hook-feedback.schema.json`
- `schema/producer-normalization-summary.schema.json`
- `schema/issue-traceability-matrix.schema.json`
- `schema/policy-decision-v1.schema.json`
- `schema/pr-state-v1.schema.json`
- `schema/policy-gate-summary-v1.schema.json`
- `schema/temporary-override-v1.schema.json`
- `schema/security-review-v1.schema.json`
- `schema/quality-report.schema.json`
- `schema/trace-validation.schema.json`
- `schema/verify-profile-summary.schema.json`

#### 3.3 evidence

- `schema/agentic-metrics.schema.json`
- `schema/automation-observability-v1.schema.json`
- `schema/artifact-metadata.schema.json`
- `schema/ci-artifact-provenance-v1.schema.json`
- `schema/assurance-summary.schema.json`
- `schema/claim-evidence-manifest.schema.json`
- `schema/claim-level-summary-v1.schema.json`
- `schema/context-pack-boundary-map-summary.schema.json`
- `schema/security-code-map-v1.schema.json`
- `schema/symbol-index-v1.schema.json`
- `schema/security-entrypoint-map-v1.schema.json`
- `schema/security-audit-task-bundle-v1.schema.json`
- `schema/security-audit-prompt-pack-v1.schema.json`
- `schema/security-finding-v1.schema.json`
- `schema/temporal-run-summary.schema.json`
- `schema/bench-criteria.schema.json`
- `schema/bench-compare.schema.json`
- `schema/benchmark-report.schema.json`
- `schema/conformance-metrics.schema.json`
- `schema/counterexample.schema.json`
- `schema/envelope.schema.json`
- `schema/formal-summary-v1.schema.json`
- `schema/formal-summary-v2.schema.json`
- `schema/harness-health.schema.json`
- `schema/license-scope-audit.schema.json`
- `schema/conditional-asset-audit.schema.json`
- `schema/notice-readiness-audit.schema.json`
- `schema/contributor-license-readiness-audit.schema.json`
- `schema/third-party-notice-candidate-audit.schema.json`
- `schema/apache-license-cutover-readiness-audit.schema.json`
- `schema/apache-license-cutover-approval-readiness-audit.schema.json`
- `schema/quality-scorecard.schema.json`
- `schema/report-envelope.schema.json`
- `schema/spec-validation-report.schema.json`
- `schema/trace-bundle.schema.json`
- `schema/trace-bundle-summary.schema.json`
- `schema/ui-e2e-summary.schema.json`
- `schema/usefulness-evaluation-report.schema.json`
- `schema/verify-lite-run-summary.schema.json`

#### 3.4 operation

- `schema/change-package.schema.json`
- `schema/change-package-v2.schema.json`
- `schema/execplan.schema.json`
- `schema/execution-plan-v1.schema.json`
- `schema/plan-artifact.schema.json`
- `schema/run-manifest.schema.json`

### 4. Produced/consumed mapping for major artifacts

The table below keeps the current producer/consumer baseline for representative artifacts. Producer and consumer columns intentionally use implementation entry points rather than abstract ownership labels.

| artifact (path/pattern) | schema | producer (primary) | consumer (primary) |
| --- | --- | --- | --- |
| `artifacts/verify-lite/verify-lite-run-summary.json` | `schema/verify-lite-run-summary.schema.json` | `scripts/ci/write-verify-lite-summary.mjs`, `.github/workflows/verify-lite.yml` | `scripts/ci/validate-verify-lite-summary.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `spec/discovery-pack/**/*.{yml,yaml,json}` | `schema/discovery-pack-v1.schema.json` | manual authoring in `spec/discovery-pack/` | `scripts/discovery-pack/validate.mjs`, `scripts/discovery-pack/compile.mjs`, `src/cli/discovery-cli.ts` |
| `artifacts/discovery-pack/discovery-pack-validate-report.json` | dedicated schema not yet defined (`contractId=discovery-pack-validation-report.v1`) | `scripts/discovery-pack/validate.mjs`, `.github/workflows/verify-lite.yml` | `docs/spec/discovery-pack.md`, `scripts/summary/render-pr-summary.mjs`, CI Step Summary / PR comment operators |
| `artifacts/discovery-pack/discovery-pack-compile-report.json` | dedicated schema not yet defined (`contractId=discovery-pack-compile-report.v1`) | `scripts/discovery-pack/compile.mjs`, `.github/workflows/verify-lite.yml` (dry-run in strict mode) | `docs/spec/discovery-pack.md`, `scripts/summary/render-pr-summary.mjs`, operator review before SSOT promotion |
| `artifacts/discovery-pack/plan-to-spec-normalized.md` | non-authoritative Markdown (no schema) | `scripts/discovery-pack/compile.mjs` (`--target plan-spec`), `src/cli/discovery-cli.ts` | `ae tests:scaffold --input ...`, human review before repo SSOT promotion |
| `artifacts/discovery-pack/context-pack-scaffold.yaml` | `schema/context-pack-v1.schema.json` (scaffold-compatible, non-authoritative) | `scripts/discovery-pack/compile.mjs` (`--target context-pack-scaffold`), `src/cli/discovery-cli.ts` | manual editing before Context Pack SSOT promotion, future Context Pack validation |
| `artifacts/context-pack/boundary-map-summary.json` | `schema/context-pack-boundary-map-summary.schema.json` | `scripts/context-pack/verify-boundary-map.mjs` (`pnpm run context-pack:verify-boundary-map`) | PR evidence review, future policy-gate / assurance-summary ingestion; `status=ok/drift/skipped/unresolved` keeps drift as a report-only design-boundary evidence gap unless later policy selects enforcement |
| `artifacts/assurance/assurance-summary.json` | `schema/assurance-summary.schema.json` | `scripts/assurance/aggregate-lanes.mjs`, `.github/workflows/verify-lite.yml`; optional `security-claim/v1`, `security-finding/v1`, `security-review/v1`, `producer-normalization-summary/v1`, `context-pack-boundary-map-summary/v1`, `claim-evidence-manifest/v1`, and `policy-decision/v1` inputs surface lane evidence plus `reviewSurface` for PR review | `scripts/ci/validate-assurance-summary.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/ci/validate-json.mjs`, `scripts/ci/enforce-assurance-summary.mjs`, `scripts/quality/build-quality-scorecard.mjs`, `scripts/agents/build-hook-feedback.mjs`, `scripts/agents/create-handoff.mjs`, `scripts/summary/render-pr-summary.mjs`, `.github/workflows/pr-ci-status-comment.yml`; `reviewSurface` is report-only and does not approve merge by itself |
| `artifacts/assurance/claim-evidence-manifest.json` | `schema/claim-evidence-manifest.schema.json` | `scripts/assurance/build-claim-evidence-manifest.mjs`, `.github/workflows/verify-lite.yml`, `fixtures/assurance/sample.claim-evidence-manifest.json` (schema contract fixture); optional `security-claim/v1`, `security-finding/v1`, and `security-review/v1` inputs are summarized under `summary.security`, preserve original security IDs in claim/evidence `externalIds`, and expose assumption handling through `securityClaimType` / `assumptionHandlingRefs` | `scripts/ci/validate-json.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, `tests/contracts/claim-evidence-manifest-contract.test.ts`, `scripts/summary/render-pr-summary.mjs`, `scripts/ci/policy-gate.mjs`, `.github/workflows/pr-ci-status-comment.yml`; primary claim status remains `satisfied` / `partial` / `waived` / `unresolved`, while review-state counts such as `behavior/tested`, `model/model-checked`, `proof/proved`, and `runtime/runtime-mitigated` are displayed separately |
| `artifacts/assurance/claim-level-summary.json` | `schema/claim-level-summary-v1.schema.json` | `scripts/assurance/aggregate-claim-levels.mjs`, `pnpm run claim-level-summary:generate`, and fixture-backed preview projection from `claim-evidence-manifest/v1`, `policy-gate-summary/v1`, optional `change-package/v2`, and `temporary-override/v1`; `fixtures/assurance/claim-level-summary/expected/claim-level-summary.json` covers satisfied, tested, model-checked, proved, runtime-mitigated, waived, unresolved, failed, and not-applicable states | `scripts/ci/validate-json.mjs`, `tests/contracts/assurance-control-plane-schema-contract.test.ts`, `tests/scripts/claim-level-summary.test.ts`, future PR/release summary renderers; this preview does not change the `claim-evidence-manifest/v1` claim-status vocabulary or `change-package/v2` package/release outcome statuses |
| `artifacts/assurance/temporary-overrides/*.json` | `schema/temporary-override-v1.schema.json` | Manual or policy-owner waiver records; `fixtures/assurance/sample.temporary-override-v1.json` is the schema contract fixture | `scripts/ci/validate-json.mjs`, `tests/contracts/assurance-control-plane-schema-contract.test.ts`, future claim-level summaries and policy-gate waiver projections; requires owner, reason, expiry, related claim IDs, and evidence link |
| `artifacts/security/security-claims.json` | `schema/security-claim-v1.schema.json` | manual authoring, `ae security import-speca`, `ae security extract-claims`, `fixtures/security-assurance/sample.security-claims.json` (schema contract fixture) | `ae security map-code`, future Security Assurance Lane producers, `scripts/ci/validate-json.mjs`, `tests/contracts/security-assurance-contract.test.ts`; downstream artifacts reference `claims[].id` |
| `artifacts/security/security-threat-model.json` | `schema/security-threat-model-v1.schema.json` | manual authoring, `ae security import-speca`, `fixtures/security-assurance/sample.security-threat-model.json` (schema contract fixture) | future security audit and review producers, `scripts/ci/validate-json.mjs`, `tests/contracts/security-assurance-contract.test.ts`; references security claim ids through `threats[].relatedClaimIds[]` |
| `artifacts/security/security-audit-scope.json` | `schema/security-audit-scope-v1.schema.json` | manual authoring, bug-bounty/audit scope translation, `fixtures/security-assurance/sample.security-audit-scope.json` (schema contract fixture) | future security claim extraction, code-map, audit, and review producers; scope remains glob-based in the MVP contract |
| `artifacts/security/security-code-map.json` | `schema/security-code-map-v1.schema.json` | `ae security map-code` (optionally consuming `symbol-index/v1` via `--symbol-index`), `fixtures/security-assurance/sample.security-code-map.json` (schema contract fixture) | `ae security audit`, `scripts/ci/validate-json.mjs`, `tests/contracts/security-assurance-contract.test.ts`; maps security claim ids to candidate source locations without treating them as findings |
| `artifacts/code/symbol-index.json` | `schema/symbol-index-v1.schema.json` | manual authoring or external deterministic symbol-index producers, `fixtures/security-assurance/sample.symbol-index.json` (schema contract fixture) | optional input to `ae security map-code --symbol-index`, `scripts/ci/validate-json.mjs`, `tests/contracts/security-assurance-contract.test.ts`; records symbol metadata only, not call graph or dataflow proof |
| `artifacts/security/security-entrypoint-map.json` | `schema/security-entrypoint-map-v1.schema.json` | manual authoring or external deterministic entrypoint-map producers, `fixtures/security-assurance/sample.security-entrypoint-map.json` (schema contract fixture) | optional input to `ae security review --entrypoint-map`, `scripts/ci/validate-json.mjs`, `tests/contracts/security-assurance-contract.test.ts`; records entrypoint reachability hints only, not full call graph or dataflow proof |
| `artifacts/security/security-audit-tasks.json` | `schema/security-audit-task-bundle-v1.schema.json` | `ae security audit`, `fixtures/security-assurance/sample.security-audit-tasks.json` (schema contract fixture) | `ae security audit-prompt`, fixture-backed proof-attempt normalization, human security review, `scripts/ci/validate-json.mjs`, `tests/contracts/security-assurance-contract.test.ts`; task bundles are prompt inputs, not findings |
| `artifacts/security/codex-audit-prompts/security-audit-prompt-pack.json` | `schema/security-audit-prompt-pack-v1.schema.json` | `ae security audit-prompt`, `fixtures/security-assurance/sample.security-audit-prompt-pack.json` (schema contract fixture) | Codex CLI / human reviewer prompt input; deterministic Markdown prompts under `artifacts/security/codex-audit-prompts/prompts/`; no external LLM or network execution |
| `artifacts/security/security-findings.json` | `schema/security-finding-v1.schema.json` | `ae security audit`, `ae security import-speca`, `fixtures/security-assurance/sample.security-findings.json` (schema contract fixture) | `ae security review`, `scripts/assurance/aggregate-lanes.mjs`, `scripts/assurance/build-claim-evidence-manifest.mjs`, and policy-gate report-only summaries; `status=candidate` is not a confirmed vulnerability |
| `artifacts/security/security-review.json` | `schema/security-review-v1.schema.json` | `ae security review` (optionally consuming `security-claim/v1` via `--claims` and `security-entrypoint-map/v1` via `--entrypoint-map`), `ae security import-speca`, `fixtures/security-assurance/sample.security-review.json` (schema contract fixture) | `scripts/assurance/aggregate-lanes.mjs`, `scripts/assurance/build-claim-evidence-manifest.mjs`, `scripts/summary/render-pr-summary.mjs`, and policy-gate report-only summaries; captures severity-preserving Dead Code / Trust Boundary / Scope gates, false-positive root-cause classification, claim type, and assumption handling |
| `artifacts/temporal/*/temporal-run-summary.json` | `schema/temporal-run-summary.schema.json` | `examples/temporal-workflow-adapter`, `fixtures/temporal/sample.temporal-run-summary.json` (schema contract fixture) | `scripts/ci/validate-json.mjs`, `tests/contracts/temporal-run-summary-contract.test.ts`, operator review; Temporal-specific metadata remains confined to this adapter sidecar |
| `spec/assurance-profile/upstream-context-promotion-v1.json` | `schema/assurance-profile.schema.json` | manual authoring in `spec/assurance-profile/` | `scripts/assurance/aggregate-lanes.mjs`, `docs/guides/upstream-context-promotion.md`, `tests/fixtures/upstream-context-promotion-minimal.assurance.test.ts` |
| `artifacts/report-envelope.json` | `schema/envelope.schema.json` | `scripts/trace/create-report-envelope.mjs` | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/trace/publish-envelope.mjs` |
| `artifacts/trace/report-envelope.json` | `schema/envelope.schema.json` | `scripts/trace/create-report-envelope.mjs` (including copy-based operation) | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/trace/post-envelope-comment.mjs` |
| `artifacts/formal/formal-summary-v1.json` | `schema/formal-summary-v1.schema.json` | `scripts/formal/generate-formal-summary-v1.mjs` (`--out`), `.github/workflows/verify-lite.yml`, `.github/workflows/formal-aggregate.yml` | `scripts/ci/validate-formal-summary-v1.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/ci/generate-run-manifest.mjs` |
| `artifacts/formal/formal-summary-v2.json` | `schema/formal-summary-v2.schema.json` | `scripts/formal/generate-formal-summary-v1.mjs` (`--out-v2`), `.github/workflows/verify-lite.yml`, `.github/workflows/formal-aggregate.yml` | `scripts/ci/validate-formal-summary-v2.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/ci/generate-run-manifest.mjs` |
| `artifacts/reference/benchmarks/bench.json` | `schema/benchmark-report.schema.json` | `src/commands/bench/run.ts` (`ae bench`) | `tests/scripts/benchmark-report-schema.test.ts`, `scripts/quality/bench-compare.mjs` |
| `configs/bench-criteria.default.json` | `schema/bench-criteria.schema.json` | `configs/bench-criteria.default.json` (repo default), `scripts/quality/bench-compare.mjs` (`when --criteria` is omitted) | `scripts/quality/bench-compare.mjs`, `tests/scripts/bench-compare.test.ts` |
| `artifacts/bench-compare.json` | `schema/bench-compare.schema.json` | `scripts/quality/bench-compare.mjs` | `tests/scripts/bench-compare-schema.test.ts`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `artifacts/conformance/conformance-results.json` | `schema/conformance-verify-result.schema.json` | `src/cli/conformance-cli.ts` (`ae conformance verify`) | `src/cli/conformance-report.ts`, `scripts/formal/verify-conformance.mjs` |
| `artifacts/hermetic-reports/conformance/summary.json` | `schema/conformance-report.schema.json` | `scripts/formal/verify-conformance.mjs` | `scripts/change-package/generate.mjs`, `scripts/ci/validate-json.mjs` |
| `artifacts/observability/trace-bundle.json` | `schema/trace-bundle.schema.json` | `src/cli/conformance-cli.ts` (`ae conformance ingest`) | `src/cli/conformance-cli.ts` (`ae conformance verify --trace-bundle`) |
| `artifacts/hermetic-reports/trace/**/kvonce-validation.json` | `schema/trace-validation.schema.json` | `scripts/trace/run-kvonce-conformance.sh` | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/trace/render-trace-summary.mjs` |
| `artifacts/change-package/change-package.json` | `schema/change-package.schema.json` | `scripts/change-package/generate.mjs` | `scripts/change-package/validate.mjs`, `.github/workflows/pr-ci-status-comment.yml` |
| `artifacts/handoff/ae-handoff.json` | `schema/ae-handoff.schema.json` | `scripts/agents/create-handoff.mjs`, `templates/comments/AE-HANDOFF.md`(manual/export), `docs/agents/handoff.md` | `scripts/agents/validate-handoff.mjs`, future PR/Issue handoff consumers |
| `artifacts/agents/hook-feedback.json` | `schema/hook-feedback.schema.json` | `scripts/agents/build-hook-feedback.mjs`, `.github/workflows/pr-ci-status-comment.yml` | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/agents/create-handoff.mjs`, `docs/agents/hook-feedback.md`, Claude Code / Codex continuation consumers |
| `artifacts/agents/producer-normalization-summary.json` | `schema/producer-normalization-summary.schema.json` | `scripts/agents/normalize-producer-output.mjs`, `fixtures/agents/evidence-adapters/*.json`; `fixtures/agents/producer-normalization-summary.codex.json` is the schema contract fixture | `scripts/ci/validate-json.mjs`, future PR summary / policy-gate report-only context; records raw producer assertions, missing evidence, known gaps, and expected routing without emitting pass/proved/approved judgment |
| `artifacts/agents/agent-pr-assurance-metrics.json` | `schema/agentic-metrics.schema.json` (`agentPrAssurance` extension) | Optional agent PR assurance metrics producer / future PR assurance collector; `fixtures/agentic-metrics/agent-pr-assurance-metrics.example.json` is the contract fixture | `scripts/ci/validate-json.mjs` and future quality-scorecard / PR-summary consumers when wired; role=observability/evidence, enforcement=report-only, not mandatory for every PR, and no policy-gate block condition is added |
| `artifacts/plan/plan-artifact.json` | `schema/plan-artifact.schema.json` | `scripts/plan-artifact/generate.mjs` | `scripts/plan-artifact/validate.mjs`, `scripts/ci/policy-gate.mjs`, `.github/workflows/pr-ci-status-comment.yml`, `.github/workflows/policy-gate.yml` |
| `artifacts/ci/policy-input-v1.json` | `schema/policy-input-v1.schema.json` | `scripts/ci/policy-gate.mjs`, `.github/workflows/policy-gate.yml` | `scripts/ci/policy-gate.mjs`, `scripts/ci/policy-shadow-compare.mjs`, `scripts/ci/validate-json.mjs`; optional `assurance` section normalizes `claim-evidence-manifest/v1`, including `summary.security` report-only finding counts, for waiver-aware decisions |
| `artifacts/ci/policy-decision-js-v1.json`, `artifacts/ci/policy-decision-opa-v1.json` | `schema/policy-decision-v1.schema.json` | `scripts/ci/policy-gate.mjs`, `scripts/ci/policy-shadow-compare.mjs`, `.github/workflows/policy-gate.yml` | `scripts/ci/policy-shadow-compare.mjs`, `scripts/ci/validate-json.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`; JS decision records waiver-aware `pass` / `waived` / `report-only` / `block` assurance results, report-only security finding counts, and optional agent assurance findings with source artifact paths |
| `artifacts/ci/policy-shadow-compare-v1.json` | dedicated schema not yet defined (`contractId=policy-shadow-compare.v1`) | `scripts/ci/policy-shadow-compare.mjs`, `.github/workflows/policy-gate.yml` | `docs/ci/pr-automation.md`, `docs/ci/label-gating.md` |
| `artifacts/ci/policy-gate-summary.json` | `schema/policy-gate-summary-v1.schema.json` | `scripts/ci/policy-gate.mjs`, `.github/workflows/policy-gate.yml` | `scripts/ci/validate-policy-gate-summary.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`; optional `evaluation.assurance.agentAssuranceFindings` surfaces producer / assurance-summary findings as report-only evidence with count, severity, and source artifact path |
| `artifacts/**/*.provenance.json` | `schema/ci-artifact-provenance-v1.schema.json` | `scripts/ci/write-artifact-provenance.mjs`; CI decision and publisher workflows including Policy Gate, PR Maintenance, Quality Gates, SBOM, and formal aggregate producers | `scripts/ci/validate-artifact-provenance.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, trusted workflow-run publishers; binds subject digests to producer repository, workflow ref, run id, run attempt, PR number, and head SHA |
| `artifacts/ci/harness-health.json` | `schema/harness-health.schema.json` | `scripts/ci/build-harness-health.mjs`, `.github/workflows/pr-ci-status-comment.yml`, `.github/workflows/ci-extended.yml` | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/ci/validate-json.mjs`, `scripts/agents/build-hook-feedback.mjs`, `scripts/change-package/generate.mjs` |
| `artifacts/quality/quality-scorecard.json` | `schema/quality-scorecard.schema.json` | `scripts/quality/build-quality-scorecard.mjs`, `.github/workflows/verify-lite.yml` | `scripts/ci/validate-quality-scorecard.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/ci/validate-json.mjs`, `scripts/summary/render-pr-summary.mjs`, `.github/workflows/pr-ci-status-comment.yml` |
| `artifacts/reference/legal/license-scope-audit.json` | `schema/license-scope-audit.schema.json` | `scripts/legal/inventory-license-scope.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/LICENSE-MIGRATION-AUDIT.md`, downstream legal audit builders |
| `artifacts/reference/legal/conditional-asset-audit.json` | `schema/conditional-asset-audit.schema.json` | `scripts/legal/inventory-conditional-assets.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/CONDITIONAL-ASSET-PROVENANCE-AUDIT.md`, downstream legal audit builders |
| `artifacts/reference/legal/notice-readiness-audit.json` | `schema/notice-readiness-audit.schema.json` | `scripts/legal/build-notice-readiness.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/NOTICE-READINESS-AUDIT.md`, operator/legal review before `NOTICE` cutover |
| `artifacts/reference/legal/contributor-license-readiness-audit.json` | `schema/contributor-license-readiness-audit.schema.json` | `scripts/legal/build-contributor-license-readiness.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/CONTRIBUTOR-LICENSE-READINESS.md`, human/legal contributor review before relicensing |
| `artifacts/reference/legal/third-party-notice-candidate-audit.json` | `schema/third-party-notice-candidate-audit.schema.json` | `scripts/legal/build-third-party-notice-candidate-audit.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/THIRD-PARTY-NOTICE-CANDIDATES-AUDIT.md`, human/legal review before third-party notice cutover |
| `artifacts/reference/legal/apache-license-cutover-readiness-audit.json` | `schema/apache-license-cutover-readiness-audit.schema.json` | `scripts/legal/build-apache-license-cutover-readiness.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/APACHE-LICENSE-CUTOVER-READINESS.md`, final cutover readiness review before replacing `LICENSE` |
| `artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.json` | `schema/apache-license-cutover-approval-readiness-audit.schema.json` | `scripts/legal/build-apache-license-cutover-approval-readiness.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-READINESS.md`, final approval completeness review before opening the cutover PR |
| `artifacts/ci/automation-report.json` | `schema/automation-observability-v1.schema.json` | `scripts/ci/lib/automation-report.mjs`, `.github/workflows/codex-autopilot-lane.yml` | `scripts/ci/validate-automation-report.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `artifacts/ci/pr-state-v1.json` | `schema/pr-state-v1.schema.json` | `scripts/ci/codex-autopilot-lane.mjs` | `scripts/ci/validate-json.mjs`, `docs/ci/codex-autopilot-lane.md` |
| `artifacts/ci/execution-plan-v1.json` | `schema/execution-plan-v1.schema.json` | `scripts/ci/codex-autopilot-lane.mjs` | `scripts/ci/validate-json.mjs`, `docs/ci/codex-autopilot-lane.md` |
| `artifacts/e2e/ui-e2e-summary.json` | `schema/ui-e2e-summary.schema.json` | `scripts/e2e/run-ui-e2e-semantic.mjs`, `.github/workflows/parallel-test-execution.yml` | `scripts/ci/build-harness-health.mjs`, `scripts/ci/validate-json.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `artifacts/e2e/summary.json` | `docs/schemas/artifacts-adapter-summary.schema.json` | `scripts/e2e/run-ui-e2e-semantic.mjs` | `scripts/ci/validate-artifacts-ajv.mjs`, future adapter-summary aggregators |

### 4.1 Canonical and legacy route markers

The produced/consumed table lists implementation entry points. When more than one route exists, use `docs/reference/ASSURANCE-CANONICAL-ROUTES.md` to decide whether a route is canonical, preview, or legacy compatibility. Current cleanup markers are:

| Topic | Canonical route | Compatibility route | Cleanup status |
| --- | --- | --- | --- |
| Quality scorecard | `quality-scorecard/v1`, `scripts/quality/build-quality-scorecard.mjs`, `pnpm run quality:scorecard:v1`, `schema/quality-scorecard.schema.json` | `pnpm run quality:scorecard`, `scripts/quality-scorecard-generator.js` | Compatibility script delegates to v1 only when both required inputs are supplied; `--legacy` / `--legacy-diagnostic` force legacy diagnostics until workflow consumers have v1 input wiring tests. |
| Formal status | `artifacts/formal/formal-summary-v2.json` plus dual-write `artifacts/formal/formal-summary-v1.json`; aggregate `artifacts/hermetic-reports/formal/summary.json` | `formal/summary.json` | Keep as final compatibility input only; PR summary rendering reads formal-summary v2/v1 and the hermetic aggregate before this fallback. |
| Counterexample GWT | `artifacts/formal/gwt.summary.json`, derived by `scripts/formal/format-counterexamples.mjs` from canonical aggregate/tool evidence that embeds counterexamples | Counterexamples embedded in `formal/summary.json` | Derived aid only; not a primary formal status contract. Legacy counterexamples remain the final fallback. |
| PR summary judgment | `scripts/summary/render-pr-summary.mjs` plus `pr-ci-status-comment.yml` append stage | Hand-authored or older bot summaries | Keep direct renderer inputs separate from workflow-appended Markdown. |
| Change package | Production `change-package/v1`; proof-carrying preview `change-package/v2` | Direct source artifact fragments | Keep v1 compatibility while v2 is preview / dual-write. |

### 4.2 Agent-output gap audit crosswalk

`docs/reports/AGENT-OUTPUT-CONTRACT-GAP-AUDIT.md` records the ACP producer-routing gap IDs. This catalog remains the artifact inventory; the report is the issue-level gap register.

| Gap ID | Catalog surface | Follow-up |
| --- | --- | --- |
| ACP-GAP-001 | raw producer examples under `fixtures/agents/evidence-adapters/` | ACP-011 / #3482 |
| ACP-GAP-002 | future report-only normalizer that routes raw examples to existing artifacts | ACP-012 / #3483 |
| ACP-GAP-003 | reviewer-facing summaries backed by existing `assurance-summary`, `quality-scorecard`, formal, and verify-lite artifacts | ACP-030 / #3486 |
| ACP-GAP-004 | report-only policy context that may consume normalized agent-assurance findings | ACP-040 / #3488 |
| ACP-GAP-005 | existing dedicated-schema gaps such as `policy-shadow-compare.v1` and selected `artifacts/ci/*-summary.json` sidecars | cataloged contract debt |
| ACP-GAP-006 | vendor-specific raw APIs for BYO agents | documented out of scope |

### 5. Security Assurance Lane status semantics

- `security-audit-task-bundle/v1` records deterministic proof-attempt prompt inputs. It is not vulnerability evidence by itself and does not confirm or reject a claim.
- `security-finding/v1` is candidate-first: `status=candidate` and `status=needs-human-review` are audit evidence, not confirmed vulnerabilities. Only `status=confirmed` represents a confirmed vulnerability.
- `security-review/v1` applies three narrow gates: Dead Code, Trust Boundary, and Scope. Each gate records `pass | fail | unknown | not-applicable` plus a rationale, and producer-generated reviews preserve the finding severity for downstream summaries. When optional `security-entrypoint-map/v1` evidence is supplied, the Trust Boundary gate uses matching entrypoint reachability before falling back to `unknown`; without that input, existing scope-reference behavior is preserved.
- `falsePositiveRootCause` uses `dead-code`, `trust-boundary-misunderstanding`, `out-of-scope`, `code-reading-error`, `spec-misinterpretation`, or `insufficient-evidence` only for resolved false positives (`rejected` or `out-of-scope`); it remains `null` for `needs-human-review`, `confirmed`, and `waived` results.
- Security findings and three-gate reviews now flow into `assurance-summary/v1` and `claim-evidence-manifest/v1`; the manifest keeps canonical lowercase IDs while exposing original `SEC-CLAIM-*` / `SEC-FINDING-*` identifiers through `externalIds`, and policy-gate consumes it in report-only mode to highlight high/critical findings that still need human review without treating candidates as confirmed vulnerabilities.

### 6. Claim-level assurance status routing

- `claim-evidence-manifest/v1` is the evidence-linking manifest. It preserves claim IDs, evidence references, waiver references, and unresolved gaps for policy-gate and summary consumers. Its primary claim status is limited to `satisfied`, `partial`, `waived`, and `unresolved`; review labels such as `tested`, `model-checked`, `proved`, and `runtime-mitigated` remain evidence-state projections.
- `claim-level-summary/v1` is the PR/release projection. It summarizes satisfied, tested, model-checked, proved, runtime-mitigated, waived, unresolved, failed, and not-applicable counts without changing the source manifest contract.
- `policy-decision/v1` records whether claim-level assurance is `pass`, `report-only`, `waived`, or `block` for the active policy mode.
- `risk:high`, `enforce-assurance`, and critical core policy can escalate missing required lanes or unresolved claims; ordinary changes can remain report-only while keeping counts visible.

### 7. Current gaps (next stage)

- assurance contracts are still being introduced in phases; default operation stays report-only, and strict assurance enforcement is limited to Verify Lite when the `enforce-assurance` label is present. `claim-level-summary/v1` and `temporary-override/v1` are preview contracts and are not mandatory producer outputs yet.
- `schemaVersion` still mixes semver and `*/v1` style identifiers. The staged unification plan lives in `docs/reference/SCHEMA-GOVERNANCE.md`.
- `change-package` still runs with `v1` as the production contract while `v2` remains the proof-carrying preview contract.
- Formal Summary still operates in a dual-write + dual-validate period (`v2`: `schemaVersion=formal-summary/v2`, `contractId=formal-summary.v2`).
- `report-envelope` still has two schema lines: `schema/envelope.schema.json` and `schema/report-envelope.schema.json`.
- The following artifacts still need dedicated schema normalization or explicit contract treatment:
  - `artifacts/verify-lite/verify-lite-lint-summary.json`
  - `artifacts/run-manifest-check.json`
  - `artifacts/*-retry-eligibility.json`
  - `artifacts/ci/*-summary.json` (risk and related summaries)

### 8. References

- `docs/reference/SCHEMA-GOVERNANCE.md`
- `docs/reference/ASSURANCE-CANONICAL-ROUTES.md`
- `docs/agents/evidence-adapters.md`
- `docs/reports/AGENT-OUTPUT-CONTRACT-GAP-AUDIT.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/architecture/DELIVERY-CONTRACT-COMPATIBILITY-MATRIX.md`
- `scripts/ci/validate-artifacts-ajv.mjs`
- `scripts/ci/validate-formal-summary-v1.mjs`
- `scripts/ci/validate-formal-summary-v2.mjs`
- `scripts/ci/validate-json.mjs`
- `docs/architecture/PR-STATE-EXECUTION-PLAN-V1-DRAFT.md`

---

## 日本語

## 1. 目的

本ドキュメントは Issue #2406 の初期成果物として、`schema/*.schema.json` の現状を契約分類で棚卸ししたものです。  
以後の `schemaVersion` 統一・dual-write/dual-validate 運用の基礎データとして利用します。

## 2. 契約分類（primary）

- `input`: 実行前に与える入力契約（要件束、設定、モデル定義など）
- `decision`: 実行結果としての判定契約（合否、ブロック理由、優先度）
- `evidence`: 監査・再現・可観測性の証跡契約（summary、report、metrics）
- `operation`: 実行計画や進行制御に関わる運用契約（plan、manifest、package）

## 3. schema 一覧（2026-05-07時点）

### 3.1 input

- `schema/assurance-profile.schema.json`
- `schema/codex-task-request.schema.json`
- `schema/context-bundle.schema.json`
- `schema/discovery-pack-v1.schema.json`
- `schema/context-pack-v1.schema.json`
- `schema/context-pack-boundary-map.schema.json`
- `schema/context-pack-functor-map.schema.json`
- `schema/context-pack-natural-transformation.schema.json`
- `schema/context-pack-phase5-templates.schema.json`
- `schema/context-pack-product-coproduct.schema.json`
- `schema/context-pack-suggestions.schema.json`
- `schema/ae-handoff.schema.json`
- `schema/flow.schema.json`
- `schema/formal-plan.schema.json`
- `schema/issue-traceability-map.schema.json`
- `schema/policy-input-v1.schema.json`
- `schema/security-audit-scope-v1.schema.json`
- `schema/security-claim-v1.schema.json`
- `schema/security-threat-model-v1.schema.json`
- `schema/release-policy.schema.json`
- `schema/state-machine.schema.json`
- `schema/trace-map.schema.json`

### 3.2 decision

- `schema/codex-task-response.schema.json`
- `schema/conformance-report.schema.json`
- `schema/conformance-verify-result.schema.json`
- `schema/hook-feedback.schema.json`
- `schema/producer-normalization-summary.schema.json`
- `schema/harness-health.schema.json`
- `schema/issue-traceability-matrix.schema.json`
- `schema/policy-decision-v1.schema.json`
- `schema/pr-state-v1.schema.json`
- `schema/policy-gate-summary-v1.schema.json`
- `schema/temporary-override-v1.schema.json`
- `schema/security-review-v1.schema.json`
- `schema/quality-report.schema.json`
- `schema/trace-validation.schema.json`
- `schema/verify-profile-summary.schema.json`

### 3.3 evidence

- `schema/agentic-metrics.schema.json`
- `schema/automation-observability-v1.schema.json`
- `schema/artifact-metadata.schema.json`
- `schema/ci-artifact-provenance-v1.schema.json`
- `schema/assurance-summary.schema.json`
- `schema/claim-evidence-manifest.schema.json`
- `schema/claim-level-summary-v1.schema.json`
- `schema/context-pack-boundary-map-summary.schema.json`
- `schema/security-code-map-v1.schema.json`
- `schema/symbol-index-v1.schema.json`
- `schema/security-entrypoint-map-v1.schema.json`
- `schema/security-audit-task-bundle-v1.schema.json`
- `schema/security-audit-prompt-pack-v1.schema.json`
- `schema/security-finding-v1.schema.json`
- `schema/temporal-run-summary.schema.json`
- `schema/bench-criteria.schema.json`
- `schema/bench-compare.schema.json`
- `schema/benchmark-report.schema.json`
- `schema/conformance-metrics.schema.json`
- `schema/counterexample.schema.json`
- `schema/envelope.schema.json`
- `schema/formal-summary-v1.schema.json`
- `schema/formal-summary-v2.schema.json`
- `schema/license-scope-audit.schema.json`
- `schema/conditional-asset-audit.schema.json`
- `schema/notice-readiness-audit.schema.json`
- `schema/contributor-license-readiness-audit.schema.json`
- `schema/third-party-notice-candidate-audit.schema.json`
- `schema/apache-license-cutover-readiness-audit.schema.json`
- `schema/apache-license-cutover-approval-readiness-audit.schema.json`
- `schema/quality-scorecard.schema.json`
- `schema/report-envelope.schema.json`
- `schema/spec-validation-report.schema.json`
- `schema/trace-bundle.schema.json`
- `schema/trace-bundle-summary.schema.json`
- `schema/ui-e2e-summary.schema.json`
- `schema/usefulness-evaluation-report.schema.json`
- `schema/verify-lite-run-summary.schema.json`

### 3.4 operation

- `schema/change-package.schema.json`
- `schema/change-package-v2.schema.json`
- `schema/execplan.schema.json`
- `schema/execution-plan-v1.schema.json`
- `schema/plan-artifact.schema.json`
- `schema/run-manifest.schema.json`

## 4. 主要 artifact の produced/consumed 対応

| artifact (path/pattern) | schema | producer (primary) | consumer (primary) |
| --- | --- | --- | --- |
| `artifacts/verify-lite/verify-lite-run-summary.json` | `schema/verify-lite-run-summary.schema.json` | `scripts/ci/write-verify-lite-summary.mjs`, `.github/workflows/verify-lite.yml` | `scripts/ci/validate-verify-lite-summary.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `spec/discovery-pack/**/*.{yml,yaml,json}` | `schema/discovery-pack-v1.schema.json` | manual authoring in `spec/discovery-pack/` | `scripts/discovery-pack/validate.mjs`, `scripts/discovery-pack/compile.mjs`, `src/cli/discovery-cli.ts` |
| `artifacts/discovery-pack/discovery-pack-validate-report.json` | 専用 schema 未整備（`contractId=discovery-pack-validation-report.v1`） | `scripts/discovery-pack/validate.mjs`, `.github/workflows/verify-lite.yml` | `docs/spec/discovery-pack.md`, `scripts/summary/render-pr-summary.mjs`, CI Step Summary / PR comment operators |
| `artifacts/discovery-pack/discovery-pack-compile-report.json` | 専用 schema 未整備（`contractId=discovery-pack-compile-report.v1`） | `scripts/discovery-pack/compile.mjs`, `.github/workflows/verify-lite.yml`（strict時 dry-run） | `docs/spec/discovery-pack.md`, `scripts/summary/render-pr-summary.mjs`, operator review before SSOT promotion |
| `artifacts/discovery-pack/plan-to-spec-normalized.md` | non-authoritative Markdown (no schema) | `scripts/discovery-pack/compile.mjs` (`--target plan-spec`), `src/cli/discovery-cli.ts` | `ae tests:scaffold --input ...`, human review before repo SSOT promotion |
| `artifacts/discovery-pack/context-pack-scaffold.yaml` | `schema/context-pack-v1.schema.json` (scaffold-compatible, non-authoritative) | `scripts/discovery-pack/compile.mjs` (`--target context-pack-scaffold`), `src/cli/discovery-cli.ts` | manual editing before Context Pack SSOT promotion, future Context Pack validation |
| `artifacts/context-pack/boundary-map-summary.json` | `schema/context-pack-boundary-map-summary.schema.json` | `scripts/context-pack/verify-boundary-map.mjs`（`pnpm run context-pack:verify-boundary-map`） | PR evidence review、将来の policy-gate / assurance-summary 取り込み。`status=ok/drift/skipped/unresolved` により、drift は後続 policy が enforcement を選択するまで report-only の design-boundary evidence gap として扱う |
| `artifacts/assurance/assurance-summary.json` | `schema/assurance-summary.schema.json` | `scripts/assurance/aggregate-lanes.mjs`, `.github/workflows/verify-lite.yml`。optional な `security-claim/v1`、`security-finding/v1`、`security-review/v1`、`producer-normalization-summary/v1`、`context-pack-boundary-map-summary/v1`、`claim-evidence-manifest/v1`、`policy-decision/v1` 入力により、lane evidence と PR review 用 `reviewSurface` を表示する | `scripts/ci/validate-assurance-summary.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/ci/validate-json.mjs`, `scripts/ci/enforce-assurance-summary.mjs`, `scripts/quality/build-quality-scorecard.mjs`, `scripts/agents/build-hook-feedback.mjs`, `scripts/agents/create-handoff.mjs`, `scripts/summary/render-pr-summary.mjs`, `.github/workflows/pr-ci-status-comment.yml`。`reviewSurface` は report-only であり、それ自体では merge 承認にならない |
| `artifacts/assurance/claim-evidence-manifest.json` | `schema/claim-evidence-manifest.schema.json` | `scripts/assurance/build-claim-evidence-manifest.mjs`、`.github/workflows/verify-lite.yml`、`fixtures/assurance/sample.claim-evidence-manifest.json`（schema contract fixture）。optional な `security-claim/v1`、`security-finding/v1`、`security-review/v1` 入力は `summary.security` に集約され、元の security ID を claim/evidence の `externalIds` に保持し、`securityClaimType` / `assumptionHandlingRefs` で assumption handling を表示する | `scripts/ci/validate-json.mjs`、`scripts/ci/validate-artifacts-ajv.mjs`、`tests/contracts/claim-evidence-manifest-contract.test.ts`、`scripts/summary/render-pr-summary.mjs`、`scripts/ci/policy-gate.mjs`、`.github/workflows/pr-ci-status-comment.yml`。primary claim status は `satisfied` / `partial` / `waived` / `unresolved` のままにし、`behavior/tested`、`model/model-checked`、`proof/proved`、`runtime/runtime-mitigated` などの review-state count は別表示する |
| `artifacts/assurance/claim-level-summary.json` | `schema/claim-level-summary-v1.schema.json` | `scripts/assurance/aggregate-claim-levels.mjs`、`pnpm run claim-level-summary:generate`。`claim-evidence-manifest/v1`、`policy-gate-summary/v1`、optional な `change-package/v2` / `temporary-override/v1` から PR/release 向け preview projection を生成する。`fixtures/assurance/claim-level-summary/expected/claim-level-summary.json` は satisfied / tested / model-checked / proved / runtime-mitigated / waived / unresolved / failed / not-applicable を網羅する | `scripts/ci/validate-json.mjs`、`tests/contracts/assurance-control-plane-schema-contract.test.ts`、`tests/scripts/claim-level-summary.test.ts`、将来の PR/release summary renderer。この preview は `claim-evidence-manifest/v1` の claim-status vocabulary や `change-package/v2` の package / release outcome status を変更しない |
| `artifacts/security/security-claims.json` | `schema/security-claim-v1.schema.json` | manual authoring、`ae security import-speca`、`ae security extract-claims`、`fixtures/security-assurance/sample.security-claims.json`（schema contract fixture） | `ae security map-code`、将来の Security Assurance Lane producer、`scripts/ci/validate-json.mjs`、`tests/contracts/security-assurance-contract.test.ts`。後続 artifact は `claims[].id` を参照する |
| `artifacts/security/security-threat-model.json` | `schema/security-threat-model-v1.schema.json` | manual authoring、`ae security import-speca`、`fixtures/security-assurance/sample.security-threat-model.json`（schema contract fixture） | 将来の security audit / review producer、`scripts/ci/validate-json.mjs`、`tests/contracts/security-assurance-contract.test.ts`。`threats[].relatedClaimIds[]` で security claim id を参照する |
| `artifacts/security/security-audit-scope.json` | `schema/security-audit-scope-v1.schema.json` | manual authoring、bug-bounty / audit scope translation、`fixtures/security-assurance/sample.security-audit-scope.json`（schema contract fixture） | 将来の security claim extraction、code-map、audit、review producer。MVP contract では glob-based scope に限定する |
| `artifacts/security/security-code-map.json` | `schema/security-code-map-v1.schema.json` | `ae security map-code`（`--symbol-index` により optional に `symbol-index/v1` を消費）、`fixtures/security-assurance/sample.security-code-map.json`（schema contract fixture） | `ae security audit`、`scripts/ci/validate-json.mjs`、`tests/contracts/security-assurance-contract.test.ts`。security claim id を candidate source location へ接続するが、finding としては扱わない |
| `artifacts/code/symbol-index.json` | `schema/symbol-index-v1.schema.json` | manual authoring または external deterministic symbol-index producer、`fixtures/security-assurance/sample.symbol-index.json`（schema contract fixture） | `ae security map-code --symbol-index` の optional input、`scripts/ci/validate-json.mjs`、`tests/contracts/security-assurance-contract.test.ts`。symbol metadata のみを記録し、call graph / dataflow proof ではない |
| `artifacts/security/security-entrypoint-map.json` | `schema/security-entrypoint-map-v1.schema.json` | manual authoring または external deterministic entrypoint-map producer、`fixtures/security-assurance/sample.security-entrypoint-map.json`（schema contract fixture） | `ae security review --entrypoint-map` の optional input、`scripts/ci/validate-json.mjs`、`tests/contracts/security-assurance-contract.test.ts`。entrypoint reachability hint のみを記録し、full call graph / dataflow proof ではない |
| `artifacts/security/security-audit-tasks.json` | `schema/security-audit-task-bundle-v1.schema.json` | `ae security audit`、`fixtures/security-assurance/sample.security-audit-tasks.json`（schema contract fixture） | `ae security audit-prompt`、fixture-backed proof-attempt normalization、human security review、`scripts/ci/validate-json.mjs`、`tests/contracts/security-assurance-contract.test.ts`。task bundle は prompt input であり finding ではない |
| `artifacts/security/codex-audit-prompts/security-audit-prompt-pack.json` | `schema/security-audit-prompt-pack-v1.schema.json` | `ae security audit-prompt`、`fixtures/security-assurance/sample.security-audit-prompt-pack.json`（schema contract fixture） | Codex CLI / human reviewer 向け prompt input。Markdown prompt は `artifacts/security/codex-audit-prompts/prompts/` 配下に deterministic に生成し、external LLM / network は実行しない |
| `artifacts/security/security-findings.json` | `schema/security-finding-v1.schema.json` | `ae security audit`、`ae security import-speca`、`fixtures/security-assurance/sample.security-findings.json`（schema contract fixture） | `ae security review`、`scripts/assurance/aggregate-lanes.mjs`、`scripts/assurance/build-claim-evidence-manifest.mjs`、policy-gate report-only summary。`status=candidate` は confirmed vulnerability ではない |
| `artifacts/security/security-review.json` | `schema/security-review-v1.schema.json` | `ae security review`（`--claims` により optional に `security-claim/v1`、`--entrypoint-map` により optional に `security-entrypoint-map/v1` を消費）、`ae security import-speca`、`fixtures/security-assurance/sample.security-review.json`（schema contract fixture） | `scripts/assurance/aggregate-lanes.mjs`、`scripts/assurance/build-claim-evidence-manifest.mjs`、`scripts/summary/render-pr-summary.mjs`、policy-gate report-only summary。finding severity、Dead Code / Trust Boundary / Scope gate、false-positive root-cause classification、claim type、assumption handling を保持する |
| `artifacts/temporal/*/temporal-run-summary.json` | `schema/temporal-run-summary.schema.json` | `examples/temporal-workflow-adapter`、`fixtures/temporal/sample.temporal-run-summary.json`（schema contract fixture） | `scripts/ci/validate-json.mjs`、`tests/contracts/temporal-run-summary-contract.test.ts`、operator review。Temporal 固有 metadata はこの adapter sidecar に閉じる |
| `spec/assurance-profile/upstream-context-promotion-v1.json` | `schema/assurance-profile.schema.json` | manual authoring in `spec/assurance-profile/` | `scripts/assurance/aggregate-lanes.mjs`, `docs/guides/upstream-context-promotion.md`, `tests/fixtures/upstream-context-promotion-minimal.assurance.test.ts` |
| `artifacts/report-envelope.json` | `schema/envelope.schema.json` | `scripts/trace/create-report-envelope.mjs` | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/trace/publish-envelope.mjs` |
| `artifacts/trace/report-envelope.json` | `schema/envelope.schema.json` | `scripts/trace/create-report-envelope.mjs` (copy運用含む) | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/trace/post-envelope-comment.mjs` |
| `artifacts/formal/formal-summary-v1.json` | `schema/formal-summary-v1.schema.json` | `scripts/formal/generate-formal-summary-v1.mjs` (`--out`), `.github/workflows/verify-lite.yml`, `.github/workflows/formal-aggregate.yml` | `scripts/ci/validate-formal-summary-v1.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/ci/generate-run-manifest.mjs` |
| `artifacts/formal/formal-summary-v2.json` | `schema/formal-summary-v2.schema.json` | `scripts/formal/generate-formal-summary-v1.mjs` (`--out-v2`), `.github/workflows/verify-lite.yml`, `.github/workflows/formal-aggregate.yml` | `scripts/ci/validate-formal-summary-v2.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/ci/generate-run-manifest.mjs` |
| `artifacts/reference/benchmarks/bench.json` | `schema/benchmark-report.schema.json` | `src/commands/bench/run.ts` (`ae bench`) | `tests/scripts/benchmark-report-schema.test.ts`, `scripts/quality/bench-compare.mjs` |
| `configs/bench-criteria.default.json` | `schema/bench-criteria.schema.json` | `configs/bench-criteria.default.json` (repo default), `scripts/quality/bench-compare.mjs` (`--criteria` 未指定時) | `scripts/quality/bench-compare.mjs`, `tests/scripts/bench-compare.test.ts` |
| `artifacts/bench-compare.json` | `schema/bench-compare.schema.json` | `scripts/quality/bench-compare.mjs` | `tests/scripts/bench-compare-schema.test.ts`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `artifacts/conformance/conformance-results.json` | `schema/conformance-verify-result.schema.json` | `src/cli/conformance-cli.ts` (`ae conformance verify`) | `src/cli/conformance-report.ts`, `scripts/formal/verify-conformance.mjs` |
| `artifacts/hermetic-reports/conformance/summary.json` | `schema/conformance-report.schema.json` | `scripts/formal/verify-conformance.mjs` | `scripts/change-package/generate.mjs`, `scripts/ci/validate-json.mjs` |
| `artifacts/observability/trace-bundle.json` | `schema/trace-bundle.schema.json` | `src/cli/conformance-cli.ts` (`ae conformance ingest`) | `src/cli/conformance-cli.ts` (`ae conformance verify --trace-bundle`) |
| `artifacts/hermetic-reports/trace/**/kvonce-validation.json` | `schema/trace-validation.schema.json` | `scripts/trace/run-kvonce-conformance.sh` | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/trace/render-trace-summary.mjs` |
| `artifacts/change-package/change-package.json` | `schema/change-package.schema.json` | `scripts/change-package/generate.mjs` | `scripts/change-package/validate.mjs`, `.github/workflows/pr-ci-status-comment.yml` |
| `artifacts/handoff/ae-handoff.json` | `schema/ae-handoff.schema.json` | `scripts/agents/create-handoff.mjs`, `templates/comments/AE-HANDOFF.md`（manual/export）, `docs/agents/handoff.md` | `scripts/agents/validate-handoff.mjs`, future PR/Issue handoff consumers |
| `artifacts/agents/hook-feedback.json` | `schema/hook-feedback.schema.json` | `scripts/agents/build-hook-feedback.mjs`, `.github/workflows/pr-ci-status-comment.yml` | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/agents/create-handoff.mjs`, `docs/agents/hook-feedback.md`, Claude Code / Codex continuation consumers |
| `artifacts/agents/producer-normalization-summary.json` | `schema/producer-normalization-summary.schema.json` | `scripts/agents/normalize-producer-output.mjs`, `fixtures/agents/evidence-adapters/*.json`。`fixtures/agents/producer-normalization-summary.codex.json` は schema contract fixture | `scripts/ci/validate-json.mjs`, 将来の PR summary / policy-gate report-only context。raw producer assertion、missing evidence、known gap、expected routing を記録し、pass/proved/approved judgment は emit しない |
| `artifacts/agents/agent-pr-assurance-metrics.json` | `schema/agentic-metrics.schema.json`（`agentPrAssurance` extension） | optional な agent PR assurance metrics producer / future PR assurance collector。`fixtures/agentic-metrics/agent-pr-assurance-metrics.example.json` は contract fixture | `scripts/ci/validate-json.mjs` と、接続時の future quality-scorecard / PR-summary consumer。role=observability/evidence、enforcement=report-only、全PR必須ではなく、policy-gate block条件も追加しない |
| `artifacts/plan/plan-artifact.json` | `schema/plan-artifact.schema.json` | `scripts/plan-artifact/generate.mjs` | `scripts/plan-artifact/validate.mjs`, `scripts/ci/policy-gate.mjs`, `.github/workflows/pr-ci-status-comment.yml`, `.github/workflows/policy-gate.yml` |
| `artifacts/ci/policy-input-v1.json` | `schema/policy-input-v1.schema.json` | `scripts/ci/policy-gate.mjs`, `.github/workflows/policy-gate.yml` | `scripts/ci/policy-gate.mjs`, `scripts/ci/policy-shadow-compare.mjs`, `scripts/ci/validate-json.mjs`; optional `assurance` section normalizes `claim-evidence-manifest/v1`, including `summary.security` report-only finding counts, for waiver-aware decisions |
| `artifacts/ci/policy-decision-js-v1.json`, `artifacts/ci/policy-decision-opa-v1.json` | `schema/policy-decision-v1.schema.json` | `scripts/ci/policy-gate.mjs`, `scripts/ci/policy-shadow-compare.mjs`, `.github/workflows/policy-gate.yml` | `scripts/ci/policy-shadow-compare.mjs`, `scripts/ci/validate-json.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`; JS decision は waiver-aware な `pass` / `waived` / `report-only` / `block` assurance result、report-only security finding count、optional な source artifact path 付き agent assurance finding を記録する |
| `artifacts/ci/policy-shadow-compare-v1.json` | 専用 schema 未整備（`contractId=policy-shadow-compare.v1`） | `scripts/ci/policy-shadow-compare.mjs`, `.github/workflows/policy-gate.yml` | `docs/ci/pr-automation.md`, `docs/ci/label-gating.md` |
| `artifacts/ci/policy-gate-summary.json` | `schema/policy-gate-summary-v1.schema.json` | `scripts/ci/policy-gate.mjs`, `.github/workflows/policy-gate.yml` | `scripts/ci/validate-policy-gate-summary.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`; optional な `evaluation.assurance.agentAssuranceFindings` は producer / assurance-summary finding を count、severity、source artifact path 付きの report-only evidence として表示する |
| `artifacts/**/*.provenance.json` | `schema/ci-artifact-provenance-v1.schema.json` | `scripts/ci/write-artifact-provenance.mjs`、Policy Gate / PR Maintenance / Quality Gates / SBOM / formal aggregate などの CI decision・publisher workflow | `scripts/ci/validate-artifact-provenance.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, trusted workflow-run publisher。subject digest を producer repository / workflow ref / run id / run attempt / PR number / head SHA に bind する |
| `artifacts/ci/harness-health.json` | `schema/harness-health.schema.json` | `scripts/ci/build-harness-health.mjs`, `.github/workflows/pr-ci-status-comment.yml`, `.github/workflows/ci-extended.yml` | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/ci/validate-json.mjs`, `scripts/agents/build-hook-feedback.mjs`, `scripts/change-package/generate.mjs` |
| `artifacts/quality/quality-scorecard.json` | `schema/quality-scorecard.schema.json` | `scripts/quality/build-quality-scorecard.mjs`, `.github/workflows/verify-lite.yml` | `scripts/ci/validate-quality-scorecard.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/ci/validate-json.mjs`, `scripts/summary/render-pr-summary.mjs`, `.github/workflows/pr-ci-status-comment.yml` |
| `artifacts/reference/legal/license-scope-audit.json` | `schema/license-scope-audit.schema.json` | `scripts/legal/inventory-license-scope.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/LICENSE-MIGRATION-AUDIT.md`, downstream legal audit builders |
| `artifacts/reference/legal/conditional-asset-audit.json` | `schema/conditional-asset-audit.schema.json` | `scripts/legal/inventory-conditional-assets.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/CONDITIONAL-ASSET-PROVENANCE-AUDIT.md`, downstream legal audit builders |
| `artifacts/reference/legal/notice-readiness-audit.json` | `schema/notice-readiness-audit.schema.json` | `scripts/legal/build-notice-readiness.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/NOTICE-READINESS-AUDIT.md`, operator/legal review before `NOTICE` cutover |
| `artifacts/reference/legal/contributor-license-readiness-audit.json` | `schema/contributor-license-readiness-audit.schema.json` | `scripts/legal/build-contributor-license-readiness.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/CONTRIBUTOR-LICENSE-READINESS.md`, human/legal contributor review before relicensing |
| `artifacts/reference/legal/third-party-notice-candidate-audit.json` | `schema/third-party-notice-candidate-audit.schema.json` | `scripts/legal/build-third-party-notice-candidate-audit.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/THIRD-PARTY-NOTICE-CANDIDATES-AUDIT.md`, human/legal review before third-party notice cutover |
| `artifacts/reference/legal/apache-license-cutover-readiness-audit.json` | `schema/apache-license-cutover-readiness-audit.schema.json` | `scripts/legal/build-apache-license-cutover-readiness.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/APACHE-LICENSE-CUTOVER-READINESS.md`, final cutover readiness review before replacing `LICENSE` |
| `artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.json` | `schema/apache-license-cutover-approval-readiness-audit.schema.json` | `scripts/legal/build-apache-license-cutover-approval-readiness.mjs` | `scripts/ci/validate-json.mjs`, `docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-READINESS.md`, final approval completeness review before opening the cutover PR |
| `artifacts/ci/automation-report.json` | `schema/automation-observability-v1.schema.json` | `scripts/ci/lib/automation-report.mjs`, `.github/workflows/codex-autopilot-lane.yml` | `scripts/ci/validate-automation-report.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `artifacts/ci/pr-state-v1.json` | `schema/pr-state-v1.schema.json` | `scripts/ci/codex-autopilot-lane.mjs` | `scripts/ci/validate-json.mjs`, `docs/ci/codex-autopilot-lane.md` |
| `artifacts/ci/execution-plan-v1.json` | `schema/execution-plan-v1.schema.json` | `scripts/ci/codex-autopilot-lane.mjs` | `scripts/ci/validate-json.mjs`, `docs/ci/codex-autopilot-lane.md` |
| `artifacts/e2e/ui-e2e-summary.json` | `schema/ui-e2e-summary.schema.json` | `scripts/e2e/run-ui-e2e-semantic.mjs`, `.github/workflows/parallel-test-execution.yml` | `scripts/ci/build-harness-health.mjs`, `scripts/ci/validate-json.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `artifacts/e2e/summary.json` | `docs/schemas/artifacts-adapter-summary.schema.json` | `scripts/e2e/run-ui-e2e-semantic.mjs` | `scripts/ci/validate-artifacts-ajv.mjs`, future adapter-summary aggregators |

### 4.1 正準/legacy route marker

Produced/consumed table は実装 entry point を列挙します。複数導線が存在する場合は、`docs/reference/ASSURANCE-CANONICAL-ROUTES.md` で canonical / preview / legacy compatibility の別を判断します。現時点の cleanup marker は次の通りです。

| Topic | 正準導線 | 互換導線 | cleanup 状態 |
| --- | --- | --- | --- |
| Quality scorecard | `quality-scorecard/v1`, `scripts/quality/build-quality-scorecard.mjs`, `pnpm run quality:scorecard:v1`, `schema/quality-scorecard.schema.json` | `pnpm run quality:scorecard`, `scripts/quality-scorecard-generator.js` | 互換 script は必須入力がある場合に v1 へ委譲する。入力なし legacy diagnostic は workflow consumer に v1 input wiring test が入るまで維持。 |
| Formal status | `artifacts/formal/formal-summary-v2.json` と dual-write の `artifacts/formal/formal-summary-v1.json`; aggregate の `artifacts/hermetic-reports/formal/summary.json` | `formal/summary.json` | final compatibility input としてのみ維持。PR summary rendering は formal-summary v2/v1 と hermetic aggregate をこの fallback より先に読む。 |
| Counterexample GWT | counterexample を埋め込む canonical aggregate / tool evidence を優先して `scripts/formal/format-counterexamples.mjs` が派生する `artifacts/formal/gwt.summary.json` | `formal/summary.json` に埋め込まれた counterexample | 派生補助であり、primary formal status contract ではない。legacy counterexample は final fallback として維持する。 |
| PR summary judgment | `scripts/summary/render-pr-summary.mjs` と `pr-ci-status-comment.yml` append stage | 手書きまたは古い bot summary | renderer direct input と workflow 追記 Markdown を分離して維持。 |
| Change package | production `change-package/v1`; proof-carrying preview `change-package/v2` | source artifact fragment の直接参照 | v2 が preview / dual-write の間は v1 互換を維持。 |

### 4.2 Agent-output gap audit crosswalk

`docs/reports/AGENT-OUTPUT-CONTRACT-GAP-AUDIT.md` は ACP producer-routing gap ID を記録します。この catalog は artifact inventory を維持し、report は Issue-level gap register として扱います。

| Gap ID | Catalog surface | Follow-up |
| --- | --- | --- |
| ACP-GAP-001 | `fixtures/agents/evidence-adapters/` 配下の raw producer example | ACP-011 / #3482 |
| ACP-GAP-002 | raw example を既存 artifact へ routing する将来の report-only normalizer | ACP-012 / #3483 |
| ACP-GAP-003 | 既存 `assurance-summary`、`quality-scorecard`、formal、verify-lite artifact に基づく reviewer-facing summary | ACP-030 / #3486 |
| ACP-GAP-004 | normalized agent-assurance finding を消費する report-only policy context | ACP-040 / #3488 |
| ACP-GAP-005 | `policy-shadow-compare.v1` や一部 `artifacts/ci/*-summary.json` sidecar など既存 dedicated-schema gap | cataloged contract debt |
| ACP-GAP-006 | BYO agent の vendor-specific raw API | documented out of scope |

## 5. Security Assurance Lane のステータス意味論

- `security-audit-task-bundle/v1` は deterministic proof-attempt prompt input を記録する。単体では vulnerability evidence ではなく、claim の成立・不成立を確定しない。
- `security-finding/v1` は candidate-first として扱う。`status=candidate` と `status=needs-human-review` は監査 evidence であり、confirmed vulnerability ではない。confirmed vulnerability を表すのは `status=confirmed` のみ。
- `security-review/v1` は Dead Code / Trust Boundary / Scope の 3 gate を適用し、各 gate は `pass | fail | unknown | not-applicable` と rationale を保持する。producer 生成 review は後続 summary のため finding severity も保持する。optional な `security-entrypoint-map/v1` evidence が指定された場合、Trust Boundary gate は一致する entrypoint reachability を優先し、ない場合は `unknown` に倒す。未指定時は既存の scope reference 挙動を維持する。
- `falsePositiveRootCause` は `dead-code`, `trust-boundary-misunderstanding`, `out-of-scope`, `code-reading-error`, `spec-misinterpretation`, `insufficient-evidence` のいずれかで、resolved false positive（`rejected` または `out-of-scope`）のときだけ設定する。`needs-human-review`, `confirmed`, `waived` では `null` のままにする。
- security finding と 3-gate review は `assurance-summary/v1` と `claim-evidence-manifest/v1` に接続される。manifest は canonical な lowercase ID を維持しつつ、元の `SEC-CLAIM-*` / `SEC-FINDING-*` 識別子を `externalIds` に保持する。policy-gate は manifest を report-only mode で消費し、human review が残る high/critical finding を強調するが、candidate を confirmed vulnerability として扱わない。

## 6. Claim-level assurance status routing

- `claim-evidence-manifest/v1` は evidence-linking manifest です。claim ID、evidence reference、waiver reference、unresolved gap を policy-gate / summary consumer 向けに保持します。primary claim status は `satisfied`、`partial`、`waived`、`unresolved` に限定し、`tested`、`model-checked`、`proved`、`runtime-mitigated` などの review label は evidence-state projection として分離します。
- `claim-level-summary/v1` は PR / release projection です。source manifest contract を変更せず、satisfied、tested、model-checked、proved、runtime-mitigated、waived、unresolved、failed、not-applicable の count を要約します。
- `policy-decision/v1` は、active policy mode における claim-level assurance の `pass`、`report-only`、`waived`、`block` を記録します。
- `risk:high`、`enforce-assurance`、critical core policy は required lane 不足や unresolved claim を昇格できます。通常変更は count を可視化したまま report-only にできます。

## 7. 現時点の未整備（次段階）

- assurance contract は段階導入中であり、既定運用は report-only、strict assurance enforcement は `enforce-assurance` ラベル時の Verify Lite に限定される。
- `schemaVersion` は semver と `*/v1` 形式が混在している（統一規約は `docs/reference/SCHEMA-GOVERNANCE.md` で段階導入）。
- `change-package` は `v1` が現行 production contract、`v2` は proof-carrying 拡張の preview contract として併存している。
- Formal Summary は `v1` / `v2` の dual-write + dual-validate 期間として運用中（`v2`: `schemaVersion=formal-summary/v2`, `contractId=formal-summary.v2`）。
- `report-envelope` は `schema/envelope.schema.json` と `schema/report-envelope.schema.json` の二系統が併存している。
- 次の artifact は専用 schema の明示運用が未完（要追加整理）:
  - `artifacts/verify-lite/verify-lite-lint-summary.json`
  - `artifacts/run-manifest-check.json`
  - `artifacts/*-retry-eligibility.json`
  - `artifacts/ci/*-summary.json`（risk など）

## 8. 参照

- `docs/reference/SCHEMA-GOVERNANCE.md`
- `docs/reference/ASSURANCE-CANONICAL-ROUTES.md`
- `docs/agents/evidence-adapters.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/architecture/DELIVERY-CONTRACT-COMPATIBILITY-MATRIX.md`
- `scripts/ci/validate-artifacts-ajv.mjs`
- `scripts/ci/validate-formal-summary-v1.mjs`
- `scripts/ci/validate-formal-summary-v2.mjs`
- `scripts/ci/validate-json.mjs`
- `docs/architecture/PR-STATE-EXECUTION-PLAN-V1-DRAFT.md`
