# Contract Catalog (Issue #2406 Foundation)

> Language / 言語: English | 日本語

---

## English (Summary)

- This catalog is the baseline inventory for Issue #2406 (contract model unification).
- It classifies `schema/*.schema.json` into four contract domains:
  - `input`: request/config/model inputs
  - `decision`: pass/fail/gate/judgement outputs
  - `evidence`: summaries/observability/audit outputs
  - `operation`: execution plans/manifests/orchestration outputs
- Some schemas are dual-role (produced evidence and consumed as input). This document records the **primary** role.

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

## 3. schema 一覧（2026-03-04時点）

### 3.1 input

- `schema/codex-task-request.schema.json`
- `schema/context-bundle.schema.json`
- `schema/context-pack-v1.schema.json`
- `schema/context-pack-functor-map.schema.json`
- `schema/context-pack-natural-transformation.schema.json`
- `schema/context-pack-phase5-templates.schema.json`
- `schema/context-pack-product-coproduct.schema.json`
- `schema/context-pack-suggestions.schema.json`
- `schema/flow.schema.json`
- `schema/formal-plan.schema.json`
- `schema/issue-traceability-map.schema.json`
- `schema/release-policy.schema.json`
- `schema/state-machine.schema.json`
- `schema/trace-map.schema.json`

### 3.2 decision

- `schema/codex-task-response.schema.json`
- `schema/conformance-report.schema.json`
- `schema/conformance-verify-result.schema.json`
- `schema/issue-traceability-matrix.schema.json`
- `schema/pr-state-v1.schema.json`
- `schema/policy-gate-summary-v1.schema.json`
- `schema/quality-report.schema.json`
- `schema/trace-validation.schema.json`
- `schema/verify-profile-summary.schema.json`

### 3.3 evidence

- `schema/agentic-metrics.schema.json`
- `schema/artifact-metadata.schema.json`
- `schema/conformance-metrics.schema.json`
- `schema/counterexample.schema.json`
- `schema/envelope.schema.json`
- `schema/formal-summary-v1.schema.json`
- `schema/report-envelope.schema.json`
- `schema/spec-validation-report.schema.json`
- `schema/trace-bundle.schema.json`
- `schema/trace-bundle-summary.schema.json`
- `schema/usefulness-evaluation-report.schema.json`
- `schema/verify-lite-run-summary.schema.json`

### 3.4 operation

- `schema/change-package.schema.json`
- `schema/execplan.schema.json`
- `schema/execution-plan-v1.schema.json`
- `schema/run-manifest.schema.json`

## 4. 主要 artifact の produced/consumed 対応

| artifact (path/pattern) | schema | producer (primary) | consumer (primary) |
| --- | --- | --- | --- |
| `artifacts/verify-lite/verify-lite-run-summary.json` | `schema/verify-lite-run-summary.schema.json` | `scripts/ci/write-verify-lite-summary.mjs`, `.github/workflows/verify-lite.yml` | `scripts/ci/validate-verify-lite-summary.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `artifacts/report-envelope.json` | `schema/envelope.schema.json` | `scripts/trace/create-report-envelope.mjs` | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/trace/publish-envelope.mjs` |
| `artifacts/trace/report-envelope.json` | `schema/envelope.schema.json` | `scripts/trace/create-report-envelope.mjs` (copy運用含む) | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/trace/post-envelope-comment.mjs` |
| `artifacts/formal/formal-summary-v1.json` | `schema/formal-summary-v1.schema.json` | `scripts/formal/generate-formal-summary-v1.mjs`, `.github/workflows/formal-aggregate.yml` | `scripts/ci/validate-formal-summary-v1.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `artifacts/conformance/conformance-results.json` | `schema/conformance-verify-result.schema.json` | `src/cli/conformance-cli.ts` (`ae conformance verify`) | `src/cli/conformance-report.ts`, `scripts/formal/verify-conformance.mjs` |
| `artifacts/hermetic-reports/conformance/summary.json` | `schema/conformance-report.schema.json` | `scripts/formal/verify-conformance.mjs` | `scripts/change-package/generate.mjs`, `scripts/ci/validate-json.mjs` |
| `artifacts/observability/trace-bundle.json` | `schema/trace-bundle.schema.json` | `src/cli/conformance-cli.ts` (`ae conformance ingest`) | `src/cli/conformance-cli.ts` (`ae conformance verify --trace-bundle`) |
| `artifacts/hermetic-reports/trace/**/kvonce-validation.json` | `schema/trace-validation.schema.json` | `scripts/trace/run-kvonce-conformance.sh` | `scripts/ci/validate-artifacts-ajv.mjs`, `scripts/trace/render-trace-summary.mjs` |
| `artifacts/change-package/change-package.json` | `schema/change-package.schema.json` | `scripts/change-package/generate.mjs` | `scripts/change-package/validate.mjs`, `.github/workflows/pr-ci-status-comment.yml` |
| `artifacts/ci/policy-gate-summary.json` | `schema/policy-gate-summary-v1.schema.json` | `scripts/ci/policy-gate.mjs`, `.github/workflows/policy-gate.yml` | `scripts/ci/validate-policy-gate-summary.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` |
| `artifacts/ci/pr-state-v1.json` | `schema/pr-state-v1.schema.json` | `scripts/ci/codex-autopilot-lane.mjs` | `scripts/ci/validate-json.mjs`, `docs/ci/codex-autopilot-lane.md` |
| `artifacts/ci/execution-plan-v1.json` | `schema/execution-plan-v1.schema.json` | `scripts/ci/codex-autopilot-lane.mjs` | `scripts/ci/validate-json.mjs`, `docs/ci/codex-autopilot-lane.md` |

## 5. 現時点の未整備（次段階）

- `schemaVersion` は semver と `*/v1` 形式が混在している（統一規約は `docs/reference/SCHEMA-GOVERNANCE.md` で段階導入）。
- `report-envelope` は `schema/envelope.schema.json` と `schema/report-envelope.schema.json` の二系統が併存している。
- 次の artifact は専用 schema の明示運用が未完（要追加整理）:
  - `artifacts/verify-lite/verify-lite-lint-summary.json`
  - `artifacts/run-manifest-check.json`
  - `artifacts/*-retry-eligibility.json`
  - `artifacts/ci/*-summary.json`（policy/risk/harness など）

## 6. 参照

- `docs/reference/SCHEMA-GOVERNANCE.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `scripts/ci/validate-artifacts-ajv.mjs`
- `scripts/ci/validate-json.mjs`
- `docs/architecture/PR-STATE-EXECUTION-PLAN-V1-DRAFT.md`
