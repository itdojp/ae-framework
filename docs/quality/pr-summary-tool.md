---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/ci/pr-automation.md
lastVerified: '2026-03-21'
---
# PR Summary Tool I/O Spec (#407)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

正規化アーティファクトを読み取り、PR 向けの単一サマリブロックを出力する集約ツールの current-state I/O 仕様です。入力（verify-lite / policy / optional assurance・quality・hook-feedback など）、出力（Markdown/JSON サイドカー）、CLI の概略、検証ノートを記載します。

## English (Detailed)

### Purpose
- Define a stable current-state contract for the PR summary renderer.
- Clarify which artifacts the renderer reads directly, which artifacts are appended by workflow, and which files are merely upstream contracts.

### Inputs (read-only)
- Required baseline:
  - `artifacts/verify-lite/verify-lite-run-summary.json`
- Current optional direct inputs:
  - `artifacts/summary/combined.json`
  - `coverage/coverage-summary.json` or `artifacts/coverage/coverage-summary.json`
  - `artifacts/domain/replay.summary.json`
  - `artifacts/bdd/scenarios.json`
  - `artifacts/properties/summary.json`
  - `artifacts/properties/ltl-suggestions.json`
  - `artifacts/formal/gwt.summary.json`
  - `artifacts/assurance/assurance-summary.json`
  - `artifacts/quality/quality-scorecard.json`
  - `artifacts/formal/formal-aggregate.json`
  - legacy `formal/summary.json`
  - `artifacts/hermetic-reports/formal/summary.json`
- Workflow append-stage inputs:
  - `artifacts/ci/harness-health.md`
  - `artifacts/change-package/change-package.md`
  - `artifacts/change-package/change-package-validation.md`
  - `artifacts/plan/plan-artifact.md`
  - `artifacts/plan/plan-artifact-validation.md`
  - `artifacts/agents/hook-feedback.md`
  - `artifacts/downloaded/verify-lite-report/artifacts/quality/quality-scorecard.md`

### Output
- A single Markdown block suitable for PR descriptions or bot comments.
- Current Markdown path: `artifacts/summary/PR_SUMMARY.md`
- Current machine-readable sidecar: none
  - `artifacts/summary/combined.json` is an input sidecar, not an output sidecar.

### Normalized Input Example
`artifacts/summary/combined.json`:
```json
{
  "coverage": { "value": 0.82, "threshold": 0.80, "delta": 0.01 },
  "bdd": { "criteriaCount": 3, "title": "Reserve inventory without going negative or double-booking" },
  "formal": { "result": "pass", "violations": [] },
  "adapters": [{ "name": "lighthouse", "status": "warn", "summary": "Perf 78, A11y 96, PWA 55" }],
  "properties": [{ "count": 4, "traceId": "inv-001" }],
  "replay": { "totalEvents": 12, "byType": { "ItemReceived": 7, "ItemAllocated": 5 }, "violations": [] }
}
```

### CLI Outline
```bash
SUMMARY_LANG=ja SUMMARY_MODE=detailed \
node scripts/summary/render-pr-summary.mjs
```

### Current Behavior Notes
- `pr-ci-status-comment.yml` job `summarize` is the canonical producer.
- `render-pr-summary.mjs` prefers `artifacts/summary/combined.json`, then supplements it with read-only coverage / replay / BDD / properties / GWT / formal fallback inputs.
- The Discovery Pack line is generated from the top-level `discoveryPack` object in `artifacts/verify-lite/verify-lite-run-summary.json`.
- `steps.discoveryPackValidation` and `steps.discoveryPackCompile` are execution records, not direct renderer inputs.
- The formal line prefers `combined.json.formal`, then falls back to `formal/summary.json`, then `artifacts/hermetic-reports/formal/summary.json`.
- Formal Summary v1/v2 are upstream producer / validator contracts, not direct renderer inputs.
- `verify-lite-run-summary` is the baseline input. Assurance and quality scorecard inputs are optional.
- After renderer output, `pr-ci-status-comment.yml` appends the workflow-stage Markdown artifacts listed above.

### Validation Boundary
- Prefer `docs/quality/ARTIFACTS-CONTRACT.md` and `docs/reference/CONTRACT-CATALOG.md` for the latest producer / consumer inventory.
- Validate JSON inputs before rendering.
- Keep append-stage Markdown out of the direct input contract.

## Sidecar Combined JSON
- Recommended path: `artifacts/summary/combined.json`
- Include only normalized fields that current consumers actually read.
- Do not duplicate Discovery Pack state in `combined.json`; current consumers read it from `verify-lite-run-summary.json`.

### Example (extended)
```json
{
  "coverage": { "value": 0.82, "threshold": 0.80, "delta": 0.01 },
  "bdd": { "criteriaCount": 3, "title": "Reserve inventory without going negative or double-booking" },
  "formal": { "result": "pass", "violations": [] },
  "adapters": [ { "name": "lighthouse", "status": "warn", "summary": "Perf 78, A11y 96, PWA 55" } ],
  "properties": [{ "count": 4, "traceId": "inv-001" }],
  "replay": { "totalEvents": 12, "byType": { "ItemReceived": 7, "ItemAllocated": 5 }, "violations": [] }
}
```
