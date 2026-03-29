---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/ci/pr-automation.md
lastVerified: '2026-03-29'
---
# PR Summary Tool I/O Spec (#407)

> Language / 言語: English | 日本語

---

## English

### Purpose
- Define a stable current-state contract for the PR summary renderer.
- Clarify which artifacts the renderer reads directly, which artifacts are appended by workflow, and which files are only upstream contracts.

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
- If optional JSON cannot be parsed or read, the renderer usually treats that input as missing and continues.

### Validation Boundary
- Prefer `docs/quality/ARTIFACTS-CONTRACT.md` and `docs/reference/CONTRACT-CATALOG.md` for the latest producer / consumer inventory.
- JSON schema and shape validation are upstream CI / producer responsibilities.
- The renderer assumes those validations have already happened and does not fail hard on malformed optional JSON.
- Keep append-stage Markdown out of the direct input contract.

### Sidecar Combined JSON
- Recommended path: `artifacts/summary/combined.json`
- Include only normalized fields that current consumers actually read.
- Do not duplicate Discovery Pack state in `combined.json`; current consumers read it from `verify-lite-run-summary.json`.

#### Example (extended)
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

## 日本語

### 目的
- PR summary renderer の current-state 契約を安定化して定義する。
- renderer が直接読む artifact、workflow で append される artifact、upstream contract にとどまる file を切り分ける。

### 入力（read-only）
- Required baseline:
  - `artifacts/verify-lite/verify-lite-run-summary.json`
- 現在の optional direct input:
  - `artifacts/summary/combined.json`
  - `coverage/coverage-summary.json` または `artifacts/coverage/coverage-summary.json`
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
- Workflow append-stage input:
  - `artifacts/ci/harness-health.md`
  - `artifacts/change-package/change-package.md`
  - `artifacts/change-package/change-package-validation.md`
  - `artifacts/plan/plan-artifact.md`
  - `artifacts/plan/plan-artifact-validation.md`
  - `artifacts/agents/hook-feedback.md`
  - `artifacts/downloaded/verify-lite-report/artifacts/quality/quality-scorecard.md`

### 出力
- PR description や bot comment に貼れる単一の Markdown block。
- 現在の Markdown 出力 path: `artifacts/summary/PR_SUMMARY.md`
- 現在の machine-readable sidecar: なし
  - `artifacts/summary/combined.json` は output sidecar ではなく input sidecar。

### 正規化入力の例
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

### CLI 概要
```bash
SUMMARY_LANG=ja SUMMARY_MODE=detailed \
node scripts/summary/render-pr-summary.mjs
```

### current behavior の補足
- canonical producer は `pr-ci-status-comment.yml` の `summarize` job。
- `render-pr-summary.mjs` はまず `artifacts/summary/combined.json` を読み、その後 coverage / replay / BDD / properties / GWT / formal の fallback input を read-only で補完する。
- Discovery Pack line は `artifacts/verify-lite/verify-lite-run-summary.json` の top-level `discoveryPack` object から生成する。
- `steps.discoveryPackValidation` と `steps.discoveryPackCompile` は execution record であり、renderer の direct input ではない。
- formal line は `combined.json.formal` を優先し、次に `formal/summary.json`、次に `artifacts/hermetic-reports/formal/summary.json` を fallback とする。
- Formal Summary v1/v2 は upstream の producer / validator contract であり、renderer の direct input ではない。
- baseline input は `verify-lite-run-summary` で、assurance と quality scorecard は optional input。
- renderer 出力後に、`pr-ci-status-comment.yml` が上記の workflow-stage Markdown artifact を append する。
- optional JSON が parse/read できなくても、renderer は通常 missing input として扱って継続する。

### validation 境界
- 最新の producer / consumer inventory は `docs/quality/ARTIFACTS-CONTRACT.md` と `docs/reference/CONTRACT-CATALOG.md` を優先する。
- JSON schema や shape validation は upstream CI / producer の責務。
- renderer はそれらの validation が済んでいる前提で動き、malformed な optional JSON で hard fail しない。
- append-stage Markdown は direct input contract に含めない。

### Sidecar Combined JSON
- 推奨 path: `artifacts/summary/combined.json`
- current consumer が実際に読む正規化 field だけを含める。
- Discovery Pack state を `combined.json` に重複格納しない。current consumer は `verify-lite-run-summary.json` 側を読む。

#### 例（拡張版）
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
