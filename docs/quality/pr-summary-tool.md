---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/ci/pr-automation.md
lastVerified: '2026-03-18'
---
# PR Summary Tool I/O Spec (#407)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

正規化アーティファクトを読み取り、PR 向けの単一サマリブロックを出力する集約ツールの current-state I/O 仕様です。入力（verify-lite / policy / optional assurance・quality・hook-feedback など）、出力（Markdown/JSON サイドカー）、CLI の概略、検証ノートを記載します。

Purpose
- Define a stable contract for the current PR summary renderer that reads normalized artifacts and emits a single summary block for PRs.

Inputs (read-only)
- Required baseline:
  - `artifacts/verify-lite/verify-lite-run-summary.json`
- Current optional inputs:
  - `artifacts/summary/combined.json`
  - `coverage/coverage-summary.json` or `artifacts/coverage/coverage-summary.json`
  - `artifacts/domain/replay.summary.json`
  - `artifacts/bdd/scenarios.json`
  - `artifacts/properties/summary.json`
  - `artifacts/properties/ltl-suggestions.json`
  - `artifacts/formal/gwt.summary.json`
  - `artifacts/ci/policy-gate-summary.json`
  - `artifacts/assurance/assurance-summary.json`
  - `artifacts/quality/quality-scorecard.json`
  - `artifacts/agents/hook-feedback.json`
  - `artifacts/formal/formal-aggregate.json`
  - `formal/summary.json` or `artifacts/hermetic-reports/formal/summary.json`
  - `artifacts/ci/harness-health.json`

Output
- A single Markdown block suitable for PR description or bot comment.
- Current Markdown path: `artifacts/summary/PR_SUMMARY.md`
- Current machine-readable sidecar (optional): `artifacts/summary/combined.json`

Output Structure (JSON example, simplified)
```json
{
  "verifyLite": { "status": "pass" },
  "discoveryPack": {
    "mode": "report-only",
    "validateStatus": "warn",
    "blockingOpenQuestions": 1,
    "orphanApprovedRequirements": 0,
    "orphanApprovedBusinessUseCases": 0
  },
  "policyGate": { "status": "pass", "decision": "allow" },
  "assurance": { "warningClaims": 0, "missingRequiredLanes": 0 },
  "qualityScorecard": { "overallStatus": "pass", "score": 1 },
  "hookFeedback": { "blockingReasons": [], "nextActions": [] }
}
```

CLI Outline
```
SUMMARY_LANG=ja SUMMARY_MODE=detailed \
node scripts/summary/render-pr-summary.mjs
```

Notes
- `pr-ci-status-comment.yml` の `summarize` job が canonical producer です。
- `render-pr-summary.mjs` は `artifacts/summary/combined.json` を優先入力としつつ、coverage / replay / BDD / properties / GWT / formal fallback を個別に read-only 参照し、`artifacts/summary/PR_SUMMARY.md` を更新します。
- Discovery Pack 行は `artifacts/verify-lite/verify-lite-run-summary.json` の top-level `discoveryPack` と `steps.discoveryPackValidation` / `steps.discoveryPackCompile` から生成します。
- formal 行は `combined.json.formal` を優先し、fallback として `formal/summary.json` または `artifacts/hermetic-reports/formal/summary.json` を参照します。Formal Summary v1/v2 は renderer の直接入力ではなく、上流 producer / validator の契約です。
- `verify-lite-run-summary` は baseline input、assurance / scorecard / hook-feedback / harness-health は存在時のみ append されます。
- `pr-ci-status-comment.yml` は renderer の出力後に `harness-health` / `change-package` / `plan-artifact` / `hook-feedback` / downloaded `quality-scorecard.md` を `artifacts/summary/PR_SUMMARY.md` に追記します。
- Validation / producer/consumer の最新一覧は `docs/quality/ARTIFACTS-CONTRACT.md` と `docs/reference/CONTRACT-CATALOG.md` を優先します。
## Sidecar Combined JSON
- Recommended path: `artifacts/summary/combined.json`
- Include only the normalized fields that current consumers actually read. Discovery Pack status は combined sidecar ではなく `verify-lite-run-summary.json` から読むため、`combined.json` に重複保持しません。

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
