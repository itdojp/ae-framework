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
  - `artifacts/assurance/assurance-summary.json`
  - `artifacts/quality/quality-scorecard.json`
  - `artifacts/formal/formal-aggregate.json`
  - `formal/summary.json` or `artifacts/hermetic-reports/formal/summary.json`
  - `artifacts/agents/hook-feedback.md`, `artifacts/ci/harness-health.md`, `artifacts/change-package/change-package.md`, `artifacts/plan/plan-artifact.md` (workflow append stage)

Output
- A single Markdown block suitable for PR description or bot comment.
- Current Markdown path: `artifacts/summary/PR_SUMMARY.md`
- Current machine-readable sidecar: なし（`artifacts/summary/combined.json` は renderer の入力 sidecar）

Normalized input example (`artifacts/summary/combined.json`, simplified)
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

CLI Outline
```
SUMMARY_LANG=ja SUMMARY_MODE=detailed \
node scripts/summary/render-pr-summary.mjs
```

Notes
- `pr-ci-status-comment.yml` の `summarize` job が canonical producer です。
- `render-pr-summary.mjs` は `artifacts/summary/combined.json` を優先入力としつつ、coverage / replay / BDD / properties / GWT / formal fallback を個別に read-only 参照し、`artifacts/summary/PR_SUMMARY.md` を更新します。
- Discovery Pack 行は `artifacts/verify-lite/verify-lite-run-summary.json` の top-level `discoveryPack` から生成します。`steps.discoveryPackValidation` / `steps.discoveryPackCompile` は verify-lite summary 側の実行記録であり、renderer の直接入力ではありません。
- formal 行は `combined.json.formal` を優先し、fallback として `formal/summary.json` または `artifacts/hermetic-reports/formal/summary.json` を参照します。Formal Summary v1/v2 は renderer の直接入力ではなく、上流 producer / validator の契約です。
- `verify-lite-run-summary` は baseline input、assurance / quality-scorecard は renderer が存在時のみ参照します。
- `pr-ci-status-comment.yml` は renderer の出力後に `harness-health` / `change-package` / `plan-artifact` / `hook-feedback` / downloaded `quality-scorecard.md` を `artifacts/summary/PR_SUMMARY.md` へ append します。これらの Markdown artifact は workflow append stage の入力です。
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
