---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/ci/pr-automation.md
lastVerified: '2026-03-16'
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
  - `artifacts/ci/policy-gate-summary.json`
  - `artifacts/assurance/assurance-summary.json`
  - `artifacts/quality/quality-scorecard.json`
  - `artifacts/agents/hook-feedback.json`
  - `artifacts/formal/formal-aggregate.json`
  - `artifacts/formal/formal-summary-v1.json` or `artifacts/formal/formal-summary-v2.json`
  - `artifacts/ci/harness-health.json`

Output
- A single Markdown block suitable for PR description or bot comment.
- Current Markdown path: `artifacts/summary/PR_SUMMARY.md`
- Current machine-readable sidecar (optional): `artifacts/summary/combined.json`

Output Structure (JSON example, simplified)
```json
{
  "verifyLite": { "status": "pass" },
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
- `render-pr-summary.mjs` は canonical path（`artifacts/summary/combined.json`、`artifacts/verify-lite/verify-lite-run-summary.json`、`artifacts/ci/policy-gate-summary.json`、`artifacts/assurance/assurance-summary.json`、`artifacts/quality/quality-scorecard.json`、`artifacts/agents/hook-feedback.json`、`artifacts/formal/formal-aggregate.json` など）を read-only で参照し、`artifacts/summary/PR_SUMMARY.md` を更新します。
- `verify-lite-run-summary` は baseline input、assurance / scorecard / hook-feedback は存在時のみ append されます。
- `pr-ci-status-comment.yml` は renderer の出力後に `harness-health` / `change-package` / `plan-artifact` / `hook-feedback` / downloaded `quality-scorecard.md` を `artifacts/summary/PR_SUMMARY.md` に追記します。
- Validation / producer/consumer の最新一覧は `docs/quality/ARTIFACTS-CONTRACT.md` と `docs/reference/CONTRACT-CATALOG.md` を優先します。
## Sidecar Combined JSON
- Recommended path: `artifacts/summary/combined.json`
- Include only the normalized fields that current consumers actually read. Legacy adapter/property examples are historical and not the current baseline.

### Example (extended)
```json
{
  "coverage": { "value": 0.82, "threshold": 0.80, "delta": 0.01 },
  "formal": { "result": "pass", "violations": [] },
  "adapters": [ { "name": "lighthouse", "status": "warn", "summary": "Perf 78, A11y 96, PWA 55" } ],
  "failingGwt": [],
  "traceIds": ["inv-001"],
  "replay": { "totalEvents": 12, "byType": { "ItemReceived": 7, "ItemAllocated": 5 }, "violations": [] }
}
```
