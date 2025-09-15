# PR Summary Tool I/O Spec (#407)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

正規化アーティファクトを読み取り、PR 向けの単一サマリブロックを出力する集約ツールの I/O 仕様です。入力（adapters/formal/properties）、出力（Markdown/JSON サイドカー）、CLI の概略、検証ノートを記載。

Purpose
- Define a stable contract for a PR summary aggregator that reads normalized artifacts and emits a single summary block for PRs.

Inputs (read-only)
- `artifacts/*/summary.json` (adapters)
- `formal/summary.json` (formal verification)
- `artifacts/properties/summary.json` (property-based tests; single object or array of objects)

Output
- A single Markdown block suitable for PR description or bot comment.
- Recommended machine-readable sidecar (optional): `artifacts/summary/combined.json`.

Output Structure (JSON example)
```json
{
  "coverage": { "value": 0.82, "threshold": 0.80, "delta": 0.01 },
  "formal": { "result": "pass", "violations": [] },
  "adapters": [
    { "name": "lighthouse", "status": "warn", "summary": "Perf 78, A11y 96, PWA 55" },
    { "name": "playwright", "status": "ok", "summary": "12/12 passed" }
  ],
  "failingGwt": [],
  "traceIds": ["inv-001", "inv-002"]
}
```

CLI Outline
```
ae-summary \
  --adapters "artifacts/*/summary.json" \
  --formal "formal/summary.json" \
  --properties "artifacts/properties/summary.json" \
  --out-md stdout \
  --out-json artifacts/summary/combined.json
```

Notes
- Validate inputs against schemas in `docs/schemas/` prior to aggregation.
- When properties summary is an array, validate each element separately.
- Keep implementation outside core; callable from CI.
## Sidecar Combined JSON
- Recommended path: `artifacts/summary/combined.json`
- Include `replay` metrics when available (see replay coverage guide).

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
