---
docRole: narrative
lastVerified: '2026-03-12'
---

# Property Harness Usage (scripts/testing/property-harness.mjs)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

プロパティハーネスの使い方。`npm run test:property`（または `TRACE_ID=...` で特定のトレースに集中）を実行。サマリは `artifacts/properties/summary.json` に出力されます。

Run
```bash
npm run test:property
# or focus a specific trace
TRACE_ID=inv-001 npm run test:property:focus
```

Output (artifacts/properties/summary.json)
```json
{
  "traceId": "inv-001",
  "seed": 123456789,
  "runs": 50,
  "version": "0.1",
  "passed": true,
  "note": "fast-check not available or skipped"
}
```
