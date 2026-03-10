---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-03-10'
---
# Property Results Aggregation Patterns (#406)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

プロパティテストの結果集約パターン。推奨は `traceId` ごとの単一 JSON（`artifacts/properties/<traceId>.summary.json`）。代替として配列形式（`artifacts/properties/summary.json`）も可。ただしスキーマは単一要約を想定しているため、配列時は要素ごとに検証します。

Patterns
- Per-trace file (recommended): write one JSON per `traceId` under `artifacts/properties/<traceId>.summary.json`.
- Single-file array (alternative): write an array to `artifacts/properties/summary.json`.

Schema Compatibility
- The schema `docs/schemas/artifacts-properties-summary.schema.json` describes a single summary object.
- For arrays, validate each element with the schema.

Example (single summary)
```json
{
  "traceId": "inv-001",
  "seed": 123456789,
  "runs": 100,
  "version": "0.1",
  "passed": true,
  "stats": { "shrinks": 0, "durationMs": 2450 }
}
```

Example (array of summaries)
```json
[
  { "traceId": "inv-001", "seed": 1, "runs": 50, "version": "0.1", "passed": true },
  { "traceId": "inv-002", "seed": 2, "runs": 50, "version": "0.1", "passed": false }
]
```

CI Tip
- If using arrays, validate with `ajv` using `--allowUnionTypes` and iterate items.
