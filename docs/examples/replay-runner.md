---
docRole: narrative
lastVerified: '2026-03-12'
---

# Replay Runner Usage (scripts/testing/replay-runner.mjs)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

リプレイランナーの使い方。`artifacts/domain/events.json` を準備し、`npm run test:replay`（または `TRACE_ID=...` でフォーカス）を実行。結果は `artifacts/domain/replay.summary.json` に出力されます。

Prerequisite
- Prepare `artifacts/domain/events.json` (see docs/ddd/events.md)

Run
```bash
npm run test:replay
# or focus
TRACE_ID=inv-001 npm run test:replay:focus
```

Output (artifacts/domain/replay.summary.json)
```json
{
  "traceId": "inv-001",
  "totalEvents": 3,
  "finalState": { "onHand": 8, "allocated": 2 },
  "violatedInvariants": []
}
```
