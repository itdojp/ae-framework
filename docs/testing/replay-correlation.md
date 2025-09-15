# Replay ↔ Formal Correlation (traceId)

> 🌍 Language / 言語: English | 日本語

Goal
- Correlate replay outcomes with formal verification by shared `traceId`.

Inputs
- `artifacts/domain/replay.summary.json`
- `formal/summary.json`

Correlation JSON (example)
```json
{
  "traceId": "inv-001",
  "replay": { "violatedInvariants": [] },
  "formal": { "result": "pass", "violations": [] },
  "summary": "Replay OK, Formal OK"
}
```

PR Integration
- Include a brief line in PR summary, e.g., `Replay/Formal: OK/OK for inv-001`.
- Optionally merge into `artifacts/summary/combined.json` under `correlation` key.
