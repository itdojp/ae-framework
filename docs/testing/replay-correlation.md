---
docRole: ssot
lastVerified: 2026-03-11
owner: testing-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Replay ↔ Formal Correlation (traceId)

> 🌍 Language / 言語: English | 日本語

Goal
- Correlate replay outcomes with formal verification by shared `traceId`.

Inputs
- `artifacts/domain/replay.summary.json`
- `formal/summary.json`

Correlation JSON (example)
```text
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
