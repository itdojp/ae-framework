---
docRole: ssot
lastVerified: 2026-03-16
owner: testing-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Replay Remediation Spec (#411)

> 🌍 Language / 言語: English | 日本語

Purpose
- Provide a minimal, machine-readable suggestion when replay violates invariants.

Schema (example)
```text
{
  "traceId": "inv-007",
  "violatedInvariant": "allocated <= onHand",
  "cause": {
    "event": { "name": "ItemAllocated", "payload": { "qty": 8 } },
    "state": { "onHand": 5, "allocated": 8 }
  },
  "suggestion": {
    "action": "adjust_allocation",
    "params": { "max": 5 },
    "message": "Reduce allocation to <= onHand (5)."
  }
}
```

Notes
- This object can be consumed by `ae fix` or external tooling.
- Keep format stable and small; link `artifacts/domain/replay.summary.json` in PR summary. Use `formal/summary.json` only when the replay/formal traceId correlation still consumes the legacy input, and attach `artifacts/hermetic-reports/formal/summary.json` plus optional `artifacts/formal/formal-summary-v1.json` / `artifacts/formal/formal-summary-v2.json` as current overall formal evidence.
