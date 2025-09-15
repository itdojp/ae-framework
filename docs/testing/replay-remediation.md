# Replay Remediation Spec (#411)

> 🌍 Language / 言語: English | 日本語

Purpose
- Provide a minimal, machine-readable suggestion when replay violates invariants.

Schema (example)
```json
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
- Keep format stable and small; link to `formal/summary.json` in PR summary.
