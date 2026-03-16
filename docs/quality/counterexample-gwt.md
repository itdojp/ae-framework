---
docRole: derived
canonicalSource:
- schema/counterexample.schema.json
- docs/quality/ASSURANCE-MODEL.md
lastVerified: '2026-03-10'
---
# Counterexample → GWT Format (Spec & Examples)

> 🌍 Language / 言語: English | 日本語

Purpose
- Provide both short GWT (human) and machine-readable JSON (for `ae fix`).
- Aligns with current Formal Summary v1/v2 evidence and the legacy compatibility input only when it is still emitted.

Short GWT (example)
```
Given inventory onHand=10
When allocate qty=12
Then invariant "allocated <= onHand" fails
```

Machine JSON (embedded in `artifacts/formal/formal-summary-v1.json` / `artifacts/formal/formal-summary-v2.json`; `formal/summary.json` is legacy compatibility only)
```json
{
  "property": "allocated <= onHand",
  "gwt": "Given inventory onHand=10\nWhen allocate qty=12\nThen invariant \"allocated <= onHand\" fails",
  "json": {
    "given": { "onHand": 10 },
    "when": { "command": "allocate", "qty": 12 },
    "then": { "violated": "allocated <= onHand" }
  }
}
```
