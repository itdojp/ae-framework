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
- Aligns with the legacy `formal/summary.json` counterexample shape and the derived `artifacts/formal/gwt.summary.json` output from `scripts/formal/format-counterexamples.mjs`.

Short GWT (example)
```
Given inventory onHand=10
When allocate qty=12
Then invariant "allocated <= onHand" fails
```

Machine JSON (embedded in legacy `formal/summary.json`; `scripts/formal/format-counterexamples.mjs` can derive `artifacts/formal/gwt.summary.json` from it)
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
