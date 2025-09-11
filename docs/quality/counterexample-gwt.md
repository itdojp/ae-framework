# Counterexample → GWT Format (Spec & Examples)

Purpose
- Provide both short GWT (human) and machine-readable JSON (for `ae fix`).
- Aligns with `formal-summary.schema.json` (#407).

Short GWT (example)
```
Given inventory onHand=10
When allocate qty=12
Then invariant "allocated <= onHand" fails
```

Machine JSON (embedded in `formal/summary.json`)
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
