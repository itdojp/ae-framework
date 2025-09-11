# Replay Runner Usage (scripts/testing/replay-runner.mjs)

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
