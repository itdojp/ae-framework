---
docRole: ssot
lastVerified: 2026-03-11
owner: testing-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Replay Test Scripts & CI (#411)

> 🌍 Language / 言語: English | 日本語

Package Scripts (example)
```text
{
  "scripts": {
    "test:replay": "node scripts/replay.js",
    "test:replay:focus": "node scripts/replay.js --focus=$TRACE_ID"
  }
}
```

CI Snippet
```text
name: replay-tests
on: [push, pull_request]
jobs:
  replay:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: npm ci
      - run: npm run test:replay
```

Notes
- Emit invariant violations with `traceId` and link to `formal/summary.json` when applicable.
- Keep implementation outside core to avoid dependency bloat.

## Env Options
- `REPLAY_DISABLE`: comma-separated flags to disable checks (e.g., `allocated_le_onhand,onhand_min`).
- `REPLAY_ONHAND_MIN`: minimum onHand value for invariant (default `0`).

Example
```text
REPLAY_DISABLE=allocated_le_onhand npm run test:replay
REPLAY_ONHAND_MIN=5 npm run test:replay
```
