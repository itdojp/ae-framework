# Replay Test Scripts & CI (#411)

Package Scripts (example)
```json
{
  "scripts": {
    "test:replay": "node scripts/replay.js",
    "test:replay:focus": "node scripts/replay.js --focus=$TRACE_ID"
  }
}
```

CI Snippet
```yaml
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
