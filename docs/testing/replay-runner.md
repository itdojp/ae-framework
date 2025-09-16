# Replay Runner — Environment Options

The replay runner (`scripts/testing/replay-runner.mjs`) supports environment variables to flexibly control checks in CI/local runs.

Environment variables
- `REPLAY_INPUT` (default: `artifacts/domain/events.json`)
  - Path to input events JSON
- `REPLAY_OUTPUT` (default: `artifacts/domain/replay.summary.json`)
  - Path to write replay summary JSON
- `REPLAY_DISABLE` (CSV, default: empty)
  - Disable specific invariants by name (e.g., `allocated_le_onhand,onhand_min`)
- `REPLAY_ONLY` (CSV, default: empty)
  - Run only specified invariants (takes precedence over DISABLE)
- `REPLAY_ONHAND_MIN` (number, default: `0`)
  - Minimum onHand inventory threshold for `onhand_min` invariant
- `REPLAY_STRICT` (`1`/`0`, default: `1`)
  - If `1`, non‑zero exit code on violations; if `0`, always exit `0` (report‑only)
- `REPLAY_PRINT_SUMMARY` (`1`/`0`, default: `0`)
  - If `1`, prints the generated replay summary to stdout

Summary output
- The runner writes a JSON summary containing: `traceId`, `totalEvents`, `finalState`, and `violatedInvariants`.

Example
```
REPLAY_INPUT=artifacts/domain/events.json \
REPLAY_ONLY=allocated_le_onhand \
REPLAY_STRICT=0 \
node scripts/testing/replay-runner.mjs
```

