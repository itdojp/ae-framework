# Contract Replay Invariants (config via env)

Script: `scripts/testing/replay-runner.mjs`

Env vars
- `REPLAY_DISABLE`: comma-separated invariant ids to disable. Known ids:
  - `allocated_le_onhand` — enforce allocated <= onHand
  - `onhand_min` — enforce onHand >= REPLAY_ONHAND_MIN
- `REPLAY_ONHAND_MIN`: minimum allowed onHand (default: 0)

Examples
- Strict: `pnpm run test:replay:strict`
- Relaxed (allow temporary overallocation): `pnpm run test:replay:relaxed`
- Focused trace: `TRACE_ID=trace-123 pnpm run test:replay:focus`

Notes
- This is a lightweight harness; domain logic applies minimal counters only.
- Wire to real domain reducers when available.

