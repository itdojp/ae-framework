# Replay Mapping Example (scripts/testing/replay-runner.mjs)

This note shows a minimal way to prepare inputs and inspect outputs when using the replay runner.

- Input events (sample): `scripts/testing/fixtures/replay-sample.json`
- Failure sample (output-like): `scripts/testing/fixtures/replay-failure.sample.json`

Quick run
```
REPLAY_INPUT=scripts/testing/fixtures/replay-sample.json \
REPLAY_OUTPUT=artifacts/domain/replay.summary.json \
REPLAY_STRICT=0 pnpm tsx scripts/testing/replay-runner.mjs
```

Checks mapping (concept)
- allocated_le_onhand: allocated must not exceed onHand at any time
- onhand_min: onHand must be >= REPLAY_ONHAND_MIN (default 0)

A minimal failure example is provided at `scripts/testing/fixtures/replay-failure.sample.json` to illustrate `violatedInvariants` shape.

