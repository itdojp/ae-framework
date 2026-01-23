# Agentic Metrics Schema (JSON)

## Purpose
Provide a machine-readable metrics contract for req2run/agentic experiments (cost/tokens/memory/turns/latency) that can be validated in CI.

## Files
- Schema: `schema/agentic-metrics.schema.json`
- Sample: `fixtures/agentic-metrics/sample.agentic-metrics.json`

## Required fields
- `schemaVersion`
- `turns`
- `latencyMs`

## Notes
- `tokens`/`costUsd`/`memoryHitRatio` may be `null` until instrumentation is implemented.
- `turns.avgLen` is interpreted as average output length (chars) derived from `JSON.stringify(output).length` where available.

## Validation
- `node scripts/ci/validate-json.mjs` validates the sample along with other schemas in CI.
