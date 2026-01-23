# Counterexample Schema (JSON)

## Purpose
Provide a machine-readable counterexample format that can be validated in CI and reused across verifier backends (TLC / Apalache / conformance).

## Files
- Schema: `schema/counterexample.schema.json`
- Sample: `fixtures/counterexample/sample.counterexample.json`

## Required fields
- `schemaVersion`
- `violated`
- `trace[]`

## Minimal shape
- `violated.kind` should be one of: `INVARIANT`, `LIVENESS`, `THEOREM`, `CONFORMANCE`, `UNKNOWN`
- `violated.name` identifies the violated property
- `trace[]` is an ordered list of steps; each step includes:
  - `index`
  - `state` (free-form object)
  - optional `action`, `meta`

## Validation
- `node scripts/ci/validate-json.mjs` validates the sample along with other schemas in CI.

## Notes
- Backend-specific details should go under `raw` and/or `hints` to keep the core shape stable.
