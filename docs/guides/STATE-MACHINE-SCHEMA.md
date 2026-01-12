# State Machine Schema (JSON)

## Purpose
Provide a machine-readable SSOT for state machines that can be validated in CI and consumed by tools.

## Files
- Schema: `schema/state-machine.schema.json`
- Sample: `specs/state-machines/order-estimate.sm.json`

## Required fields
- `schemaVersion` (semver)
- `id`
- `initial`
- `states[]`
- `events[]`
- `transitions[]`

## Minimal shape
Each state should include:
- `name`

Each transition should include:
- `from`
- `event`
- `to`
- optional `guard`, `actions[]`

## Validation
- CLI: `node dist/cli.js sm validate specs/state-machines --format json`
- The schema enforces structure and required fields.
- Referencing checks (initial/state/event validity, duplicates, ambiguous transitions) are enforced by `sm validate`.

## Notes
- Use `metadata` for ownership and component hints.
- Keep events and states unique to avoid ambiguous behavior.
