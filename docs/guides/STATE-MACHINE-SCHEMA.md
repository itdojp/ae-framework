# State Machine Schema (JSON)

## Purpose
Provide a machine-readable SSOT for state machines that can be validated in CI and consumed by tools.

## Files
- Schema: `schema/state-machine.schema.json`
- Specs: `**/*.sm.json` (place your specs in any directory)

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

## Example
```json
{
  "schemaVersion": "1.0.0",
  "id": "order-estimate",
  "initial": "DRAFT",
  "states": [
    { "name": "DRAFT" },
    { "name": "SUBMITTED" }
  ],
  "events": ["SUBMIT", "RESET"],
  "transitions": [
    { "from": "DRAFT", "event": "SUBMIT", "to": "SUBMITTED" },
    { "from": "SUBMITTED", "event": "RESET", "to": "DRAFT" }
  ]
}
```

## Validation
- CLI: `node dist/src/cli/index.js sm validate path/to/specs --format json`
- The schema enforces structure and required fields.
- Referencing checks (initial/state/event validity, duplicates, ambiguous transitions) are enforced by `sm validate`.
- CI: verify-lite runs `sm validate specs/state-machines --format json` and fails on errors.

## Notes
- Use `metadata` for ownership and component hints.
- Keep events and states unique to avoid ambiguous behavior.
