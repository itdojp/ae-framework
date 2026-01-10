# ExecPlan: Common / 03-impl

## Goal
- Implement core behaviors to satisfy spec + tests.

## Inputs
- `spec/*` artifacts
- `tests/*` skeletons
- Data model notes (if any)

## Outputs
- `src/<domain>/` implementation
- Minimal migrations/seed data (if applicable)
- Updated tests where necessary

## Steps
1) Implement core data model + APIs.
2) Wire adapters (DB/HTTP/queues) minimally.
3) Fill TODOs in tests to match implementation.
4) Keep changes small and reversible.

## Commands (suggested)
- `pnpm lint`
- `pnpm test:unit`

## Notes
- Replace `<domain>` with project-specific labels.
