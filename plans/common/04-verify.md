# ExecPlan: Common / 04-verify

## Goal
- Run required verification gates and collect evidence.

## Inputs
- `src/`
- `tests/`
- `spec/`

## Outputs
- CI-ready command list
- Verification logs/artifacts
- Updated PR summary notes

## Steps
1) Run lint/type/unit/integration/property checks.
2) Run mutation quick if applicable.
3) Capture failures and link to spec/test gaps.

## Commands (suggested)
- `pnpm lint`
- `pnpm test:unit`
- `pnpm test:integration` (if available)
- `pnpm test:property` (if available)
- `STRYKER_TIME_LIMIT=0 pnpm run pipelines:mutation:quick` (optional)

## Notes
- Keep evidence links in `docs/flows/<flow>.md`.
