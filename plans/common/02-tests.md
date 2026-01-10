# ExecPlan: Common / 02-tests

## Goal
- Create unit/integration/property test skeletons aligned with the spec kit.

## Inputs
- `spec/bdd/<domain>-sample.md`
- `spec/properties/<domain>-sample.md`
- `spec/api/<domain>-openapi.yml` (if present)

## Outputs
- `tests/unit/<domain>.*.test.ts`
- `tests/integration/<domain>.*.test.ts`
- `tests/property/<domain>.*.test.ts`
- TODO list for missing data, fixtures, and edge cases

## Steps
1) Map BDD scenarios to test file skeletons.
2) Add property tests with generator placeholders.
3) Add integration test skeletons with setup/teardown notes.
4) Record open questions as TODOs in tests.

## Commands (suggested)
- `pnpm test:unit`
- `pnpm test:integration` (if available)
- `pnpm test:property` (if available)

## Notes
- Replace `<domain>` with project-specific labels.
