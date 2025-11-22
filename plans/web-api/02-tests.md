# ExecPlan: Web API / 02-tests

## Goal
- Produce runnable test skeletons aligned to spec: unit, integration (API), property.

## Inputs
- `spec/bdd/web-api-sample.md`
- `spec/properties/web-api-sample.md`
- `spec/api/openapi.yml`

## Outputs
- `tests/unit/web-api/*.test.ts` skeletons (pure logic/helpers)
- `tests/integration/web-api/*.test.ts` using HTTP client against app factory
- `tests/property/web-api/README-web-api-sample.md` updated with property cases (pseudocode ok)

## Steps
1) Map BDD scenarios to integration test stubs (one file per resource).
2) Add unit test stubs for validation/helpers (focus on deterministic logic).
3) Add property test stubs with generators placeholders referencing invariants.
4) Wire shared fixtures (app factory, test db URL) via existing test helpers.
5) Ensure tests are skipped/pending until implementation exists.

## Commands (suggested)
- `pnpm run test:fast -- --runInBand --passWithNoTests`
