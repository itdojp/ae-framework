# ExecPlan: Common / 02-tests

## Goal
- Produce runnable test skeletons aligned with specs: unit / integration / property.

## Inputs
- `spec/bdd/*.feature`
- `spec/properties/*.md`
- Schemas (OpenAPI/JSON)

## Outputs
- `tests/unit/...` stubs
- `tests/integration/...` stubs (HTTP or service-level)
- `tests/property/...` stubs referencing invariants

## Steps (suggested)
1) Map BDD scenarios to integration test files (one per resource/group)
2) Add unit tests for deterministic logic/helpers
3) Add property tests with generators placeholders
4) Wire fixtures (app factory, test DB) via existing helpers
5) Mark as skip/pending until impl exists
