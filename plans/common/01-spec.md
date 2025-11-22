# ExecPlan: Common / 01-spec

## Goal
- Turn intent into concrete specs (OpenAPI/Schema + BDD + Property) using Markdown/JSON outputs.

## Inputs
- requirements markdown / issue description
- optional glossary: `docs/glossary.md`

## Outputs
- `spec/api/openapi.yml` (skeleton or updates)
- `spec/bdd/*.feature` with scenarios/examples
- `spec/properties/*.md` with invariants + generators

## Steps (suggested)
1) Summarize intent → resources, operations, error models
2) Draft OpenAPI/Schema (placeholders allowed, keep lintable)
3) Derive BDD scenarios (happy/edge) and write to `.feature`
4) List property invariants and generators
5) Run lint/schema validation if available

## Notes
- Keep outputs in repo paths (no temp dirs). JSON/YAML must be lintable.
