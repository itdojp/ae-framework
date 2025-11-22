# ExecPlan: Web API / 01-spec

## Goal
- Convert business intent into API boundary, BDD examples, and property candidates in JSON/Markdown.

## Inputs
- `requirements/*.md` or issue description
- Existing domain glossary (if any): `docs/glossary.md`

## Outputs
- `spec/api/openapi.yml` (skeleton)
- `spec/bdd/web-api-sample.md` updated with scenarios and examples
- `spec/properties/web-api-sample.md` updated with property list and generators (pseudo-code allowed)
- Trace notes in `docs/flows/web-api-agent.md`

## Steps
1) Summarize intent → list endpoints (CRUD + auth) and data model (1-2 tables) in Markdown.
2) Draft OpenAPI skeleton (paths, schemas, error models). Keep placeholders where unknown.
3) Derive BDD scenarios (happy + edge) and paste into `spec/bdd/web-api-sample.md`.
4) List property-based invariants (idempotency, uniqueness, monotonicity) into `spec/properties/web-api-sample.md`.
5) Validate JSON/YAML/Markdown lint.

## Commands (suggested)
- `pnpm lint:md` (if available) or run markdownlint via editor
- `pnpm ajv:lint` (if schemas touched)
