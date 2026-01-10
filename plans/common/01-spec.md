# ExecPlan: Common / 01-spec

## Goal
- Convert intent into boundaries, executable specs, and verification candidates.

## Inputs
- `requirements/*.md` or issue description
- Domain glossary (optional): `docs/glossary.md`
- Existing API/schema notes (optional)

## Outputs
- `spec/api/<domain>-openapi.yml` (optional; skeleton)
- `spec/bdd/<domain>-sample.md` (scenarios + examples)
- `spec/properties/<domain>-sample.md` (invariants + generators)
- Trace notes in `docs/flows/<flow>.md`

## Steps
1) Decide `<domain>` label and scope boundaries.
2) Draft OpenAPI/JSON schema skeleton (paths, schemas, error models).
3) Derive BDD scenarios (happy + edge) and populate `spec/bdd`.
4) List property-based invariants (idempotency, uniqueness, monotonicity).
5) Validate Markdown/YAML/JSON formatting.

## Commands (suggested)
- `pnpm lint:md` (if available)
- `pnpm ajv:lint` (if schemas touched)

## Notes
- Replace `<domain>` and `<flow>` with project-specific labels.
