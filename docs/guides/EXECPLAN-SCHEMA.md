# ExecPlan Schema (JSON)

## Purpose
Provide a machine-readable ExecPlan format that can be validated in CI and reused across agents.

## Files
- Schema: `schema/execplan.schema.json`
- Sample: `fixtures/execplan/sample.execplan.json`

## Required fields
- `schemaVersion`
- `planId`
- `name`
- `steps[]`

## Minimal shape
Each step should include:
- `id`
- `title`
- optional `description`, `inputs`, `outputs`, `commands`, `checks`, `notes`

## Validation
- `node scripts/ci/validate-json.mjs` validates the ExecPlan sample along with other schemas in CI.

## Notes
- Keep `inputs`/`outputs` aligned with Spec Kit and Blueprint artifacts.
- Use `commands[].run` for reproducible CLI snippets.
