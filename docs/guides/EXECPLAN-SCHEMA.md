---
docRole: derived
canonicalSource:
- schema/execplan.schema.json
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-03-10'
---
# ExecPlan Schema (JSON)

## Purpose
Provide a machine-readable ExecPlan format that can be validated in CI and reused across agents.

## Files
- Schema: `schema/execplan.schema.json`
- Sample: `fixtures/execplan/sample.execplan.json`
- PR orchestration draft schema: `schema/execution-plan-v1.schema.json`
- PR orchestration draft sample: `fixtures/execution-plan/sample.execution-plan.autopilot.json`
- Related state schema: `schema/pr-state-v1.schema.json`

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
- `execplan.schema.json` は汎用契約、`execution-plan-v1.schema.json` は PR自動化向けの専用契約（Issue #2405）として併存運用する。
- delivery-layer 拡張時の責務分離は `docs/architecture/DELIVERY-CONTRACT-COMPATIBILITY-MATRIX.md` を参照する。
