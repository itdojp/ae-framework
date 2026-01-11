# Spec Kit Minimal Template (Seed)

This folder is a seed template for a minimal Spec & Verification Kit setup.
Copy this directory into a new repository and populate the spec/test artifacts.

## What this seed contains
- `specs/bdd/` placeholder for Gherkin features and steps
- `tests/property/` placeholder for property-based tests

## Suggested next steps
1. Copy templates from `docs/templates/spec-kit/` into your repo:
   - `bdd-template.feature` -> `specs/bdd/features/<feature>.feature`
   - `bdd-steps.template.js` -> `specs/bdd/steps/<feature>.steps.js`
   - `property-template.md` -> design your `tests/property/*.test.ts`
2. Add or adapt scripts in your `package.json`:
   - `pnpm lint`, `pnpm types:check`, `pnpm run test:fast`
   - `pnpm run test:property -- --runInBand`
3. Add a workflow from `docs/templates/ci/spec-kit-min.workflow.yml`.

Note: This is a seed only and does not include runtime configuration files.
