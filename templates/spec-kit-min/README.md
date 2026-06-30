# Spec Kit Minimal Template (Seed)

This folder is a seed template for a minimal Spec & Verification Kit setup.
Copy this directory into a new repository and populate the spec/test artifacts.

## What this seed contains
- `spec/bdd/` placeholder for Gherkin features and steps
- `tests/property/` placeholder for property-based tests

## Suggested next steps
1. Copy templates from `docs/templates/spec-kit/` into your repo:
   - `bdd-template.feature` -> `spec/bdd/features/<feature>.feature`
   - `bdd-steps.template.js` -> `spec/bdd/steps/<feature>.steps.js`
   - `property-template.md` -> design your `tests/property/*.test.ts`
2. Add or adapt scripts in your `package.json`:
   - `pnpm lint`, `pnpm types:check`, `pnpm run test:fast`
   - `pnpm run test:property`
   - `pnpm run spec-kit-min:verify`
3. Add a workflow from `docs/templates/ci/spec-kit-min.workflow.yml`.
4. Add requirement or trace markers such as `@trace:REQ-001` to BDD/property examples so the activation summary can connect checks to spec fragments.

## Local activation command

```bash
pnpm run spec-kit-min:verify
```

Use authored BDD/property suites only after their steps and generators are ready:

```bash
pnpm run spec-kit-min:verify -- --run-custom-suites
```

The activation runner writes `artifacts/spec-kit-min/activation-summary.json` and
`artifacts/spec-kit-min/activation-summary.md`. If custom suites are discovered
without `--run-custom-suites`, the summary explains that the built-in
`test:property` harness smoke path is distinct from authored property suites.

Note: This is a seed only. Copy the runner or provide an equivalent script in the
consumer repository before treating this as a standalone generated project.
