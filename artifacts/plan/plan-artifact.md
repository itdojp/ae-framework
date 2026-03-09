## Plan Artifact

- goal: Define plan-artifact/v1 and require it for high-risk PR pre-review.
- scope: Add schema, generator, validator, policy-gate enforcement, PR summary integration, and operator documentation.
- risk: risk:high
- approvals required: 1
- source: itdojp/ae-framework#2544 (main <- feat/2535-plan-artifact)

### Assumptions

- A1: High-risk PRs can commit plan artifacts under artifacts/plan before review.
- A2: policy-gate checkout contains committed plan artifacts from the PR branch.

### Files expected to change

- `schema/plan-artifact.schema.json`
- `scripts/plan-artifact/generate.mjs`
- `scripts/plan-artifact/validate.mjs`
- `scripts/ci/policy-gate.mjs`
- `.github/workflows/policy-gate.yml`
- `.github/workflows/pr-ci-status-comment.yml`
- `docs/ci/plan-artifact.md`

### Verification plan

- V1: Contract and unit tests
  - command: `pnpm exec vitest run tests/contracts/plan-artifact-contract.test.ts tests/unit/ci/plan-artifact-generate.test.ts tests/unit/ci/plan-artifact-validate.test.ts tests/unit/ci/risk-policy.test.ts tests/unit/ci/policy-gate.test.ts`
  - expected evidence: `tests/contracts/plan-artifact-contract.test.ts`, `tests/unit/ci/policy-gate.test.ts`
- V2: Schema and docs validation
  - command: `node scripts/ci/validate-json.mjs && pnpm -s run check:doc-consistency && pnpm -s run check:ci-doc-index-consistency`
  - expected evidence: `fixtures/plan/sample.plan-artifact.json`, `docs/ci/plan-artifact.md`

### Rollback plan

Revert the plan-artifact schema, scripts, policy-gate integration, and PR summary wiring.

### Required human input

- Confirm the high-risk review scope before implementation proceeds.
- Approve the required verification and rollback plan for the PR.

### Notes

- Change Package remains the after-change evidence artifact; this contract only covers before-change review.

