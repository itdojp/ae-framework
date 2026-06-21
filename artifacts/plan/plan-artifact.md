## Plan Artifact

- goal: Add a 15-minute offline BYO-agent assurance quickstart and local demo command for Issue #3509.
- scope: Add the demo runner, package script, quickstart documentation, example README, and tests needed to generate local reviewer-first assurance artifacts without external agent or GitHub API calls.
- risk: risk:high
- approvals required: 1
- source: itdojp/ae-framework#3517 (main <- feat/3509-agent-assurance-demo)

### Assumptions

- A1: The package.json change is limited to a new demo script entrypoint and does not modify dependency declarations or lockfiles.
- A2: The demo remains offline after pnpm dependencies are installed and does not require a GitHub token, hosted LLM API, or live PR.
- A3: Producer output is treated only as evidence input; generated policy output remains report-only for ordinary fast-lane changes.

### Files expected to change

- `package.json`
- `scripts/demo/run-agent-assurance-demo.mjs`
- `scripts/assurance/aggregate-lanes.mjs`
- `tests/unit/scripts/agent-assurance-demo.test.ts`
- `docs/guides/byo-agent-assurance-quickstart.md`
- `docs/guides/byo-agent-assurance-onboarding.md`
- `examples/assurance-control-plane/agent-assurance-demo/README.md`
- `README.md`
- `docs/README.md`
- `artifacts/plan/plan-artifact.json`
- `artifacts/plan/plan-artifact.md`

### Verification plan

- V1: Offline demo command
  - command: `pnpm run demo:agent-assurance`
  - expected evidence: `artifacts/review/agent-assurance-demo/assurance-review.md`, `artifacts/policy/agent-assurance-demo/policy-gate-summary.json`
- V2: Demo runner and aggregate-lanes regression tests
  - command: `pnpm vitest run tests/unit/scripts/agent-assurance-demo.test.ts tests/scripts/assurance-aggregate-lanes.test.ts --reporter dot`
  - expected evidence: `tests/unit/scripts/agent-assurance-demo.test.ts`
- V3: Schema and JSON fixture validation
  - command: `pnpm -s run check:schemas && node scripts/ci/validate-json.mjs`
  - expected evidence: `schema/producer-normalization-summary.schema.json`, `schema/assurance-summary.schema.json`, `schema/policy-gate-summary-v1.schema.json`
- V4: Docs and Context Pack validation
  - command: `pnpm -s run check:doc-consistency && pnpm -s run docs:lint && pnpm -s run context-pack:validate && pnpm -s run context-pack:verify-boundary-map`
  - expected evidence: `docs/guides/byo-agent-assurance-quickstart.md`, `spec/context-pack/boundary-map.json`

### Rollback plan

Revert the quickstart/demo commit and this plan artifact commit; remove generated demo artifacts from any local artifacts directory if present.

### Required human input

- approval=plan-review

### Notes

- package.json is classified as high-risk by policy because it is a package manifest, but this change only adds a script entrypoint.
- run-security is requested so the policy label requirement for package manifest changes can be satisfied.

