## Plan Artifact

- goal: Render PR assurance review Markdown as the primary reviewer surface for Issue #3510.
- scope: Add a reusable assurance review-surface renderer, route the offline BYO-agent demo through it, add an expected reviewer Markdown fixture, and document the command in quickstart and operations guidance.
- risk: risk:high
- approvals required: 1
- source: itdojp/ae-framework#3518 (main <- feat/3510-pr-review-surface)

### Assumptions

- A1: The package.json change is limited to adding an assurance:review-surface script entrypoint and does not modify dependency declarations or lockfiles.
- A2: The renderer only reads local JSON artifacts and writes Markdown; it does not post GitHub comments, call external APIs, or create merge approvals.
- A3: Missing optional artifacts must stay visible as missing/not provided so reviewers do not infer boundary or claim-evidence success from absence.

### Files expected to change

- `package.json`
- `scripts/assurance/render-pr-review-surface.mjs`
- `scripts/demo/run-agent-assurance-demo.mjs`
- `tests/unit/scripts/agent-assurance-demo.test.ts`
- `examples/assurance-control-plane/agent-assurance-demo/expected/assurance-review.md`
- `examples/assurance-control-plane/agent-assurance-demo/README.md`
- `docs/guides/byo-agent-assurance-quickstart.md`
- `docs/quality/assurance-operations-runbook.md`
- `README.md`
- `artifacts/plan/plan-artifact.json`
- `artifacts/plan/plan-artifact.md`

### Verification plan

- V1: Offline demo and renderer integration
  - command: `pnpm run demo:agent-assurance`
  - expected evidence: `artifacts/review/agent-assurance-demo/assurance-review.md`, `examples/assurance-control-plane/agent-assurance-demo/expected/assurance-review.md`
- V2: Renderer fixture and demo regression tests
  - command: `pnpm vitest run tests/unit/scripts/agent-assurance-demo.test.ts tests/scripts/assurance-aggregate-lanes.test.ts --reporter dot`
  - expected evidence: `tests/unit/scripts/agent-assurance-demo.test.ts`, `examples/assurance-control-plane/agent-assurance-demo/expected/assurance-review.md`
- V3: Full unit regression suite
  - command: `pnpm vitest run tests/unit --reporter dot`
  - expected evidence: `tests/unit/scripts/agent-assurance-demo.test.ts`
- V4: Schema, JSON, docs, and Context Pack checks
  - command: `pnpm -s run check:schemas && node scripts/ci/validate-json.mjs && pnpm -s run check:doc-consistency && pnpm -s run docs:lint && pnpm -s run context-pack:validate && pnpm -s run context-pack:verify-boundary-map && git diff --check`
  - expected evidence: `docs/guides/byo-agent-assurance-quickstart.md`, `docs/quality/assurance-operations-runbook.md`, `spec/context-pack/boundary-map.json`

### Rollback plan

Revert the renderer/demo/docs/test commit and this plan artifact commit; remove any generated artifacts/review/assurance-review.md files from local artifact directories if present.

### Required human input

- approval=plan-review

### Notes

- package.json is classified as high-risk by policy because it is a package manifest, but this change only adds a script entrypoint.
- run-security, enforce-testing, enforce-assurance, and risk:high are requested on PR #3518 to satisfy high-risk policy expectations for package manifest changes.
- Renderer output is a reviewer surface only and intentionally does not automate GitHub PR comment posting.
