# Verification Evidence Fixture: EVIDENCE-011 Web API Pilot

This file records the deterministic verification surface for the fixture-backed
Web API pilot. Final PR closeout still relies on required GitHub checks,
`pr-review-completeness`, and the post-merge Issue completion audit.

## Verification commands

```bash no-doctest
node scripts/domain-presets/render-preset.mjs --preset templates/domain-presets/web-api-bff/preset.json --generated-at 2026-07-01T00:00:00.000Z --output-json fixtures/evidence-sprint/web-api-pilot/domain-preset-report.json --output-md fixtures/evidence-sprint/web-api-pilot/domain-preset-report.md
node scripts/exec-plan/validate-v2.mjs --file fixtures/evidence-sprint/web-api-pilot/exec-plan.v2.json --no-write
node scripts/ci/validate-json.mjs
pnpm -s run check:schemas
pnpm -s run check:doc-consistency
pnpm -s run docs:lint
pnpm -s run types:check
pnpm -s run context-pack:validate
pnpm -s run context-pack:verify-boundary-map
pnpm -s run verify:lite
git diff --check
```

## Local verification result before PR publication

Observed local status on 2026-07-01 JST: all commands listed above completed
with exit code 0 in the #3572 worktree. `verify:lite` completed with the
repository's existing lint baseline in warn-only mode; no new blocking lint
error was introduced by this docs/fixtures pilot.

## Evidence boundary

- The command set validates the checked-in preset report, ExecPlan v2 fixture,
  measurement report, docs navigation, Context Pack boundary, TypeScript surface,
  and verify-lite baseline.
- This fixture does not replace GitHub Actions, Copilot/Codex review, branch
  protection, or post-merge completion audit.
- The pilot uses a deterministic API contract fixture instead of a live route;
  therefore it supports instrumentation readiness and traceability, not
  production API behavior claims.
