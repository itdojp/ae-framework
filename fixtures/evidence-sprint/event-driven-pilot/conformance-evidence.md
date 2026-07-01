# Conformance Evidence Fixture: EVIDENCE-012 event-driven pilot

This fixture records the deterministic verification surface for the
fixture-backed event-driven/conformance pilot. Final PR closeout still relies on
required GitHub checks, `pr-review-completeness`, and the post-merge Issue
completion audit.

## Commands

```bash no-doctest
node scripts/domain-presets/render-preset.mjs --preset templates/domain-presets/event-driven-domain/preset.json --generated-at 2026-07-01T00:00:00.000Z --output-json fixtures/evidence-sprint/event-driven-pilot/domain-preset-report.json --output-md fixtures/evidence-sprint/event-driven-pilot/domain-preset-report.md
node scripts/formal/trace-validate.mjs samples/conformance/sample-traces.json
pnpm -s run conformance:verify:sample
node scripts/exec-plan/validate-v2.mjs --file fixtures/evidence-sprint/event-driven-pilot/exec-plan.v2.json --no-write
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

## Observed local verification before PR publication

- `node scripts/formal/trace-validate.mjs samples/conformance/sample-traces.json`
  exited 0 and validated 2 events against the trace schema.
- `pnpm -s run conformance:verify:sample` exited 0 and wrote
  `artifacts/hermetic-reports/conformance/sample-results.json`.
- The conformance sample's report-only result was `overall = fail` with 23 total
  rules, 22 executed, 13 passed, 9 failed, 1 skipped, and 0 rule errors.
- Violation categories were security policy, compliance rule, business logic,
  and data validation. These are existing sample-fixture findings used to prove
  that the pilot can surface conformance evidence and escalation decisions.

## Evidence boundary

- The conformance failures are not introduced by this PR; this PR records them
  as report-only pilot evidence.
- The event trace validation pass only proves trace-schema compatibility for the
  sample fixture. It does not prove production event ordering, broker behavior,
  or absence of domain defects.
- A future live event-driven pilot must decide whether invariant failures are
  blocking or report-only before merge judgment.
