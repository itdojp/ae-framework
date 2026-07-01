# Conformance Evidence Fixture: EVIDENCE-012 event-driven pilot

This fixture records the deterministic verification surface for the
fixture-backed event-driven/conformance pilot. The selected evidence is tied to
`samples/conformance/sample-traces.json`; `pnpm run conformance:verify:selected-trace`
is the preset-aligned command for that fixture. The generic
`conformance:verify:sample` script targets `configs/samples/sample-data.json`
and remains optional smoke evidence only. Final PR closeout still relies on
required GitHub checks, `pr-review-completeness`, and the post-merge Issue
completion audit.

## Commands

```bash no-doctest
node scripts/domain-presets/render-preset.mjs --preset templates/domain-presets/event-driven-domain/preset.json --generated-at 2026-07-01T00:00:00.000Z --output-json fixtures/evidence-sprint/event-driven-pilot/domain-preset-report.json --output-md fixtures/evidence-sprint/event-driven-pilot/domain-preset-report.md
node scripts/formal/trace-validate.mjs samples/conformance/sample-traces.json
pnpm run conformance:verify:selected-trace
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
- `pnpm run conformance:verify:selected-trace`
  exited 0 and wrote the selected-trace conformance summary for the selected
  inventory trace.
- The selected-trace conformance summary recorded 2 events, 0 schema errors, and
  0 invariant violations, aligning the evidence with the documented
  `InventoryAllocated -> InventoryUpdated` replay assumptions.

## Evidence boundary

- The selected event trace validation and conformance summary only prove
  fixture-level schema and invariant compatibility for
  `samples/conformance/sample-traces.json`; they do not prove production event
  ordering, broker behavior, or absence of domain defects.
- Generic `conformance:verify:sample` findings from `configs/samples` remain
  optional smoke evidence and are not selected-trace evidence for this pilot.
- A future live event-driven pilot must decide whether invariant failures are
  blocking or report-only before merge judgment.
