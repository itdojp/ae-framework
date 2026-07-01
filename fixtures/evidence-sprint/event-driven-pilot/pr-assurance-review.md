# PR Assurance Review Preview: EVIDENCE-012 Event-driven Pilot

This preview is the reviewer-facing traceability surface for Issue #3573. It is
fixture-backed and report-only: the pilot exercises the event-driven domain
preset, trace validation, and the existing conformance sample without adding a
runtime event processor.

## Traceability chain

| Stage | Artifact | Status | Reviewer check |
| --- | --- | --- | --- |
| Issue intent | <https://github.com/itdojp/ae-framework/issues/3573> | present | Confirms event-driven/conformance pilot scope and required evidence path. |
| Scope memo / pilot report | `docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md` | present | Confirms fixture-backed boundary and unsupported-claim exclusions. |
| Ordering / invariant assumptions | `fixtures/evidence-sprint/event-driven-pilot/invariant-assumptions.md` | present | Confirms timestamp order, causal order, inventory invariants, and escalation rule. |
| Domain preset report | `fixtures/evidence-sprint/event-driven-pilot/domain-preset-report.json` / `.md` | present | Confirms required inputs, starting command, expected artifacts, and escalation rule from `event-driven-domain`. |
| Conformance evidence | `fixtures/evidence-sprint/event-driven-pilot/conformance-evidence.md` | present | Shows trace validation pass and report-only conformance findings. |
| ExecPlan v2 | `fixtures/evidence-sprint/event-driven-pilot/exec-plan.v2.json` | present | Confirms task graph, evidence requirements, stop rules, rollback, and report-only risk decision. |
| Measurement report | `fixtures/evidence-sprint/event-driven-pilot/measurement-report.json` | present | Confirms all eight #3569 metric slots are represented for the pilot. |
| Req2run metrics | `fixtures/metrics/req2run/expected.req2run-metrics.json` | present | Links the existing report-only requirement-to-runnable metric surface. |
| Review completeness | `pr-review-completeness` | pending closeout | Confirm unresolved threads are zero after Copilot/Codex review. |
| Completion audit | Issue #3573 post-merge comment | pending closeout | Confirm final required/advisory/stale/skipped surfaces are separated. |

## Event/invariant review checklist

- [ ] Ordering assumptions are explicit before conformance results are used.
- [ ] The report distinguishes trace-schema validation from domain correctness.
- [ ] Existing conformance sample failures are treated as report-only evidence,
      not as newly introduced blocking defects.
- [ ] Escalation criteria are visible for nondeterminism, invariant failure,
      disputed ordering, or payment/auth/safety-critical domains.
- [ ] The domain preset report records required inputs, starting command,
      expected artifacts, and escalation rule.

## Planned local verification

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

## Known pre-closeout limitations

- The PR number, final head SHA, review rework count, full CI rollup, and
  completion audit comment are not known at preview creation time.
- The conformance sample intentionally surfaces report-only violations; it is
  evidence for escalation and review traceability, not production correctness.
- This preview is evidence for review traceability; it is not approval or merge
  authority.
