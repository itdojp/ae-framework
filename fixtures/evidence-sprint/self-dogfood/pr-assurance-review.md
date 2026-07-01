# PR Assurance Review Preview: EVIDENCE-003 Self-Dogfood

This preview is the reviewer-facing traceability surface for Issue #3570. It is
prepared before Copilot/Codex review and CI closeout, so final review-thread and
completion-audit results are intentionally recorded later in the PR/Issue.

## Traceability chain

| Stage | Artifact | Status | Reviewer check |
| --- | --- | --- | --- |
| Issue intent | <https://github.com/itdojp/ae-framework/issues/3570> | present | Confirms the required evidence path and non-goals. |
| Scope memo | `docs/product/EVIDENCE-SPRINT-SELF-DOGFOOD-2026-07-01.md` | present | Confirms docs/fixtures-only boundary and unsupported-claim exclusions. |
| ExecPlan v2 | `fixtures/evidence-sprint/self-dogfood/exec-plan.v2.json` | present | Confirms task graph, evidence requirements, stop rules, and rollback plan. |
| Domain preset report | not applicable | not required | #3570 is not a Web API or event-driven domain pilot. |
| Measurement report | `fixtures/evidence-sprint/self-dogfood/measurement-report.json` | present | Confirms all eight #3569 metric slots are represented. |
| Req2run metrics | `fixtures/metrics/req2run/expected.req2run-metrics.json` | present | Confirms report-only adoption-readiness metric surface is linked. |
| Verification output | local commands and required GitHub checks | pending closeout | Confirm local checks in PR body and final GitHub checks before merge. |
| Review completeness | `pr-review-completeness` | pending closeout | Confirm unresolved threads are zero after Copilot/Codex review. |
| Completion audit | Issue #3570 post-merge comment | pending closeout | Confirm final required/advisory/stale/skipped surfaces are separated. |

## Reviewer checklist

- [ ] Claims are limited to this scoped self-dogfood run.
- [ ] The report does not claim generalized speed, safety, quality, adoption, or
      agent/vendor superiority.
- [ ] Missing closeout evidence is visible as pending, not silently counted as
      success.
- [ ] `not_collected` timing and review-rework metrics are not interpreted as
      zero.
- [ ] The ExecPlan v2 fixture validates against `schema/exec-plan.v2.schema.json`.
- [ ] The measurement report validates against
      `schema/evidence-sprint-measurement-report.schema.json`.
- [ ] Required checks and `pr-review-completeness` are verified before merge.

## Planned local verification

```bash no-doctest
node scripts/exec-plan/validate-v2.mjs --file fixtures/evidence-sprint/self-dogfood/exec-plan.v2.json --no-write
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
- `time_to_first_runnable_verification_minutes` is `not_collected` because the
  run-start timestamp was not fixed when Issue #3570 was accepted.
- This preview is evidence for review traceability; it is not approval or merge
  authority.
