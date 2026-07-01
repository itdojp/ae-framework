# PR Assurance Review Preview: EVIDENCE-011 Web API Pilot

This preview is the reviewer-facing traceability surface for Issue #3572. It is
fixture-backed and report-only: the pilot exercises the Web API/BFF domain
preset and an API contract fixture, but it does not add a runtime API endpoint.

## Traceability chain

| Stage | Artifact | Status | Reviewer check |
| --- | --- | --- | --- |
| Issue intent | <https://github.com/itdojp/ae-framework/issues/3572> | present | Confirms Web API pilot scope and required evidence path. |
| Scope memo / pilot report | `docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md` | present | Confirms fixture-backed boundary and unsupported-claim exclusions. |
| API contract evidence | `fixtures/evidence-sprint/web-api-pilot/api-contract.md` | present | Confirms request/response shape, invariants, and escalation trigger. |
| Domain preset report | `fixtures/evidence-sprint/web-api-pilot/domain-preset-report.json` / `.md` | present | Confirms required inputs, starting command, expected artifacts, and escalation rule from `web-api-bff`. |
| ExecPlan v2 | `fixtures/evidence-sprint/web-api-pilot/exec-plan.v2.json` | present | Confirms task graph, evidence requirements, stop rules, rollback, and report-only risk decision. |
| Measurement report | `fixtures/evidence-sprint/web-api-pilot/measurement-report.json` | present | Confirms all eight #3569 metric slots are represented for the pilot. |
| Req2run metrics | `fixtures/metrics/req2run/expected.req2run-metrics.json` | present | Links the existing report-only requirement-to-runnable metric surface. |
| Verification evidence | local validation and required GitHub checks | pending closeout | Confirm local checks in PR body and final GitHub checks before merge. |
| Review completeness | `pr-review-completeness` | pending closeout | Confirm unresolved threads are zero after Copilot/Codex review. |
| Completion audit | Issue #3572 post-merge comment | pending closeout | Confirm final required/advisory/stale/skipped surfaces are separated. |

## API contract review checklist

- [ ] The selected contract is explicitly fixture-backed and does not imply a
      live route exists.
- [ ] Request and response fields are visible enough for a reviewer to identify
      contract evidence.
- [ ] `reportOnly` remains true and cannot be interpreted as approval or merge
      authority.
- [ ] Security/high-assurance escalation triggers are stated before any future
      live route implementation.
- [ ] The domain preset report records required inputs, starting command,
      expected artifacts, and escalation rule.

## Planned local verification

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

## Known pre-closeout limitations

- The PR number, final head SHA, review rework count, full CI rollup, and
  completion audit comment are not known at preview creation time.
- The timing metric is deterministic fixture timing, not observed product
  speed or reviewer throughput.
- This preview is evidence for review traceability; it is not approval or merge
  authority.
