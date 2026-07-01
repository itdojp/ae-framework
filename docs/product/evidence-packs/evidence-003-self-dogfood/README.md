---
docRole: derived
canonicalSource:
- docs/product/EVIDENCE-SPRINT-SELF-DOGFOOD-2026-07-01.md
- docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md
- docs/ci/completion-audit-report.md
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: node scripts/ci/validate-json.mjs && pnpm -s run check:doc-consistency
---
# Evidence Pack: EVIDENCE-003 Self-Dogfood

This evidence pack is the stable link index for the #3570 / #3578 self-dogfood
run. It contains repository-local artifacts and GitHub links that were observed
during closeout. It is report-only and does not create approval authority.

## Canonical public entry

- Case study: `docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md`

## GitHub evidence

| Surface | Link | Notes |
| --- | --- | --- |
| Parent epic | <https://github.com/itdojp/ae-framework/issues/3567> | Evidence Sprint epic. |
| Self-dogfood issue | <https://github.com/itdojp/ae-framework/issues/3570> | Closed after PR #3578 merge. |
| Completion audit comment | <https://github.com/itdojp/ae-framework/issues/3570#issuecomment-4853023127> | Final closeout report for required checks, review completeness, advisory findings, and stale runs. |
| Implementation PR | <https://github.com/itdojp/ae-framework/pull/3578> | Merged docs/fixtures self-dogfood PR. |
| PR final head | `6c9a83f79f75e2f40fcf5ecd7e0418f81069164b` | Empty-amend refresh after review-thread resolution. |
| Merge commit | `7ccdd1dac45a0353582c78c79229a31078485bdd` | Merge commit for PR #3578. |

## Checked-in artifacts

| Artifact | Path | Purpose |
| --- | --- | --- |
| Scope memo / self-dogfood report | `docs/product/EVIDENCE-SPRINT-SELF-DOGFOOD-2026-07-01.md` | Scope, claim boundary, metrics snapshot, observations, and closeout boundary. |
| ExecPlan v2 | `fixtures/evidence-sprint/self-dogfood/exec-plan.v2.json` | Task graph, verification profile, evidence requirements, risk, stop rules, rollback, and output artifacts. |
| Measurement report | `fixtures/evidence-sprint/self-dogfood/measurement-report.json` | #3569 Evidence Sprint metrics for the self-dogfood run. |
| PR assurance review preview | `fixtures/evidence-sprint/self-dogfood/pr-assurance-review.md` | Reviewer-facing traceability checklist. |
| Domain preset report | not applicable | #3570 is a docs/fixtures self-dogfood run; domain preset evidence is deferred to #3572 and #3573. |
| Req2run fixture | `fixtures/metrics/req2run/expected.req2run-metrics.json` | Existing report-only adoption-readiness metric surface referenced by the flow. |

## Verification evidence

Local verification recorded in the completion audit:

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
git diff --cached --check
```

Final required checks on PR #3578:

| Check | Result | Job |
| --- | --- | --- |
| Copilot Review Gate / `gate` | pass | <https://github.com/itdojp/ae-framework/actions/runs/28508732798/job/84503523604> |
| Policy Gate / `policy-gate` | pass | <https://github.com/itdojp/ae-framework/actions/runs/28508732891/job/84503524084> |
| Verify Lite / `verify-lite` | pass | <https://github.com/itdojp/ae-framework/actions/runs/28508732934/job/84503523947> |

Full status-check rollup was inspected before merge. Non-pass entries after
final stabilization: none.

## Review evidence

Final `pr-review-completeness` for PR #3578:

| Field | Value |
| --- | --- |
| `status` | `ok` |
| `reviews` | `6` |
| `review_comments` | `8` |
| `review_threads` | `4` |
| `unresolved_threads` | `0` |
| `generated_count_mismatches` | `0` |
| `missing_review_ids` | `0` |

Actionable review feedback fixed during PR stabilization:

1. Completion audit output now targets the post-merge Issue #3570 comment.
2. ExecPlan v2 required/optional checks now match existing fixture conventions.
3. `evidence_coverage.sourceArtifactRefs` includes `issue-3570`.
4. Docs index wording distinguishes pilot template, self-dogfood report, and Q3 pilot report.

## Metrics and limitations

| Metric / finding | Evidence | Publication boundary |
| --- | --- | --- |
| Evidence coverage | Pre-closeout fixture: `5/7`; final closeout artifacts are linked in this pack. | Do not treat pre-closeout missing evidence as success; final closeout is separate. |
| Review rework | Four actionable review-feedback clusters. | Review count is not an agent/vendor score. |
| Time to first runnable verification | `not_collected`. | No speed or onboarding-time claim is supported. |
| Manual intervention | Post-merge completion audit comment. | Intentional governance control, not automatically product friction. |
| Audit discrepancy | Pre-merge audit not final until after merge. | Completion wording must separate required checks from advisory workflow findings. |

## Unsupported claims

This pack does not support:

- faster implementation or review as a generalized claim;
- safer code or higher quality as a generalized claim;
- external adoption proof;
- agent/vendor comparison;
- autonomous approval, policy waiver, or guaranteed merge readiness.
