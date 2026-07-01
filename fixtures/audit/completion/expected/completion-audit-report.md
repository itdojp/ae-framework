# Completion Audit Report: PR #3566

- schemaVersion: `completion-audit-report/v1`
- generatedAt: `2026-07-01T00:00:00.000Z`
- repository: `itdojp/ae-framework`
- pullRequest: [#3566 feat(assurance): add domain preset packages](https://github.com/itdojp/ae-framework/pull/3566)
- conclusion: `merged-with-advisory-findings`
- reportOnly: `true`

## Conclusion

Required merge checks passed for PR #3566; advisory workflow findings, skipped runs, and stale runs are recorded separately and do not represent approval authority.

| Signal | Value |
| --- | --- |
| Required checks passed | yes |
| Advisory findings present | yes |
| Stale runs present | yes |
| Local verification passed | yes |
| Audit grants approval | no |

## Required merge checks

| Check | Workflow | Status | Head | Link |
| --- | --- | --- | --- | --- |
| gate | Copilot Review Gate | pass | `50dce20e3920` | [run](https://github.com/itdojp/ae-framework/actions/runs/28489969888/job/84444362440) |
| policy-gate | Policy Gate | pass | `50dce20e3920` | [run](https://github.com/itdojp/ae-framework/actions/runs/28489969882/job/84444333981) |
| verify-lite | Verify Lite | pass | `50dce20e3920` | [run](https://github.com/itdojp/ae-framework/actions/runs/28489969870/job/84444333777) |

## Advisory workflow findings

| Finding | Workflow | Severity | Status | Blocking | Link |
| --- | --- | --- | --- | --- | --- |
| GitHub reported default-branch vulnerability alerts during push/fetch operations. This is visible at workflow/security-advisory level but was not a required merge check for PR #3566. Track separately from required-check pass/fail wording. | Security Analysis / Dependency Audit | warning | warning | no | [source](https://github.com/itdojp/ae-framework/security/dependabot) |

## Skipped workflow runs

| Run | Reason | Link |
| --- | --- | --- |
| coverage-check / coverage | Optional/advisory coverage surfaces are recorded separately from required merge checks. | [source](https://github.com/itdojp/ae-framework/pull/3566/checks) |

## Stale workflow runs

| Run | Status | Stale head | Resolution | Link |
| --- | --- | --- | --- | --- |
| Copilot Review Gate / gate | cancelled | `5a1e2219cb39` | Review threads were resolved, then an unchanged empty amend refreshed the head to 50dce20e392083fce044077ca24a9e12b2810ee1 so required checks could be evaluated on a clean rollup. | [run](https://github.com/itdojp/ae-framework/actions/runs/28489852391/job/84443990897) |

## Local verification

| ID | Command | Status | Note |
| --- | --- | --- | --- |
| targeted-vitest | `pnpm -s exec vitest run tests/scripts/domain-presets.test.ts --reporter dot` | pass | Domain preset renderer regression tests passed: 1 file / 6 tests. |
| verify-lite | `pnpm -s run verify:lite` | pass | Local verify-lite passed with pre-existing lint findings remaining warn-only under the baseline. |

## Audit notes

| ID | Severity | Category | Message |
| --- | --- | --- | --- |
| note-required-vs-advisory | warning | wording | Completion comments must say required checks passed, not that every repository workflow or advisory surface was clean when advisory findings remain visible. |
| note-report-only | info | authority | Completion audit evidence is report-only. It records closeout state and does not approve, merge, or waive human review. |

## Collection boundaries

- Live GitHub APIs called by this renderer: no
- Generated from local fixture: yes
- Approval authority: human maintainers and repository branch protection remain the approval authority
- Report-only reason: The audit distinguishes closeout evidence classes; it does not add a policy-gate block condition.
