# Req2run Metrics

Report-only requirement-to-runnable-evidence metrics for reval3-reference-flow-offline-demo. Metrics evaluate ae-framework workflow effectiveness, not agent vendor quality.

- generatedAt: `2026-07-01T00:00:00.000Z`
- source: `offline-fixture`
- referenceFlow: `docs/getting-started/REFERENCE-FLOW.md`
- approvalAuthority: human maintainer; metrics are evidence only

## Metrics

| Metric | Value | Question | Limitation |
| --- | --- | --- | --- |
| time_to_first_runnable_verification_minutes | 34 minutes | How long did it take for a requirement to produce the first runnable verification artifact? | Sensitive to queueing, task size, CI availability, and whether timestamps are synthetic, redacted, or live. |
| spec_task_evidence_coverage | 3/4 (75%) | How many spec or plan tasks have at least one linked evidence artifact? | Coverage says evidence exists; it does not prove the evidence is sufficient, current, or correct. |
| deterministic_replay_pass_rate | 2/2 (100%) | Can the same local inputs be replayed deterministically? | Fixture replay is not a live external-agent benchmark and does not measure raw coding-agent quality. |
| manual_intervention_count | 1 | How many human interventions were required before runnable evidence existed? | Manual intervention taxonomy must be stable before comparing teams or repositories. |
| evidence_review_completeness | 4/5 (80%) | How complete is the review-ready evidence set for the requirement-to-run path? | Completeness does not replace human approval and must not be promoted to a blocking gate without policy work. |

## Source artifacts

| ID | Kind | Path | Present | Required |
| --- | --- | --- | --- | --- |
| requirement | issue-summary | docs/getting-started/REFERENCE-FLOW.md | yes | yes |
| exec-plan | exec-plan/v2 | fixtures/exec-plan/baseline.exec-plan.v2.json | yes | yes |
| verify-lite | verify-lite-run-summary | examples/loop-engineering/success/verify-lite-summary.json | yes | yes |
| loop-summary | loop-run-summary/v1 | fixtures/loop/success.loop-run-summary.json | yes | yes |
| claim-evidence-manifest | claim-evidence-manifest/v1 | fixtures/assurance/sample.claim-evidence-manifest.json | yes | yes |
| assurance-summary | assurance-summary/v1 | fixtures/assurance/sample.assurance-summary.json | yes | no |

## Limitations

- offline fixture mode: no GitHub API or live external agent API was called.
- report-only adoption evidence: this document does not approve, merge, or replace human review.
- agent-vendor comparison is out of scope; metrics evaluate ae-framework workflow effectiveness only.
