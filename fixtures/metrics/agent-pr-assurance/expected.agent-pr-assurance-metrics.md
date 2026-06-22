# Agent PR Assurance Metrics

Report-only metrics for itdojp/ae-framework#3526. Producer output and metrics are review evidence, not approval.

- generatedAt: `2026-06-23T00:00:00.000Z`
- source: `offline-fixture`
- PR state: `MERGED`
- mergeStateStatus: `CLEAN`

## Product metrics

| Metric | Value |
| --- | --- |
| review_threads_total | 4 |
| review_threads_unresolved_final | 0 |
| scope_drift_finding_count | 2 |
| missing_evidence_finding_count | 4 |
| selected_high_risk_claim_count | 2 |
| ci_rerun_count | 1 |
| time_to_merge_minutes | 24 |
| policy_gate_false_positive_count | not_collected |
| policy_gate_false_negative_count | not_collected |

## Required checks

| Check | Classification | Attempts | Stale/superseded failures | Latest conclusion |
| --- | --- | ---: | ---: | --- |
| gate | success | 2 | 1 | SUCCESS |
| policy-gate | success | 1 | 0 | SUCCESS |
| verify-lite | success | 1 | 0 | SUCCESS |

## Limitations

- offline fixture mode: GitHub API was not called.
- policy_gate_false_positive_count and policy_gate_false_negative_count require manual annotation; they are not inferred from reruns.
