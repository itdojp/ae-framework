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
| ci_rerun_classification_counts | `{"total":1,"stale_cancelled":1,"superseded":0,"same_head_stale":1,"manual_rerun_required":0}` |
| time_to_merge_minutes | 24 |
| policy_gate_false_positive_count | not_collected |
| policy_gate_false_negative_count | not_collected |

## Required checks

Blocking rows are semantic failures. Operational notes are stale, cancelled, superseded, or rerun-needed states and are not policy false-positive annotations.

### Operational notes

| Check | Classification | Review disposition | Attempts | Stale cancelled | Superseded | Same-head stale | Latest conclusion |
| --- | --- | --- | ---: | ---: | ---: | ---: | --- |
| gate | success | operational_note | 2 | 1 | 0 | 1 | SUCCESS |

### Non-blocking checks

| Check | Classification | Review disposition | Attempts | Stale cancelled | Superseded | Same-head stale | Latest conclusion |
| --- | --- | --- | ---: | ---: | ---: | ---: | --- |
| policy-gate | success | non_blocking | 1 | 0 | 0 | 0 | SUCCESS |
| verify-lite | success | non_blocking | 1 | 0 | 0 | 0 | SUCCESS |

## Limitations

- offline fixture mode: GitHub API was not called.
- policy_gate_false_positive_count and policy_gate_false_negative_count require manual annotation; they are not inferred from reruns.
