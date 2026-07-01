---
docRole: derived
canonicalSource:
- docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md
- docs/product/EFFECTIVENESS-METRICS.md
- docs/product/REQ2RUN-METRICS.md
- docs/ci/completion-audit-report.md
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: node scripts/ci/validate-json.mjs && pnpm -s run check:doc-consistency
---
# Evidence Sprint Pilot Report Template

> Language / 言語: English | 日本語

Use this template for #3570 self-dogfood, #3572 Web API pilot, and #3573 event-driven / conformance pilot. Keep private details redacted unless publication is explicitly approved.

---

## English

### 1. Header

| Field | Value |
| --- | --- |
| Observation id | `<evidence-sprint-id>` |
| Related Issue | `<#issue>` |
| Observation type | `self-dogfood` / `web-api-pilot` / `event-driven-pilot` |
| Repository | `<repo or redacted alias>` |
| Operator | `<name or role alias>` |
| Evidence window | `<start/end or not_collected>` |
| Execution status | `planned` / `in_progress` / `completed` / `not_executed` |
| Publication status | `synthetic` / `approved` / `aggregate_only` / `private` / `not_approved_for_publication` |

### 2. Collection boundaries

- Workflow effectiveness only: `true`
- External agent APIs called: `false` (required for this report-only Evidence Sprint metric fixture; if live external-agent data was used, describe the captured source separately and do not present it as an offline fixture)
- Live GitHub APIs called during collection: `false` / `true with captured source noted`
- Agent/vendor comparison: `false`
- Approval authority: `<human maintainer / branch protection / policy>`
- Report-only reason: `<why this report does not approve, merge, waive, or block>`
- Redaction notes: `<private fields, exact timestamps, reviewer identity, comments>`

### 3. Source artifact table

| artifact_id | kind | path_or_url | present | required | schemaVersion | notes |
| --- | --- | --- | --- | --- | --- | --- |
| `issue-intent` | `issue-summary` | `<path/url/redacted>` | `true/false` | `true` | `n/a` | `<scope summary>` |
| `context-or-scope` | `context-pack/scope-memo` | `<path>` | `true/false` | `true` | `<version or n/a>` | `<conflict status>` |
| `exec-plan-v2` | `exec-plan/v2` | `<path>` | `true/false` | `true` | `exec-plan/v2` | `<validation status>` |
| `domain-preset-report` | `domain-assurance-preset-report/v1` | `<path or not_applicable>` | `true/false` | `<true for #3572/#3573>` | `<version>` | `<domain>` |
| `verification-output` | `verify-lite/conformance/api-contract` | `<path>` | `true/false` | `true` | `<version>` | `<pass/fail/not_collected>` |
| `req2run-metrics` | `req2run-metrics/v1` | `<path or not_collected>` | `true/false` | `<issue-dependent>` | `req2run-metrics/v1` | `<summary>` |
| `review-surface` | `pr-assurance-review` | `<path/url>` | `true/false` | `<issue-dependent>` | `n/a` | `<posted/preview/private>` |
| `review-completeness` | `pr-review-completeness` | `<path/json>` | `true/false` | `true` | `n/a` | `<unresolved_threads>` |
| `completion-audit` | `completion-audit-report/v1` | `<path>` | `true/false` | `true` | `completion-audit-report/v1` | `<required/advisory separation>` |

### 4. Metrics

Use the exact metric names from `docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md`.

| Metric | Value | Source artifact refs | Interpretation | Limitation |
| --- | --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | `<minutes or not_collected>` | `<ids>` | `<what this observation supports>` | `<queueing/synthetic/redaction caveat>` |
| `evidence_coverage` | `<numerator>/<denominator> = <ratio or not_collected>` | `<ids>` | `<coverage statement>` | `<sufficiency/freshness caveat>` |
| `missing_evidence_count` | `<count>` | `<ids>` | `<follow-up/publication boundary>` | `<claim-set caveat>` |
| `unresolved_claim_count` | `<count>` | `<ids>` | `<closeout statement>` | `<untracked-claim caveat>` |
| `review_rework_count` | `<count>` | `<ids>` | `<risk discovery or clarity statement>` | `<review-style caveat>` |
| `deterministic_replay_pass` | `true/false/not_collected` | `<ids>` | `<reproducibility statement>` | `<fixture/live caveat>` |
| `manual_intervention_count` | `<count>` | `<ids>` | `<friction or governance statement>` | `<intentional-control caveat>` |
| `audit_discrepancy_count` | `<count>` | `<ids>` | `<closeout wording or follow-up statement>` | `<advisory-surface coverage caveat>` |

### 5. Claim boundary

Allowed claims for this observation:

- `<claim supported by this specific evidence chain>`
- `<claim supported by metric collection readiness>`

Forbidden or not yet supported claims:

- `<speed/safety/quality/adoption/vendor claim not supported>`
- `<publication claim blocked by missing approval or redaction>`

### 6. Follow-up backlog

| Follow-up | Triggering evidence | Owner | Target Issue/PR |
| --- | --- | --- | --- |
| `<follow-up>` | `<metric/artifact>` | `<owner>` | `<issue or not_created>` |

### 7. Required limitations paragraph

```text
This report measures one scoped ae-framework workflow observation. It evaluates workflow evidence collection and review traceability, not raw agent quality or vendor performance. Values marked synthetic, private, redacted, or not_collected do not support public speed, safety, quality, or adoption claims.
```

---

## 日本語

# Evidence Sprint Pilot Report Template

#3570 self-dogfood、#3572 Web API pilot、#3573 event-driven / conformance pilot で使用するテンプレートです。公開承認のない raw PR text、reviewer name、exact timestamp、private comment は記載しません。

## 1. Header

| Field | Value |
| --- | --- |
| Observation id | `<evidence-sprint-id>` |
| Related Issue | `<#issue>` |
| Observation type | `self-dogfood` / `web-api-pilot` / `event-driven-pilot` |
| Repository | `<repo or redacted alias>` |
| Evidence window | `<start/end or not_collected>` |
| Execution status | `planned` / `in_progress` / `completed` / `not_executed` |
| Publication status | `synthetic` / `approved` / `aggregate_only` / `private` / `not_approved_for_publication` |

## 2. Metrics

| Metric | Value | Source artifact refs | Interpretation | Limitation |
| --- | --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | `<minutes or not_collected>` | `<ids>` | `<解釈>` | `<制限>` |
| `evidence_coverage` | `<numerator>/<denominator>` | `<ids>` | `<解釈>` | `<制限>` |
| `missing_evidence_count` | `<count>` | `<ids>` | `<解釈>` | `<制限>` |
| `unresolved_claim_count` | `<count>` | `<ids>` | `<解釈>` | `<制限>` |
| `review_rework_count` | `<count>` | `<ids>` | `<解釈>` | `<制限>` |
| `deterministic_replay_pass` | `true/false/not_collected` | `<ids>` | `<解釈>` | `<制限>` |
| `manual_intervention_count` | `<count>` | `<ids>` | `<解釈>` | `<制限>` |
| `audit_discrepancy_count` | `<count>` | `<ids>` | `<解釈>` | `<制限>` |

## 3. Claim boundary

1回の観測で主張できるのは、そのscopeに限定された evidence chain、metric collection readiness、具体的なfollow-upです。速度改善、安全性、品質改善、外部adoption、agent vendor順位、autonomous approval は主張しません。
