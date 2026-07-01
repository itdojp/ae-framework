---
docRole: derived
canonicalSource:
- docs/product/PILOT-RUNBOOK-2026Q3.md
- docs/guides/external-pilot-onboarding.md
- docs/product/EFFECTIVENESS-METRICS.md
- docs/product/REQ2RUN-METRICS.md
- docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md
- docs/templates/evidence-sprint-pilot-report.md
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency
---

# Pilot Evidence Template 2026 Q3

> Language / 言語: English | 日本語

---

## English

This template captures report-only evidence for the first external agent PR
assurance pilot. It is intentionally redaction-first: live PR identifiers,
reviewer names, comments, file paths, and exact timestamps stay private unless
the pilot maintainer approves publication.

Use this template with `docs/product/PILOT-RUNBOOK-2026Q3.md`. For Evidence Sprint #3570/#3572/#3573 observations, use `docs/templates/evidence-sprint-pilot-report.md` as the per-observation report and keep this document as the external-pilot rollup template. If no live pilot
has run, use the synthetic example under `examples/pilot-redacted/` and mark the
status as `pilot-ready, not executed`.

### 1. Pilot header

| Field | Value |
| --- | --- |
| Pilot ID | `<pilot-id>` |
| Repository | `<redacted repo id or private URL>` |
| Pilot maintainer | `<name or redacted owner>` |
| ae-framework operator | `<name>` |
| Evidence window | `<date range or not started>` |
| Publication owner | `<approver>` |
| Publication status | `approved` / `aggregate only` / `private` / `not approved for publication` |
| Overall status | `pilot-ready` / `in progress` / `paused` / `aborted` / `completed` |

### 2. Consent and redaction record

- Raw output viewers: `<people or roles>`
- PR URL handling: `private artifact only` / `redacted` / `approved for publication`
- Timing handling: `exact private only` / `duration only` / `date bucket` / `not collected`
- Reviewer identity handling: `private only` / `role alias` / `approved`
- Comment handling: `category summary only` / `redacted excerpt approved` / `private only`
- ACP-097 use: `aggregate only` / `redacted case note` / `synthetic fixture` / `not approved`

### 3. Five-PR collection table

| pilot_pr_id | producer | issue_scope | review_surface_link | metrics_json / req2run_metrics_json | reviewer_disposition | limitations | publication_status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `pilot-pr-1` | `<agent/human/ci/mixed>` | `<redacted scope>` | `<private URL or local md>` | `<path or not_collected; include req2run report path when collected>` | `<merge/request changes/defer/block/not_collected>` | `<missing data / redaction / CI note>` | `<approved/aggregate only/private/not approved for publication>` |
| `pilot-pr-2` | `<agent/human/ci/mixed>` | `<redacted scope>` | `<private URL or local md>` | `<path or not_collected>` | `<merge/request changes/defer/block/not_collected>` | `<missing data / redaction / CI note>` | `<approved/aggregate only/private/not approved for publication>` |
| `pilot-pr-3` | `<agent/human/ci/mixed>` | `<redacted scope>` | `<private URL or local md>` | `<path or not_collected>` | `<merge/request changes/defer/block/not_collected>` | `<missing data / redaction / CI note>` | `<approved/aggregate only/private/not approved for publication>` |
| `pilot-pr-4` | `<agent/human/ci/mixed>` | `<redacted scope>` | `<private URL or local md>` | `<path or not_collected>` | `<merge/request changes/defer/block/not_collected>` | `<missing data / redaction / CI note>` | `<approved/aggregate only/private/not approved for publication>` |
| `pilot-pr-5` | `<agent/human/ci/mixed>` | `<redacted scope>` | `<private URL or local md>` | `<path or not_collected>` | `<merge/request changes/defer/block/not_collected>` | `<missing data / redaction / CI note>` | `<approved/aggregate only/private/not approved for publication>` |

### 4. Per-PR detail block

Copy one block for each pilot PR.

```markdown
#### `<pilot-pr-id>`

- Producer: `<agent/human/ci/mixed>`
- Issue scope: `<redacted scope>`
- Required checks collected: `<names or not_collected>`
- Metrics JSON: `<path or not_collected>`
- Req2run metrics JSON: `<path or not_collected>`
- Metrics Markdown / review surface: `<path or private URL>`
- Review surface posted: `yes` / `no` / `preview only`
- Reviewer disposition: `merge` / `request changes` / `defer` / `block` / `not_collected`
- Review-thread total: `<number or not_collected>`
- Final unresolved threads: `<number or not_collected>`
- CI rerun classification: `<summary or not_collected>`
- Timing metric: `<duration only / not_collected>`
- Req2run metrics: `time_to_first_runnable_verification_minutes=<duration/not_collected>`, `spec_task_evidence_coverage=<ratio/not_collected>`, `deterministic_replay_pass_rate=<ratio/not_collected>`, `manual_intervention_count=<count/not_collected>`, `evidence_review_completeness=<ratio/not_collected>`
- Maintainer feedback: `<useful / missing / confusing / noisy / not_collected>`
- Limitations: `<redaction, missing data, CI instability, or reviewer note>`
- Publication status: `approved` / `aggregate only` / `private` / `not approved for publication`
```

### 5. Aggregation block for ACP-097

Use only approved aggregate or redacted data.

| Metric | Value | Publication status | Note |
| --- | --- | --- | --- |
| Planned PR count | `5` | aggregate only | Replace with live count when collected. |
| Collected PR count | `<0-5>` | aggregate only | Do not imply execution when count is `0`. |
| Posted review surfaces | `<count>` | aggregate only | Count only maintainer-approved posts. |
| Final unresolved threads | `<count or not_collected>` | aggregate only | Keep live links private. |
| `ci_rerun_count` | `<count or not_collected>` | aggregate only | Separate stale/superseded from current failures. |
| Timing metrics | `<duration only or not_collected>` | aggregate only/private | Publish only if maintainer approves. |
| Req2run metrics | `<aggregate ratios/counts or not_collected>` | aggregate only/private | Use `docs/product/REQ2RUN-METRICS.md`; synthetic fixture values do not prove adoption-speed. |
| Reviewer feedback categories | `<useful/missing/confusing/noisy counts>` | aggregate only | Do not copy raw comments unless approved. |

### 6. Required limitations paragraph

Use this paragraph when a pilot is not yet executed:

```text
This is a pilot-ready evidence template and synthetic redacted example. No live
external repository PR has been collected yet, and no adoption-speed, code
quality, req2run improvement, or agent-vendor comparison claim is supported by
this placeholder.
```

---

## 日本語

この template は、最初の external agent PR assurance pilot で report-only evidence を取得するためのものです。redaction-first を前提にし、live PR identifier、reviewer name、comment、file path、exact timestamp は、pilot maintainer が公開承認しない限り private に保持します。

`docs/product/PILOT-RUNBOOK-2026Q3.md` と併用します。Live pilot が未実施の場合は `examples/pilot-redacted/` の synthetic example を使い、status を `pilot-ready, not executed` と明記します。

### 1. Pilot header

| Field | Value |
| --- | --- |
| Pilot ID | `<pilot-id>` |
| Repository | `<redacted repo id or private URL>` |
| Pilot maintainer | `<name or redacted owner>` |
| ae-framework operator | `<name>` |
| Evidence window | `<date range or not started>` |
| Publication owner | `<approver>` |
| Publication status | `approved` / `aggregate only` / `private` / `not approved for publication` |
| Overall status | `pilot-ready` / `in progress` / `paused` / `aborted` / `completed` |

### 2. Consent / redaction record

- Raw output viewers: `<people or roles>`
- PR URL handling: `private artifact only` / `redacted` / `approved for publication`
- Timing handling: `exact private only` / `duration only` / `date bucket` / `not collected`
- Reviewer identity handling: `private only` / `role alias` / `approved`
- Comment handling: `category summary only` / `redacted excerpt approved` / `private only`
- ACP-097 use: `aggregate only` / `redacted case note` / `synthetic fixture` / `not approved`

### 3. 5 PR collection table

| pilot_pr_id | producer | issue_scope | review_surface_link | metrics_json / req2run_metrics_json | reviewer_disposition | limitations | publication_status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `pilot-pr-1` | `<agent/human/ci/mixed>` | `<redacted scope>` | `<private URL or local md>` | `<path or not_collected; req2run report 収集時はその path を含める>` | `<merge/request changes/defer/block/not_collected>` | `<missing data / redaction / CI note>` | `<approved/aggregate only/private/not approved for publication>` |
| `pilot-pr-2` | `<agent/human/ci/mixed>` | `<redacted scope>` | `<private URL or local md>` | `<path or not_collected>` | `<merge/request changes/defer/block/not_collected>` | `<missing data / redaction / CI note>` | `<approved/aggregate only/private/not approved for publication>` |
| `pilot-pr-3` | `<agent/human/ci/mixed>` | `<redacted scope>` | `<private URL or local md>` | `<path or not_collected>` | `<merge/request changes/defer/block/not_collected>` | `<missing data / redaction / CI note>` | `<approved/aggregate only/private/not approved for publication>` |
| `pilot-pr-4` | `<agent/human/ci/mixed>` | `<redacted scope>` | `<private URL or local md>` | `<path or not_collected>` | `<merge/request changes/defer/block/not_collected>` | `<missing data / redaction / CI note>` | `<approved/aggregate only/private/not approved for publication>` |
| `pilot-pr-5` | `<agent/human/ci/mixed>` | `<redacted scope>` | `<private URL or local md>` | `<path or not_collected>` | `<merge/request changes/defer/block/not_collected>` | `<missing data / redaction / CI note>` | `<approved/aggregate only/private/not approved for publication>` |

### 4. PR detail block

PR ごとに 1 block コピーします。

```markdown
#### `<pilot-pr-id>`

- Producer: `<agent/human/ci/mixed>`
- Issue scope: `<redacted scope>`
- Required checks collected: `<names or not_collected>`
- Metrics JSON: `<path or not_collected>`
- Req2run metrics JSON: `<path or not_collected>`
- Metrics Markdown / review surface: `<path or private URL>`
- Review surface posted: `yes` / `no` / `preview only`
- Reviewer disposition: `merge` / `request changes` / `defer` / `block` / `not_collected`
- Review-thread total: `<number or not_collected>`
- Final unresolved threads: `<number or not_collected>`
- CI rerun classification: `<summary or not_collected>`
- Timing metric: `<duration only / not_collected>`
- Req2run metrics: `time_to_first_runnable_verification_minutes=<duration/not_collected>`, `spec_task_evidence_coverage=<ratio/not_collected>`, `deterministic_replay_pass_rate=<ratio/not_collected>`, `manual_intervention_count=<count/not_collected>`, `evidence_review_completeness=<ratio/not_collected>`
- Maintainer feedback: `<useful / missing / confusing / noisy / not_collected>`
- Limitations: `<redaction, missing data, CI instability, or reviewer note>`
- Publication status: `approved` / `aggregate only` / `private` / `not approved for publication`
```

### 5. ACP-097 aggregation block

承認済みの aggregate または redacted data だけを使います。

| Metric | Value | Publication status | Note |
| --- | --- | --- | --- |
| Planned PR count | `5` | aggregate only | live count 収集後に置き換える。 |
| Collected PR count | `<0-5>` | aggregate only | `0` の場合、実施済みに見せない。 |
| Posted review surfaces | `<count>` | aggregate only | maintainer 承認済み post だけを数える。 |
| Final unresolved threads | `<count or not_collected>` | aggregate only | live link は private に保持する。 |
| `ci_rerun_count` | `<count or not_collected>` | aggregate only | stale / superseded と current failure を分ける。 |
| Timing metrics | `<duration only or not_collected>` | aggregate only/private | maintainer 承認時だけ公開する。 |
| Req2run metrics | `<aggregate ratios/counts or not_collected>` | aggregate only/private | `docs/product/REQ2RUN-METRICS.md` を使う。Synthetic fixture 値は adoption-speed の証明ではない。 |
| Reviewer feedback categories | `<useful/missing/confusing/noisy counts>` | aggregate only | 承認なしに raw comment をコピーしない。 |

### 6. Required limitations paragraph

Pilot が未実施の場合はこの paragraph を使います。

```text
This is a pilot-ready evidence template and synthetic redacted example. No live
external repository PR has been collected yet, and no adoption-speed, code
quality, req2run improvement, or agent-vendor comparison claim is supported by
this placeholder.
```
