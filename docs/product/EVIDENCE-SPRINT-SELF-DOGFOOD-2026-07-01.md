---
docRole: derived
canonicalSource:
- docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md
- docs/templates/evidence-sprint-pilot-report.md
- docs/product/REQ2RUN-METRICS.md
- docs/ci/completion-audit-report.md
- docs/reference/EXEC-PLAN-V2.md
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: node scripts/ci/validate-json.mjs && pnpm -s run check:doc-consistency
---
# Evidence Sprint Self-Dogfood Report 2026-07-01

> Language / 言語: English | 日本語

This report records the first scoped self-dogfood flow for Evidence Sprint
Issue #3570. It is a checked-in scope memo and evidence index for one small
repository change: add self-dogfood evidence fixtures and navigation, then take
that change through PR review, CI, and completion audit.

It is intentionally report-only. It does not claim generalized speed, safety,
quality, adoption, or agent-vendor performance.

---

## English

### 1. Observation header

| Field | Value |
| --- | --- |
| Observation id | `evidence-003-self-dogfood` |
| Related Issue | #3570 |
| Parent Epic | #3567 |
| Observation type | `self-dogfood` |
| Repository | `itdojp/ae-framework` |
| Operator | Codex CLI under maintainer control |
| Evidence window | `not_collected`; live start timestamp was not fixed at Issue creation |
| Execution status | `in_progress` until the PR is merged and the completion-audit Issue comment is posted |
| Publication status | `approved` for repository-internal evidence fixtures; no private pilot data included |

### 2. Scope memo

In scope:

- add a schema-validated ExecPlan v2 fixture for the #3570 flow;
- add an Evidence Sprint measurement fixture using the #3569 protocol;
- add a PR assurance review preview that ties Issue intent, plan, verification,
  evidence, review, and audit together;
- add this report as the checked-in scope memo and evidence index;
- link the report from the docs index.

Out of scope:

- runtime behavior changes;
- Context Pack schema or boundary-map changes;
- domain preset contract changes;
- policy-gate enforcement changes;
- external repository pilot execution;
- public effectiveness claims beyond this scoped traceability run.

Context Pack boundary: no new Context Pack slice is required for this small
docs/fixtures change. The explicit scope memo in this file is the scope boundary,
and `spec/context-pack/boundary-map.json` remains read-only evidence that no
mapped implementation slice ownership is modified.

Domain preset boundary: not applicable for #3570 because the selected target is
a docs/fixtures self-dogfood flow, not a Web API or event-driven domain pilot.
#3572 and #3573 use domain preset reports.

### 3. Evidence path

| Evidence surface | Artifact / location | Status | Notes |
| --- | --- | --- | --- |
| Issue | <https://github.com/itdojp/ae-framework/issues/3570> | present | The Issue defines the self-dogfood goal and required evidence path. |
| Scope memo | `docs/product/EVIDENCE-SPRINT-SELF-DOGFOOD-2026-07-01.md` | present | This file fixes the scope, non-goals, and closeout boundary. |
| ExecPlan v2 | `fixtures/evidence-sprint/self-dogfood/exec-plan.v2.json` | present | Validated by `schema/exec-plan.v2.schema.json` and semantic checks. |
| Domain preset report | not applicable | not required | The flow is docs/fixtures-only; domain pilots handle presets separately. |
| Verification output | local commands and required GitHub checks | pending closeout | Local results are recorded before PR creation; final CI state is recorded in the completion audit. |
| Req2run metrics | `fixtures/metrics/req2run/expected.req2run-metrics.json` | present | Existing report-only fixture exercises the requirement-to-runnable metric surface. |
| Evidence Sprint metrics | `fixtures/evidence-sprint/self-dogfood/measurement-report.json` | present | Captures the eight #3569 metric slots for this run. |
| PR assurance review surface | `fixtures/evidence-sprint/self-dogfood/pr-assurance-review.md` | present | Preview for reviewers before PR review completes. |
| Review completeness | `pr-review-completeness` output | pending closeout | Final unresolved-thread count is recorded after Copilot/Codex review. |
| Completion audit report | Issue #3570 completion comment after merge | pending closeout | Final required checks, advisory findings, stale runs, and local verification are separated. |

### 4. Metrics snapshot

The measurement fixture is
`fixtures/evidence-sprint/self-dogfood/measurement-report.json`.

| Metric | Value | Interpretation | Limitation |
| --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | `not_collected` | The run exposed a timing instrumentation gap. | Do not infer speed or onboarding friction. Future pilots must record a start timestamp at run start. |
| `evidence_coverage` | `5/7 = 0.7142857143` | Pre-PR evidence is available for Issue, scope memo, ExecPlan v2, req2run metrics, and PR assurance review. | Final verification output and completion audit are only truthful after PR stabilization and merge. |
| `missing_evidence_count` | `2` | The missing items are expected closeout artifacts: final verification output and completion audit. | This is a lifecycle state, not a pass/fail result before closeout. |
| `unresolved_claim_count` | `0` | The report scopes its claims to traceability and metric collection readiness. | It does not prove code correctness or generalized product effectiveness. |
| `review_rework_count` | `not_collected` | Review rework is measured after Copilot/Codex and maintainer review threads are handled. | Final count belongs in the completion audit comment. |
| `deterministic_replay_pass` | `true` | The evidence package is designed for local schema/docs replay without live external agent APIs. | Passing local replay does not replace GitHub CI or human review. |
| `manual_intervention_count` | `1` | A post-merge completion-audit comment is a required governance closeout action. | This intervention is an intentional control, not necessarily a defect. |
| `audit_discrepancy_count` | `1` | The report keeps pre-merge and final closeout evidence separate to avoid overclaiming. | Re-evaluate after the PR is merged and final CI/review state is known. |

### 5. Claim boundary

Supported for this observation:

- The #3570 flow has a traceable evidence chain from Issue intent to scope memo,
  ExecPlan v2, measurement fixture, PR assurance review preview, verification
  plan, review completeness, and completion audit boundary.
- The repository can represent #3569 Evidence Sprint metrics in a local,
  schema-backed fixture for this self-dogfood run.
- The run exposed at least one concrete improvement: timing metrics need an
  explicit start timestamp at run start, otherwise `not_collected` is the only
  defensible value.

Not supported by this observation:

- faster implementation, faster review, safer code, better quality, or external
  adoption as generalized claims;
- agent/vendor comparison;
- autonomous approval, merge readiness, or policy-gate enforcement from the
  report-only metrics alone;
- publication of private raw review text, exact live timestamps, or sensitive
  pilot data.

### 6. Verification plan

Run the narrow checks before PR publication, then rely on required GitHub checks
for final merge judgment.

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

### 7. Observations and follow-ups

| Observation | Triggering evidence | Disposition |
| --- | --- | --- |
| Start timestamp was not fixed when the Issue was accepted. | `time_to_first_runnable_verification_minutes = not_collected` | Future dogfood/pilot Issues should record a run-start timestamp before first verification. |
| Completion audit cannot be final before merge. | `missing_evidence_count = 2`, `audit_discrepancy_count = 1` | Keep final required-check and advisory-finding language in the post-merge Issue comment. |
| Context Pack was unnecessary for this slice. | Scope memo and target file list | Use explicit scope memo for small docs/fixtures changes, and reserve Context Pack slices for implementation ownership changes. |

### 8. Completion-audit closeout boundary

The final completion-audit report is not embedded in this pre-merge report. It
is posted as an Issue #3570 comment after the PR is merged, because the final PR
head, required checks, advisory workflow findings, stale/skipped runs, review
completeness, and merge result are not knowable before closeout.

---

## 日本語

### 1. 目的

この report は、Evidence Sprint の #3570 self-dogfood を1つの小さな repository change として実施し、Issue intent から PR completion audit までの証跡を追跡するための scope memo です。

対象は ae-framework の workflow traceability と metric collection readiness です。速度、安全性、品質、外部 adoption、agent vendor 比較の一般的な主張は行いません。

### 2. Scope

対象範囲は、ExecPlan v2 fixture、Evidence Sprint measurement fixture、PR assurance review preview、この report、docs index link です。Runtime、policy-gate enforcement、domain preset contract、外部 pilot は対象外です。

Context Pack はこの docs/fixtures slice では新規作成しません。この file を明示的な scope memo とし、boundary-map は変更しません。

### 3. Evidence path

| Evidence | Artifact | Status |
| --- | --- | --- |
| Issue | #3570 | present |
| Scope memo | `docs/product/EVIDENCE-SPRINT-SELF-DOGFOOD-2026-07-01.md` | present |
| ExecPlan v2 | `fixtures/evidence-sprint/self-dogfood/exec-plan.v2.json` | present |
| Measurement report | `fixtures/evidence-sprint/self-dogfood/measurement-report.json` | present |
| Req2run metrics | `fixtures/metrics/req2run/expected.req2run-metrics.json` | present |
| PR assurance review | `fixtures/evidence-sprint/self-dogfood/pr-assurance-review.md` | present |
| Verification output | local commands / GitHub required checks | closeout pending |
| Review completeness | `pr-review-completeness` | closeout pending |
| Completion audit | #3570 closeout comment | closeout pending |

### 4. 主な観測

- `time_to_first_runnable_verification_minutes` は `not_collected`。Issue acceptance 時点で計測開始 timestamp を固定していないため、速度 claim には使えません。
- `evidence_coverage` は pre-closeout 時点で `5/7`。final verification output と completion audit は PR stabilization / merge 後に記録します。
- `manual_intervention_count` は `1`。post-merge completion-audit comment は意図された governance control です。
- `audit_discrepancy_count` は `1`。pre-merge の計画証跡と post-merge の最終監査証跡を分離する必要があります。

### 5. Follow-up

今後の dogfood / pilot では、作業開始時に run-start timestamp を記録し、`time_to_first_runnable_verification_minutes` を `not_collected` ではなく実測値として扱えるようにします。ただし、その値は workflow friction の観測であり、agent/vendor score ではありません。
