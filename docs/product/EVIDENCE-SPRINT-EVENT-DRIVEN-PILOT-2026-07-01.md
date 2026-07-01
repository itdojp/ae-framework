---
docRole: derived
canonicalSource:
- docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md
- docs/templates/evidence-sprint-pilot-report.md
- docs/guides/domain-presets.md
- templates/domain-presets/event-driven-domain/preset.json
- docs/ci/completion-audit-report.md
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: node scripts/ci/validate-json.mjs && pnpm -s run check:doc-consistency
---
# Evidence Sprint Event-driven Pilot Report 2026-07-01

> Language / 言語: English | 日本語

This report records Evidence Sprint Issue #3573 as a deterministic,
fixture-backed event-driven / conformance pilot. It applies the existing
`event-driven-domain` domain preset to one replayable inventory trace fixture
and connects Issue intent, ordering and invariant assumptions, trace-specific
conformance verification, ExecPlan v2, measurement, PR review, and
completion-audit boundaries.

It is intentionally report-only. It does not claim generalized review speed,
implementation speed, safety, quality, adoption impact, production event
correctness, or agent/vendor performance.

---

## English

### 1. Observation header

| Field | Value |
| --- | --- |
| Observation id | `evidence-012-event-driven-pilot` |
| Related Issue | #3573 |
| Parent Epic | #3567 |
| Observation type | `event-driven-pilot` |
| Repository | `itdojp/ae-framework` |
| Operator | Codex CLI under maintainer control |
| Evidence window | deterministic fixture window `2026-07-01T10:55:00.000Z` to `2026-07-01T11:04:00.000Z` |
| Execution status | `in_progress` until the PR is merged and the completion-audit Issue comment is posted |
| Publication status | `approved` for repository-local fixture evidence; no private pilot data included |

### 2. Pilot selection and scope

Issue #3573 allows a real event-driven or conformance change when available,
otherwise a deterministic fixture-backed pilot. No live event processor or
workflow implementation target was provided in the Issue, so this run uses the
existing inventory trace fixture and the trace-specific formal conformance
verifier.

Selected event fixture:

- replay sequence: `InventoryAllocated -> InventoryUpdated`;
- source trace: `samples/conformance/sample-traces.json`;
- invariant scope: ordering, non-negative inventory, allocation bounded by
  stock, append-only evidence, and selected-trace conformance summary;
- source artifact:
  `fixtures/evidence-sprint/event-driven-pilot/invariant-assumptions.md`.

In scope:

- render the event-driven domain preset report;
- record ordering and invariant assumptions explicitly;
- run trace validation and trace-specific conformance summary generation;
- add ExecPlan v2 and Evidence Sprint measurement fixtures;
- add a PR assurance review preview and docs navigation link;
- keep final review and CI closeout in the post-merge Issue completion audit.

Out of scope:

- adding or changing a runtime event processor, queue, broker, or workflow;
- policy-gate enforcement promotion;
- using the generic `conformance:verify:sample` data/rules fixture as evidence
  for the selected inventory trace;
- external repository or external-agent API calls;
- generalized product effectiveness, production event-correctness, or
  vendor-comparison claims.

### 3. Domain preset application

Rendered preset report:

- JSON: `fixtures/evidence-sprint/event-driven-pilot/domain-preset-report.json`
- Markdown: `fixtures/evidence-sprint/event-driven-pilot/domain-preset-report.md`
- Source preset: `templates/domain-presets/event-driven-domain/preset.json`

| Preset field | Recorded value |
| --- | --- |
| Preset default starting command | `pnpm run conformance:verify:selected-trace` |
| Selected trace verification command | `pnpm run conformance:verify:selected-trace` |
| Required inputs | selected trace fixture, sample domain events, conformance rules, Context Pack and Boundary Map, ExecPlan v2 |
| Expected required artifacts | selected-trace conformance summary and verify-lite summary |
| Optional evidence surfaces | generic conformance sample result, conformance summary, and assurance summary |
| Escalation rule | escalate for nondeterministic replay, invariant failure, disputed ordering, or payment/auth/safety-critical domain |
| Approval authority | human maintainer, branch protection, and explicit policy; preset output remains guidance |

### 4. Evidence path

| Evidence surface | Artifact / location | Status | Notes |
| --- | --- | --- | --- |
| Issue | <https://github.com/itdojp/ae-framework/issues/3573> | present | The Issue defines the event-driven/conformance pilot goal and required evidence. |
| Scope memo / pilot report | `docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md` | present | This file fixes the fixture-backed scope and unsupported-claim exclusions. |
| Ordering / invariant assumptions | `fixtures/evidence-sprint/event-driven-pilot/invariant-assumptions.md` | present | States timestamp order, causal order, inventory invariants, replay determinism, and escalation. |
| Domain preset report | `fixtures/evidence-sprint/event-driven-pilot/domain-preset-report.json` / `.md` | present | Rendered from `event-driven-domain` without live external APIs. |
| Conformance evidence | `fixtures/evidence-sprint/event-driven-pilot/conformance-evidence.md` | present | Records trace validation pass and the trace-specific formal conformance summary. |
| ExecPlan v2 | `fixtures/evidence-sprint/event-driven-pilot/exec-plan.v2.json` | present | Validated by `schema/exec-plan.v2.schema.json`. |
| Evidence Sprint metrics | `fixtures/evidence-sprint/event-driven-pilot/measurement-report.json` | present | Captures the eight #3569 metric slots for this pilot. |
| Req2run metrics | `fixtures/metrics/req2run/expected.req2run-metrics.json` | present | Existing report-only requirement-to-runnable fixture linked as compatible evidence. |
| PR assurance review surface | `fixtures/evidence-sprint/event-driven-pilot/pr-assurance-review.md` | present | Preview for reviewers before PR review completes. |
| Review completeness | `pr-review-completeness` output | pending closeout | Final unresolved-thread count is recorded after Copilot/Codex review. |
| Completion audit report | Issue #3573 completion comment after merge | pending closeout | Final required checks, advisory findings, stale runs, and local verification are separated. |

### 5. Verification and conformance evidence

| Command | Result | Interpretation | Limitation |
| --- | --- | --- | --- |
| `node scripts/formal/trace-validate.mjs samples/conformance/sample-traces.json` | pass; 2 events validated | The selected trace fixture conforms to the trace schema. | This is schema validation, not proof of production ordering correctness. |
| `pnpm run conformance:verify:selected-trace` | pass; 2 events, 0 schema errors, 0 invariant violations | The selected trace fixture has a trace-specific conformance summary aligned with the inventory replay assumptions. | This is fixture-level evidence and does not prove production event ordering or broker behavior. |
| `pnpm -s run verify:lite` | local pass with warn-only lint baseline | Ordinary repository verification remains available alongside domain evidence. | Local verification does not replace GitHub CI or human review. |

### 6. Metrics snapshot

The measurement fixture is
`fixtures/evidence-sprint/event-driven-pilot/measurement-report.json`.

| Metric | Value | Interpretation | Limitation |
| --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | `9` synthetic fixture minutes | The pilot can represent timing data in the #3569 schema. | Synthetic timing proves instrumentation readiness only; do not infer speed. |
| `evidence_coverage` | `10/12 = 0.8333333333` | Pre-closeout evidence is available for Issue, scope, invariants, preset, conformance evidence, ExecPlan, metrics, req2run, and review preview. | Final review completeness and completion audit are only truthful after PR stabilization and merge. |
| `missing_evidence_count` | `2` | The missing items are expected closeout artifacts. | Lifecycle state, not a failure before merge. |
| `unresolved_claim_count` | `0` | Claims are scoped to traceability, preset application, invariant visibility, and fixture-backed metric readiness. | Does not prove production event behavior or domain correctness. |
| `review_rework_count` | `not_collected` | Review rework is measured after Copilot/Codex and maintainer review threads are handled. | Final count belongs in the completion audit comment. |
| `deterministic_replay_pass` | `true` | The trace validation, selected-trace conformance summary, and fixture rendering are designed for local replay without live external APIs. | Passing replay does not replace GitHub CI or human review. |
| `manual_intervention_count` | `3` | Operator selected a fixture-backed pilot, routed conformance evidence to the selected trace, and must post a completion audit. | These interventions are governance controls, not necessarily defects. |
| `audit_discrepancy_count` | `1` | The report keeps pre-merge evidence separate from final closeout state. | Re-evaluate after the PR is merged and final CI/review state is known. |

### 7. Observations and follow-ups

| Observation | Triggering evidence | Disposition |
| --- | --- | --- |
| No live event-driven implementation target was specified for #3573. | Issue body says to use a real change when available, otherwise fixture-backed. | Use deterministic trace/conformance fixtures and avoid runtime behavior claims. |
| Ordering assumptions must be explicit before conformance summaries are interpreted. | Event-driven preset fit criteria and invariant fixture. | Add `invariant-assumptions.md` and review checklist. |
| The original #3573 pilot had to substitute the generic `conformance:verify:sample` command because it targets `configs/samples/sample-data.json`, not the selected inventory trace. | Package script definition, review feedback, and follow-up #3584. | The event-driven preset now records the selected trace fixture and starts from `pnpm run conformance:verify:selected-trace`; keep `conformance:verify:sample` as optional generic smoke evidence only. |
| Final closeout cannot be known at report creation time. | review completeness and completion audit pending. | Keep final required-check and advisory-finding language in the post-merge Issue comment. |

### 8. Claim boundary

Supported for this observation:

- The #3573 flow has a traceable event-driven evidence chain from Issue intent
  to invariant assumptions, domain preset report, trace-specific conformance evidence, ExecPlan
  v2, measurement fixture, PR assurance review preview, review completeness
  boundary, and completion audit boundary.
- The repository can apply the event-driven domain preset and selected-trace
  verification to deterministic fixtures without live external APIs.
- The pilot exposes ordering and invariant assumptions before conformance
  summaries are interpreted.

Not supported by this observation:

- live production event ordering, broker semantics, workflow correctness, or
  absence of domain defects;
- faster review or faster implementation as a general claim;
- safer code, better quality, or external adoption as generalized claims;
- agent/vendor comparison;
- autonomous approval, merge readiness, waiver, or policy-gate enforcement from
  report-only metrics alone.

---

## 日本語

### 1. 目的

この report は #3573 の event-driven / conformance pilot を deterministic
fixture-backed pilot として記録します。Runtime event processor は追加せず、
`event-driven-domain` preset、ordering / invariant assumptions、trace
validation、trace-specific conformance summary、ExecPlan v2、measurement report、PR assurance
review、completion audit 境界を接続します。

### 2. Scope

対象は event-driven preset report、invariant assumptions、selected-trace conformance evidence、
ExecPlan v2 fixture、Evidence Sprint measurement fixture、review surface、docs
navigation です。Runtime workflow 実装、policy-gate enforcement、外部 repository
pilot、agent vendor 比較、速度・安全性・品質・adoption・production event
correctness の一般 claim は対象外です。

### 3. Evidence path

| Evidence | Artifact | Status |
| --- | --- | --- |
| Issue | #3573 | present |
| Pilot report | `docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md` | present |
| Ordering / invariant assumptions | `fixtures/evidence-sprint/event-driven-pilot/invariant-assumptions.md` | present |
| Domain preset report | `fixtures/evidence-sprint/event-driven-pilot/domain-preset-report.json` / `.md` | present |
| Conformance evidence | `fixtures/evidence-sprint/event-driven-pilot/conformance-evidence.md` | present |
| ExecPlan v2 | `fixtures/evidence-sprint/event-driven-pilot/exec-plan.v2.json` | present |
| Measurement report | `fixtures/evidence-sprint/event-driven-pilot/measurement-report.json` | present |
| PR assurance review | `fixtures/evidence-sprint/event-driven-pilot/pr-assurance-review.md` | present |
| Review / completion audit | `pr-review-completeness`, GitHub checks, #3573 completion comment | closeout pending |

### 4. 主な観測

- #3573 には具体的な live event-driven change が指定されていないため、Issue の条件に従い fixture-backed pilot としました。
- Ordering / invariant assumptions を明示しないと、conformance result の意味を review できません。
- `trace-validate` は sample trace schema validation を pass します。
- `pnpm run conformance:verify:selected-trace` は selected trace に対して 2 events / 0 schema errors / 0 invariant violations の summary を生成します。
- review completeness と completion audit は PR closeout 後に記録します。

### 5. Claim boundary

この pilot が支持するのは、scoped event-driven evidence chain、domain preset 適用、ordering / invariant assumptions の可視性、selected-trace conformance evidence routing、metric collection readiness です。Live event correctness、速度、安全性、品質、adoption、agent/vendor 優位性、autonomous approval は主張しません。
