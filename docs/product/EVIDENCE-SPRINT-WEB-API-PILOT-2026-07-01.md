---
docRole: derived
canonicalSource:
- docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md
- docs/templates/evidence-sprint-pilot-report.md
- docs/guides/domain-presets.md
- templates/domain-presets/web-api-bff/preset.json
- docs/ci/completion-audit-report.md
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: node scripts/ci/validate-json.mjs && pnpm -s run check:doc-consistency
---
# Evidence Sprint Web API Pilot Report 2026-07-01

> Language / 言語: English | 日本語

This report records Evidence Sprint Issue #3572 as a deterministic,
fixture-backed Web API pilot. It applies the existing `web-api-bff` domain
preset to one small API-contract fixture and connects Issue intent, ExecPlan v2,
domain preset evidence, API contract evidence, measurement, verification, PR
review, and completion-audit boundaries.

It is intentionally report-only. It does not claim generalized review speed,
implementation speed, safety, quality, adoption impact, production API behavior,
or agent/vendor performance. Any future live Web API or external-pilot claim
must satisfy `docs/product/LIVE-PILOT-ENTRY-CRITERIA.md` first.

---

## English

### 1. Observation header

| Field | Value |
| --- | --- |
| Observation id | `evidence-011-web-api-pilot` |
| Related Issue | #3572 |
| Parent Epic | #3567 |
| Observation type | `web-api-pilot` |
| Repository | `itdojp/ae-framework` |
| Operator | Codex CLI under maintainer control |
| Evidence window | deterministic fixture window `2026-07-01T10:25:00.000Z` to `2026-07-01T10:33:00.000Z` |
| Execution status | `in_progress` until the PR is merged and the completion-audit Issue comment is posted |
| Publication status | `approved` for repository-local fixture evidence; no private pilot data included |

### 2. Pilot selection and scope

Issue #3572 allows a real small API change when available, otherwise a
deterministic fixture-backed pilot. No specific live API implementation target
was provided in the Issue, so this run uses a contract fixture instead of adding
runtime API code.

Selected contract fixture:

- route shape: `GET /internal/evidence-sprint/pilots/{pilotId}`;
- selected pilot id: `evidence-011-web-api-pilot`;
- purpose: return a report-only evidence summary for an internal assurance UI or
  BFF;
- source artifact: `fixtures/evidence-sprint/web-api-pilot/api-contract.md`.

In scope:

- render the Web API/BFF domain preset report;
- record required inputs, starting command, expected artifacts, and escalation
  rule from the preset;
- add a Web API contract fixture and review checklist;
- add ExecPlan v2 and Evidence Sprint measurement fixtures;
- add a PR assurance review preview and docs navigation link;
- keep final review and CI closeout in the post-merge Issue completion audit.

Out of scope:

- adding or changing a runtime API endpoint;
- policy-gate enforcement promotion;
- security/high-assurance lane implementation for a hypothetical live route;
- external repository or external-agent API calls;
- generalized product effectiveness or vendor-comparison claims.

### 3. Domain preset application

Rendered preset report:

- JSON: `fixtures/evidence-sprint/web-api-pilot/domain-preset-report.json`
- Markdown: `fixtures/evidence-sprint/web-api-pilot/domain-preset-report.md`
- Source preset: `templates/domain-presets/web-api-bff/preset.json`

| Preset field | Recorded value |
| --- | --- |
| Starting command | `pnpm run verify:lite` |
| Required inputs | requirement/Issue summary, API contract or route spec, Context Pack and Boundary Map, ExecPlan v2 |
| Expected required artifacts | verify-lite summary, boundary-map report, ExecPlan v2 |
| Optional evidence surface | PR assurance review surface |
| Escalation rule | escalate for authentication, authorization, payment, PII, cross-service contract breakage, or `risk:high` |
| Approval authority | human maintainer, branch protection, and explicit policy; preset output remains guidance |

### 4. Evidence path

| Evidence surface | Artifact / location | Status | Notes |
| --- | --- | --- | --- |
| Issue | <https://github.com/itdojp/ae-framework/issues/3572> | present | The Issue defines the Web API pilot goal and required evidence. |
| Scope memo / pilot report | `docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md` | present | This file fixes the fixture-backed scope and unsupported-claim exclusions. |
| API contract evidence | `fixtures/evidence-sprint/web-api-pilot/api-contract.md` | present | Contains route shape, request/response contract, invariants, and escalation trigger. |
| Domain preset report | `fixtures/evidence-sprint/web-api-pilot/domain-preset-report.json` / `.md` | present | Rendered from `web-api-bff` without live external APIs. |
| ExecPlan v2 | `fixtures/evidence-sprint/web-api-pilot/exec-plan.v2.json` | present | Validated by `schema/exec-plan.v2.schema.json`. |
| Evidence Sprint metrics | `fixtures/evidence-sprint/web-api-pilot/measurement-report.json` | present | Captures the eight #3569 metric slots for this pilot. |
| Req2run metrics | `fixtures/metrics/req2run/expected.req2run-metrics.json` | present | Existing report-only requirement-to-runnable fixture linked as compatible evidence. |
| PR assurance review surface | `fixtures/evidence-sprint/web-api-pilot/pr-assurance-review.md` | present | Preview for reviewers before PR review completes. |
| Verification evidence | `fixtures/evidence-sprint/web-api-pilot/verification-evidence.md` plus local commands / required checks | pending closeout | Local results are recorded before PR publication; final CI state belongs in completion audit. |
| Review completeness | `pr-review-completeness` output | pending closeout | Final unresolved-thread count is recorded after Copilot/Codex review. |
| Completion audit report | Issue #3572 completion comment after merge | pending closeout | Final required checks, advisory findings, stale runs, and local verification are separated. |

### 5. Metrics snapshot

The measurement fixture is
`fixtures/evidence-sprint/web-api-pilot/measurement-report.json`.

| Metric | Value | Interpretation | Limitation |
| --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | `8` synthetic fixture minutes | The pilot can represent timing data in the #3569 schema. | Synthetic timing proves instrumentation readiness only; do not infer speed. |
| `evidence_coverage` | `8/10 = 0.8` | Pre-closeout evidence is available for Issue, scope, API contract, preset, ExecPlan, measurement, req2run, and review preview. | Final review completeness and completion audit are only truthful after PR stabilization and merge. |
| `missing_evidence_count` | `2` | The missing items are expected closeout artifacts. | Lifecycle state, not a failure before merge. |
| `unresolved_claim_count` | `0` | Claims are scoped to traceability, preset application, and fixture-backed metric readiness. | Does not prove runtime API behavior or production quality. |
| `review_rework_count` | `not_collected` | Review rework is measured after Copilot/Codex and maintainer review threads are handled. | Final count belongs in the completion audit comment. |
| `deterministic_replay_pass` | `true` | The preset report and fixtures are designed for local replay without live external APIs. | Passing replay does not replace GitHub CI or human review. |
| `manual_intervention_count` | `2` | One operator decision selected a fixture-backed pilot; one post-merge completion-audit action remains required. | These interventions are governance controls, not necessarily defects. |
| `audit_discrepancy_count` | `1` | The report keeps pre-merge evidence separate from final closeout state. | Re-evaluate after the PR is merged and final CI/review state is known. |

### 6. API contract review surface

Reviewers can inspect API contract evidence in
`fixtures/evidence-sprint/web-api-pilot/api-contract.md` and the PR assurance
review preview.

Key contract checks:

- the selected route is read-only and fixture-backed;
- request and response fields are explicit enough to review contract evidence;
- no raw private review text, PII, secrets, credentials, or exact private
  timestamps are exposed;
- `reportOnly` remains `true` and cannot be used as approval or waiver evidence;
- future live implementation escalates when authentication, authorization,
  payment, PII, cross-service contract breakage, or `risk:high` is in scope.

### 7. Verification plan

Run the narrow fixture checks before PR publication, then rely on required
GitHub checks and review completeness for final merge judgment.

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

### 8. Observations and follow-ups

| Observation | Triggering evidence | Disposition |
| --- | --- | --- |
| No live API change target was specified for #3572. | Issue body says to use a real small change when available, otherwise fixture-backed. | Use deterministic contract fixture and avoid runtime behavior claims. |
| The Web API preset expects an API contract artifact before review. | `requiredInputs` includes `api-contract`. | Add `api-contract.md` and require reviewers to inspect contract invariants. |
| Escalation is domain-specific. | `web-api-bff` escalation rule. | Future live routes involving auth, payment, PII, cross-service breakage, or `risk:high` must add security/high-assurance lanes. |
| Final closeout cannot be known at report creation time. | review completeness and completion audit pending. | Keep final required-check and advisory-finding language in the post-merge Issue comment. |
| Live claim promotion requires a separate entry decision. | Fixture-backed pilot evidence cannot support live API behavior or external effectiveness claims. | Apply `docs/product/LIVE-PILOT-ENTRY-CRITERIA.md` before collecting live data or publishing a live claim. |

### 9. Claim boundary

Supported for this observation:

- The #3572 flow has a traceable Web API evidence chain from Issue intent to API
  contract fixture, domain preset report, ExecPlan v2, measurement fixture, PR
  assurance review preview, verification plan, review completeness boundary, and
  completion audit boundary.
- The repository can apply the Web API/BFF domain preset to a deterministic
  fixture-backed pilot without live external APIs.
- The pilot exposes the API contract evidence expected by the Web API preset.

Not supported by this observation:

- live production API behavior or runtime route correctness;
- faster review or faster implementation as a general claim;
- safer code, better quality, or external adoption as generalized claims;
- agent/vendor comparison;
- autonomous approval, merge readiness, waiver, or policy-gate enforcement from
  report-only metrics alone.

---

## 日本語

### 1. 目的

この report は #3572 の Web API pilot を deterministic fixture-backed pilot
として記録します。実 runtime endpoint は追加せず、Web API/BFF domain preset、
API contract evidence、ExecPlan v2、measurement report、PR assurance review、
completion audit 境界を接続します。将来 live Web API / external pilot claim を出す前に、`docs/product/LIVE-PILOT-ENTRY-CRITERIA.md` を満たす必要があります。

### 2. Scope

対象は `web-api-bff` preset report、API contract fixture、ExecPlan v2
fixture、Evidence Sprint measurement fixture、review surface、docs navigation
です。Runtime API 実装、policy-gate enforcement、外部 repository pilot、agent
vendor 比較、速度・安全性・品質・adoption の一般 claim は対象外です。

### 3. Evidence path

| Evidence | Artifact | Status |
| --- | --- | --- |
| Issue | #3572 | present |
| Pilot report | `docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md` | present |
| API contract | `fixtures/evidence-sprint/web-api-pilot/api-contract.md` | present |
| Domain preset report | `fixtures/evidence-sprint/web-api-pilot/domain-preset-report.json` / `.md` | present |
| ExecPlan v2 | `fixtures/evidence-sprint/web-api-pilot/exec-plan.v2.json` | present |
| Measurement report | `fixtures/evidence-sprint/web-api-pilot/measurement-report.json` | present |
| PR assurance review | `fixtures/evidence-sprint/web-api-pilot/pr-assurance-review.md` | present |
| Verification / review / completion audit | local commands, GitHub checks, #3572 completion comment | closeout pending |

### 4. 主な観測

- #3572 には具体的な live API change が指定されていないため、Issue の条件に従い fixture-backed pilot としました。
- `web-api-bff` preset の必須 input として API contract が必要なため、route shape、request/response、invariant、escalation rule を fixture として明示しました。
- timing metric は synthetic fixture timing であり、速度 claim ではありません。
- review completeness と completion audit は PR closeout 後に記録します。

### 5. Claim boundary

この pilot が支持するのは、scoped Web API evidence chain、domain preset 適用、API contract evidence の可視性、metric collection readiness です。Live API correctness、速度、安全性、品質、adoption、agent/vendor 優位性、autonomous approval は主張しません。
