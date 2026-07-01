---
docRole: ssot
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: node scripts/ci/validate-json.mjs && pnpm -s run check:doc-consistency
---
# Dogfooding and Pilot Measurement Protocol

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This protocol fixes the Evidence Sprint measurement vocabulary before the
self-dogfood and domain pilots run. It measures the ae-framework **workflow**:
Issue intent, Context Pack or scope memo, ExecPlan v2, domain preset selection,
runnable verification, req2run metrics, PR assurance review, review-thread
closure, and completion audit.

It does **not** measure raw coding-agent intelligence, rank Codex / Copilot /
Claude Code / other producers, or turn report-only metric values into approval.
Human maintainers, repository branch protection, and explicit policy remain the
decision authority.

Use this protocol for:

- #3570 self-dogfood;
- #3572 Web API pilot;
- #3573 event-driven / conformance pilot;
- #3571 public case-study and evidence pack when selecting which statements are
  supported by observed repository evidence.

Before any fixture-backed or dry-run observation is converted into a live
external claim, apply `docs/product/LIVE-PILOT-ENTRY-CRITERIA.md` so consent,
data handling, retention, baselines, and publication boundaries are recorded.

### 2. Observation boundary

| Boundary | Rule |
| --- | --- |
| Unit of observation | One Issue-to-PR or pilot flow, not an agent run. |
| Claim boundary | A single run can support instrumentation-readiness and traceability statements, not generalized speed, safety, quality, or adoption claims. |
| Producer boundary | Agents, CI, formal tools, and humans are evidence producers; producer identity is a covariate, not the metric target. |
| Evidence source | Prefer local artifacts and summary reports over raw logs. Record raw-log links only when publication and redaction boundaries allow it. |
| Enforcement default | Report-only. The protocol adds no `policy-gate` block condition. |
| Privacy boundary | Raw PR text, reviewer names, exact live timestamps, and private comments remain private unless publication is explicitly approved. |
| External API boundary | Offline fixtures must be collectable without live GitHub or external agent APIs. Live pilots may reference captured GitHub state, but the report must state that boundary. |

### 3. Canonical metrics

Every metric row has purpose, source artifact, calculation method,
interpretation, and limitation. Use `not_collected` instead of `0` when data was
not collected.

| Metric | Purpose | Source artifact / source | Calculation method | Interpretation | Limitation |
| --- | --- | --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | Measure setup and execution friction from accepted requirement or Issue intent to first runnable verification. | Issue timestamp or redacted timing note, ExecPlan v2, `verify-lite-run-summary`, loop summary, req2run report. | Minutes from accepted requirement timestamp to the first passing runnable verification artifact. | Lower values may indicate smoother onboarding when task size, queueing, and branch policy are comparable. | Synthetic timestamps only prove instrumentation readiness; live timing is sensitive to queueing, CI availability, and reviewer/operator availability. |
| `evidence_coverage` | Show how much required evidence is present before merge-readiness or publication wording. | ExecPlan v2 evidence requirements, claim-evidence manifest, assurance summary, completion audit, pilot checklist. | Required evidence items marked present divided by all required evidence items. | Higher coverage means more work can be reviewed through artifacts instead of prose alone. | Coverage does not prove evidence sufficiency, freshness, or correctness. |
| `missing_evidence_count` | Keep unsupported claims or absent required artifacts visible. | Producer-normalization summary, claim-evidence manifest, assurance summary, completion audit notes. | Count required evidence items or PR-relevant claims whose supporting artifact is absent, stale, or `not_collected`. | Non-zero values identify follow-up or publication limitations; they are not automatically blocking. | Counts depend on the declared claim set and denominator, so record both. |
| `unresolved_claim_count` | Check whether PR-relevant claims have a final disposition. | Claim-evidence manifest, claim-level summary, policy decision, assurance summary. | Count claims without evidence, waiver, deferral, or non-applicability disposition at the final snapshot. | Lower counts support traceable closeout for the scoped claim set. | Zero unresolved claims does not prove code correctness or absence of untracked claims. |
| `review_rework_count` | Capture review feedback that required follow-up changes. | PR review bodies, inline threads, `pr-review-completeness`, task ledger, follow-up commits. | Count actionable feedback clusters that resulted in code, fixture, or doc changes after the first PR draft. | Higher counts can mean useful risk discovery or unclear first-pass evidence; classify the cause. | Review style varies by tool and reviewer; do not use this as an agent/vendor score. |
| `deterministic_replay_pass` | Record whether local fixture inputs reproduce the report-only evidence. | Fixture JSON, renderer output, schema validation, verify-lite or domain preset reports. | `true` only when the documented local fixture/render/validation commands pass without drift. | Passing replay supports reproducibility of the evidence pack. | Fixture replay is not a live external-agent or external-repository pilot. |
| `manual_intervention_count` | Track human actions needed for approval, redaction, environment repair, missing evidence, or publication boundary decisions. | Operator note, task ledger, Issue comments, private pilot tracker, loop summary. | Count interventions using the fixed taxonomy: approval, redaction, environment, missing evidence, review disposition, publication boundary. | Non-zero values identify friction or required governance controls. | Some interventions are intentional controls, not defects. |
| `audit_discrepancy_count` | Track differences between completion wording and actual required/advisory/stale workflow evidence. | Completion audit report, final check rollup, review completeness output, local verification notes. | Count completion-audit notes where required checks, advisory findings, skipped runs, stale runs, or local verification were previously conflated. | Non-zero values show where closeout wording or follow-up tracking needs improvement. | Depends on how thoroughly advisory surfaces were inspected. |

### 4. Source artifact checklist

| Evidence surface | Required for #3570 | Required for #3572/#3573 | Notes |
| --- | --- | --- | --- |
| Issue / scope memo | yes | yes | Redact or alias private pilot identifiers. |
| Context Pack or scope memo | yes | yes | If Context Pack is not used, record the alternative scope boundary. |
| ExecPlan v2 or equivalent task plan | yes | yes | Must list evidence expectations and verification commands. |
| Domain preset report | optional | yes | Use Web API preset for #3572 and event-driven preset for #3573. |
| Verification output | yes | yes | Prefer `verify-lite`, conformance, API contract, or deterministic fixture outputs. |
| Req2run metrics | yes | recommended | Use `docs/product/REQ2RUN-METRICS.md` where applicable. |
| PR assurance review surface | yes | recommended | Link Markdown or redacted/private artifact. |
| Review completeness | yes | yes when PR review occurs | Record unresolved threads at final snapshot. |
| Completion audit report | yes | yes | Required for final closeout wording. |

### 5. Collection workflow

1. Register the observation id, issue ref, observation type, execution status,
   and publication status.
2. List source artifacts before calculating metrics. Missing optional artifacts
   stay visible instead of being silently converted to zero.
3. Calculate all eight canonical metrics. Use `not_collected` where the source
   data is absent.
4. Record allowed and forbidden claims for the observation.
5. Attach the pilot report template or completed report to the Issue/PR.
6. At PR closeout, link review completeness, required checks, full check rollup,
   and completion audit evidence.

### 6. Claim rules

Allowed after one self-dogfood or pilot run:

- "The workflow produced a traceable evidence chain for this scoped run."
- "The repository can collect the Evidence Sprint metrics from local artifacts
  or explicitly captured PR state."
- "The run exposed concrete missing evidence, review rework, manual
  intervention, or audit discrepancy follow-ups."

Not supported by one run:

- faster review or faster implementation as a general claim;
- safer code or better quality as a general claim;
- external adoption proof;
- agent/vendor ranking;
- autonomous approval or guaranteed merge readiness.

### 7. Offline fixture

The schema-backed fixture at
`fixtures/metrics/evidence-sprint/pilot-measurement-example.json` demonstrates
collection without live external APIs. It intentionally includes one missing
publication-boundary evidence item and one audit discrepancy so downstream
reports show limitations rather than unsupported public claims.

Schema: `schema/evidence-sprint-measurement-report.schema.json`
(`evidence-sprint-measurement-report/v1`).

### 8. Relationship to existing metrics

- `docs/product/EFFECTIVENESS-METRICS.md` remains the broader product metric
  vocabulary.
- `docs/product/REQ2RUN-METRICS.md` remains the requirement-to-runnable subset.
- This protocol binds those metrics to the post-REVAL-3 Evidence Sprint and adds
  review rework plus completion-audit discrepancy tracking for #3570-#3573.
- `docs/templates/evidence-sprint-pilot-report.md` is the copyable report
  template for the self-dogfood and domain pilots.
- `docs/product/LIVE-PILOT-ENTRY-CRITERIA.md` defines the consent, data
  handling, retention, measurement-field, artifact, and claim-boundary
  prerequisites before any live external claim is made.

---

## 日本語

### 1. 目的

この protocol は、Evidence Sprint の self-dogfood / pilot を実施する前に測定語彙を固定します。測定対象は ae-framework の **workflow effectiveness** です。Issue intent、Context Pack または scope memo、ExecPlan v2、domain preset、runnable verification、req2run metrics、PR assurance review、review-thread closure、completion audit を観測します。

raw coding-agent intelligence、agent vendor の優劣、または report-only metric による承認・マージ可否は測りません。承認権限は human maintainer、branch protection、明示された policy に残ります。Fixture-backed / dry-run observation を live external claim に変える前に、`docs/product/LIVE-PILOT-ENTRY-CRITERIA.md` で consent、data handling、retention、baseline、publication boundary を固定します。

### 2. 測定境界

| Boundary | Rule |
| --- | --- |
| 観測単位 | agent run ではなく Issue-to-PR / pilot flow。 |
| Claim boundary | 1回のrunで言えるのは instrumentation readiness と traceability。速度・安全性・品質・adoption の一般化はしない。 |
| Producer boundary | agent、CI、formal tool、人間は evidence producer。producer identity は metric target ではない。 |
| Evidence source | raw log より local artifact / summary report を優先する。 |
| Enforcement default | report-only。新しい `policy-gate` block 条件は作らない。 |
| Privacy boundary | raw PR text、reviewer name、exact live timestamp、private comment は公開承認なしに出さない。 |

### 3. Canonical metrics

| Metric | 目的 | 主なsource | 計算 | 解釈 | 制限 |
| --- | --- | --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | 要求から最初のrunnable verificationまでの摩擦を見る。 | Issue timing、ExecPlan v2、verify-lite、loop summary、req2run report。 | accepted requirement から first passing runnable verification までの分。 | 条件が揃えば onboarding friction の低さを示す。 | synthetic timing は計測準備の証跡であり速度claimではない。 |
| `evidence_coverage` | 必須証跡がどれだけ揃っているかを見る。 | ExecPlan v2、claim-evidence、assurance summary、completion audit。 | present required evidence / all required evidence。 | artifactでreviewできる範囲を示す。 | 十分性・鮮度・正しさは別途確認が必要。 |
| `missing_evidence_count` | unsupported claim / 欠落artifactを見える化する。 | producer-normalization、claim-evidence、completion audit。 | absent/stale/not_collected の必須証跡件数。 | follow-up / publication limitation を示す。 | claim set と分母を固定しないと比較できない。 |
| `unresolved_claim_count` | PR関連claimに最終dispositionがあるかを見る。 | claim-evidence、claim-level、policy decision。 | evidence / waiver / deferral / non-applicability がないclaim数。 | scoped claim set のcloseout追跡性を示す。 | code correctness の証明ではない。 |
| `review_rework_count` | review feedback による手戻りを数える。 | review thread、`pr-review-completeness`、follow-up commit。 | code/fixture/doc変更を生んだactionable feedback cluster数。 | risk discovery または初回証跡不足を示す。 | reviewer style に依存し、vendor scoreには使えない。 |
| `deterministic_replay_pass` | local fixture が再現できるかを見る。 | fixture、renderer、schema validation、verify-lite。 | documented command がdrift/schema failureなしでpassすればtrue。 | evidence pack の再現性を示す。 | live external-agent pilotではない。 |
| `manual_intervention_count` | 人間介入の量と理由を記録する。 | operator note、task ledger、Issue、pilot tracker。 | approval/redaction/environment/missing-evidence/review/publication boundary の介入数。 | product friction または必要なgovernanceを示す。 | 意図されたcontrolはdefectではない。 |
| `audit_discrepancy_count` | completion wording と実際のworkflow evidenceのずれを数える。 | completion audit、final check rollup、review completeness。 | required/advisory/skipped/stale/local verification を混同したaudit note数。 | closeout表現やfollow-upの改善点を示す。 | advisory surface の確認範囲に依存する。 |

### 4. Claim rules

1回の self-dogfood / pilot run で言えるのは、scoped run の evidence chain、metric collection readiness、具体的なfollow-upです。一般的な速度改善、安全性、品質改善、外部adoption、agent vendor順位、autonomous approval は主張しません。

### 5. Fixture / template

- Schema fixture: `fixtures/metrics/evidence-sprint/pilot-measurement-example.json`
- Schema: `schema/evidence-sprint-measurement-report.schema.json`
- Report template: `docs/templates/evidence-sprint-pilot-report.md`

このfixtureは live external API を呼ばず、public claim approval を意図的に missing として残します。これにより、case study / release note でunsupported claimを避ける判断を練習できます。
