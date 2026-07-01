---
docRole: ssot
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency && pnpm -s run docs:lint
---

# Live Pilot Entry Criteria for External Claims

> Language / 言語: English | 日本語

---

## English

### 1. Status and purpose

This document is the entry gate for turning fixture-backed or internal
Evidence Sprint pilot material into live external-pilot evidence. It defines
what must be recorded before ae-framework can collect live external repository
pilot data or make any public claim based on live repository behavior.

Current status as of 2026-07-01:

- Evidence Sprint Web API and event-driven pilots are fixture-backed and
  report-only.
- ACP-097 external pilot material is `dry-run only` with 0 live external PRs
  collected.
- The controlled-comparison protocol is ready as a design, but it has not been
  executed.

These criteria do not authorize data collection by themselves. A live pilot
still requires maintainer consent, a private evidence tracker, redaction
approval, and the repository-specific operating decisions below.

### 2. Scope and non-goals

| Area | Entry rule |
| --- | --- |
| Applies to | Live external repository pilots, live API/event behavior statements, external PR review-surface observations, and any public claim that goes beyond fixture-backed readiness. |
| Does not apply to | Purely local fixture demos, synthetic examples, or internal report-only dogfooding when no live external behavior claim is made. |
| Default enforcement | Report-only. These criteria do not add a new required check, branch-protection rule, or policy-gate block. |
| Decision authority | Human maintainers, repository branch protection, and explicitly approved policy remain the approval and merge authority. |
| Publication authority | The pilot maintainer or named publication owner approves what can leave the pilot team. |
| Benchmark status | Not a benchmark. Review-speed, quality, safety, adoption, or vendor-comparison claims require the controlled-comparison protocol plus comparable baseline data. |

### 3. Entry decision states

| State | Meaning | Allowed public statement |
| --- | --- | --- |
| `not_started` | Only fixture-backed, dry-run, or internal evidence exists. Consent, live scope, retention, and publication decisions are incomplete. | The repository has a pilot-ready path or fixture-backed evidence route. Do not claim live external outcomes. |
| `ready_for_collection` | Maintainer consent, data handling, artifact retention, metrics plan, repository scope, and stop rules are recorded. Live collection may begin. | The pilot is approved for report-only live collection. Do not claim outcome or effectiveness. |
| `claim_ready` | Required live artifacts are collected, redacted, reviewed, and tied to the pre-registered claim statement. Baselines are present when the claim needs comparison. | Only the measured, maintainer-approved, redacted claim may be published. Unsupported claims remain excluded. |

A pilot can move backward if consent changes, redaction fails, CI becomes
uninterpretable, or the review surface is mistaken for approval.

### 4. Minimum entry criteria before live collection

Record these items before the first live external PR is collected.

| Criterion | Minimum evidence |
| --- | --- |
| Repository consent | Named pilot maintainer, target repository, approved operator, and written confirmation that report-only collection is allowed. |
| Repository scope | Included PR categories, excluded PR categories, target branch-policy assumptions, and actual required-check names. |
| Data handling | Raw-output viewers, private storage location, allowed live identifiers, redaction owner, and treatment of PR URLs, reviewer identities, comments, file paths, timestamps, secrets, credentials, PII, customer data, incidents, and business context. |
| Artifact retention | Retention period, deletion or archival owner, access control, and whether raw artifacts can be referenced by private URL or must be copied into a private tracker. |
| Publication boundary | Publication owner, allowed publication forms (`aggregate only`, `redacted case note`, `synthetic fixture`, or `private only`), and final approval step before external use. |
| Claim statement | Pre-registered claim text, observation window, denominator, expected evidence, unsupported claims list, and the state required to call the claim `claim_ready`. |
| Metrics plan | Required Evidence Sprint and agent PR assurance fields, source artifacts, `not_collected` handling, and denominator definitions. |
| Baseline / comparison plan | Required when claiming faster review, improved decision quality, better safety/quality, adoption impact, or any comparative result. Use `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md`. |
| Review and audit plan | Review-surface preview, maintainer feedback capture, review-completeness method, final unresolved-thread snapshot, and completion-audit report. |
| Stop rules | Conditions for pausing or aborting collection, including sensitive-data exposure, unresolved consent, branch-policy drift, CI instability, reviewer confusion, or approval-signal confusion. |

### 5. Required evidence artifacts

A live pilot claim needs an evidence index that separates private raw evidence
from public or publication-approved evidence. Required artifacts are:

| Artifact | Required when | Notes |
| --- | --- | --- |
| Consent record | Before collection | Private issue, maintainer note, signed agreement, or equivalent written approval. |
| Pilot scope memo | Before collection | Repository, PR category, observation window, target required checks, roles, and stop rules. |
| Data-handling and retention note | Before collection | Redaction fields, private storage, retention period, access list, and deletion/archive owner. |
| Private per-PR tracker | During collection | Derived from `docs/product/PILOT-EVIDENCE-TEMPLATE.md`; do not edit public templates with live data. |
| Context Pack or scope memo | Per PR when applicable | Use Context Pack when the pilot task depends on repository design boundaries; otherwise record scope explicitly. |
| ExecPlan v2 or equivalent plan | Per PR or observation | Must list evidence expectations, verification commands, allowed actions, and stop rules. |
| Domain preset report | When using Web API, event-driven, Spec Kit, or high-assurance starter packages | Keeps preset fit, required inputs, expected artifacts, and escalation rule visible. |
| Verification output | Per PR or observation | Examples: `verify:lite`, API contract evidence, trace/conformance output, req2run metrics, or repository-specific CI evidence. |
| Agent PR assurance metrics | Per PR when collecting PR review evidence | Must preserve `not_collected` instead of converting missing live data to zero. |
| PR assurance review surface | Per PR when shown to reviewers | Preview before posting; posting requires explicit maintainer approval. |
| Review completeness snapshot | Before final pilot closeout | Capture total review threads and final unresolved-thread count when available. |
| Completion audit report | Before any external claim | Separates local verification, required checks, advisory findings, skipped runs, stale runs, and review disposition. |
| Redaction and publication approval log | Before publication | Records what was removed, what is aggregate-only, what remains private, and who approved publication. |
| Baseline/control evidence | Before comparative claims | Required for review-speed, decision-quality, safety, quality, adoption, or vendor/workflow comparison claims. |

### 6. Required measurement fields

At minimum, a live pilot entry plan lists these fields and their source. Use
`not_collected` or `unknown` rather than zero when data is missing or not
approved.

| Field | Required source or disposition |
| --- | --- |
| `observation_id` | Stable id for the pilot observation or per-PR row. |
| `repository_scope` | Redacted repository id, PR category, branch-policy assumptions, and excluded categories. |
| `consent_status` | `approved`, `pending`, `revoked`, or `not_collected`; collection starts only when approved. |
| `redaction_status` | `planned`, `reviewed`, `approved`, `needs_changes`, or `not_approved`. |
| `retention_status` | Storage location, retention period, access list, and deletion/archive owner recorded or `not_collected`. |
| `publication_status` | `approved`, `aggregate only`, `private`, or `not approved for publication`. |
| `claim_disposition` | `not_started`, `ready_for_collection`, `claim_ready`, `unsupported`, or `deferred`. |
| `sample_size` | Planned and collected PR count, plus denominator by category when applicable. |
| `baseline_available` | `yes`, `no`, or `not_required`; comparative claims require `yes`. |
| `time_to_first_runnable_verification_minutes` | From accepted requirement or review-ready timestamp to first passing runnable verification; separate synthetic timing from live timing. |
| `evidence_coverage` | Required evidence items present divided by all required evidence items; record denominator. |
| `missing_evidence_count` | Missing, stale, or `not_collected` required evidence items; record claim set and denominator. |
| `unresolved_claim_count` | Claims without evidence, waiver, deferral, or non-applicability at final snapshot. |
| `review_rework_count` | Actionable review-feedback clusters that caused code, fixture, doc, or evidence changes. |
| `manual_intervention_count` | Approval, redaction, environment, missing-evidence, review-disposition, and publication-boundary interventions. |
| `audit_discrepancy_count` | Completion-audit discrepancies between wording and actual required/advisory/stale/local evidence. |
| `deterministic_replay_pass` | Whether documented local fixture/render/validation commands replay without drift. |
| `completion_audit_status` | Final status of required checks, advisory findings, review completeness, and publication boundary. |

### 7. Claim boundary matrix

| Claim type | Minimum state | Required additional evidence | Unsupported until |
| --- | --- | --- | --- |
| Fixture-backed readiness | `not_started` is enough when clearly labelled fixture-backed/report-only. | Checked-in fixture, replay command, schema/doc validation, and unsupported-claim note. | N/A, as long as no live outcome is implied. |
| Live API or event behavior | `claim_ready`. | Live target scope, environment boundary, selected data source, verification output, incident/production-impact boundary, and redaction approval. | Live route/event processing evidence exists and maintainer approves publication. |
| Review-speed or productivity | `claim_ready` plus baseline. | Controlled comparison, comparable PR categories, review-ready/disposition timing, queueing notes, sample denominator, and missing-value handling. | `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md` is executed with comparable baseline data. |
| Safety or code-quality outcome | `claim_ready` plus baseline. | Defect/finding taxonomy, severity, denominator, independent review or delayed finding window, and baseline/control evidence. | Outcome endpoint and baseline/control data are defined and collected. |
| Adoption impact | `claim_ready` plus observation window. | Adoption metric, repository/team denominator, consent, redaction, confounder notes, and baseline or pre/post protocol. | Maintainer-approved live data covers the adoption metric and window. |
| Agent/vendor superiority | Not supported by these criteria. | A separate approved study comparing workflows without ranking vendors is required before any public comparative wording. | The project has an explicit controlled protocol and maintainer-approved analysis plan. |
| Enforcement or merge-readiness guarantee | Not supported by these criteria. | Policy changes require separate design, branch-protection approval, and CI governance. | A separate enforcement PR changes policy and branch protection intentionally. |

### 8. Fixture-backed pilot status

Until these criteria reach `claim_ready` through a new, reviewed PR:

- `docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md` remains a
  deterministic fixture-backed Web API pilot report.
- `docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md` remains a
  deterministic fixture-backed event-driven/conformance pilot report.
- `docs/product/PILOT-REPORT-2026Q3-01.md` remains an ACP-097 `dry-run only`
  report with 0 live external PRs collected.
- Release notes, articles, and social posts must continue to avoid review-speed,
  safety, quality, adoption-impact, live API/event behavior, and agent/vendor
  benchmark claims unless a later live-pilot claim explicitly satisfies this
  document.

### 9. Related operating documents

- Measurement vocabulary:
  `docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md`
- External pilot consent/runbook path:
  `docs/guides/external-pilot-onboarding.md`,
  `docs/product/PILOT-RUNBOOK-2026Q3.md`, and
  `docs/product/PILOT-EVIDENCE-TEMPLATE.md`
- Current dry-run report:
  `docs/product/PILOT-REPORT-2026Q3-01.md`
- Fixture-backed Evidence Sprint pilots:
  `docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md` and
  `docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md`
- Future baseline/comparison design:
  `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md`
- Release wording boundary:
  `docs/product/EVIDENCE-SPRINT-RELEASE-ASSETS-2026-07-01.md`

---

## 日本語

### 1. Status / 目的

この文書は、fixture-backed または internal な Evidence Sprint pilot を、live external
pilot evidence や公開 claim に昇格する前の entry criteria です。Live repository
behavior を根拠に公開 claim を出す前に、consent、data handling、artifact retention、
metrics、baseline、publication boundary を固定します。

2026-07-01 時点では、Web API / event-driven pilots は fixture-backed/report-only、
ACP-097 external pilot report は `dry-run only` かつ live external PR 収集数0件、
controlled comparison protocol は未実施です。

この文書だけでは data collection は承認されません。Live pilot には、maintainer
consent、private evidence tracker、redaction approval、repository 固有の operating
decision が必要です。

### 2. Entry states

| State | 意味 | 公開可能な表現 |
| --- | --- | --- |
| `not_started` | fixture-backed、dry-run、internal evidence のみ。consent、scope、retention、publication が未固定。 | pilot-ready path / fixture-backed evidence route がある、とだけ言える。live outcome は言えない。 |
| `ready_for_collection` | maintainer consent、data handling、artifact retention、metrics plan、scope、stop rule を記録済み。 | report-only live collection が承認された、とだけ言える。outcome claim は不可。 |
| `claim_ready` | 必須 live artifact が収集・redact・review され、pre-registered claim に接続済み。比較claimには baseline も必要。 | 測定済みで maintainer 承認済みの範囲に限って公開できる。 |

### 3. Live collection 前の最小条件

- Pilot maintainer、target repository、operator、report-only collection consent を記録する。
- 対象 PR category、除外 category、branch-policy assumption、actual required-check name を記録する。
- Raw output viewer、private storage、redaction owner、PR URL、reviewer identity、comment、file path、timestamp、secret、PII、customer/incident/business context の扱いを固定する。
- Retention period、access control、deletion/archive owner を決める。
- Publication owner、publication form（`aggregate only`、`redacted case note`、`synthetic fixture`、`private only`）、外部公開前の approval step を決める。
- Pre-registered claim、observation window、denominator、required evidence、unsupported claim list を記録する。
- Comparative claim を出す場合は `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md` に従い、baseline/control evidence を先に設計する。
- Review surface preview、review completeness、completion audit、stop rule を計画に含める。

### 4. 必須 evidence artifact

Live pilot claim には、private raw evidence と publication-approved evidence を分けた evidence index が必要です。

| Artifact | 必要なタイミング |
| --- | --- |
| Consent record | collection 前 |
| Pilot scope memo | collection 前 |
| Data-handling / retention note | collection 前 |
| Private per-PR tracker | collection 中。公開 template に live data を直接書かない。 |
| Context Pack または scope memo | PR ごと。design boundary が関係する場合は Context Pack を使う。 |
| ExecPlan v2 または同等 plan | PR または observation ごと |
| Domain preset report | Web API、event-driven、Spec Kit、high-assurance starter package を使う場合 |
| Verification output | PR または observation ごと |
| Agent PR assurance metrics | PR review evidence を収集する場合 |
| PR assurance review surface | reviewer に見せる場合。投稿は maintainer approval 後。 |
| Review completeness snapshot | final closeout 前 |
| Completion audit report | external claim 前 |
| Redaction / publication approval log | publication 前 |
| Baseline/control evidence | speed、decision quality、安全性、品質、adoption、比較claim 前 |

### 5. 必須 measurement fields

最低限、次の field と source を entry plan に含めます。未収集または未承認の値は 0 にせず
`not_collected` / `unknown` として残します。

- `observation_id`
- `repository_scope`
- `consent_status`
- `redaction_status`
- `retention_status`
- `publication_status`
- `claim_disposition`
- `sample_size`
- `baseline_available`
- `time_to_first_runnable_verification_minutes`
- `evidence_coverage`
- `missing_evidence_count`
- `unresolved_claim_count`
- `review_rework_count`
- `manual_intervention_count`
- `audit_discrepancy_count`
- `deterministic_replay_pass`
- `completion_audit_status`

### 6. Claim boundary

- Fixture-backed readiness は、fixture-backed/report-only と明示する限り現在の evidence で扱える。
- Live API / event behavior claim は、live target、environment boundary、verification output、production-impact boundary、redaction approval が揃うまで不可。
- Review-speed / productivity claim は、controlled comparison と comparable baseline data が揃うまで不可。
- Safety / quality outcome claim は、defect taxonomy、severity、denominator、independent review または delayed finding window、baseline/control が揃うまで不可。
- Adoption impact claim は、adoption metric、observation window、consent、redaction、confounder note、baseline または pre/post protocol が揃うまで不可。
- Agent/vendor superiority、enforcement guarantee、merge-readiness guarantee は、この criteria では支持しない。

### 7. Fixture-backed pilot の扱い

新しい reviewed PR でこの criteria を満たし `claim_ready` に到達するまで、次の文書は
report-only のままです。

- `docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md`
- `docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md`
- `docs/product/PILOT-REPORT-2026Q3-01.md`

Release note、article、SNS post は、後続の live-pilot claim がこの文書を満たすまで、
review-speed、安全性、品質、adoption impact、live API/event behavior、agent/vendor
benchmark claim を避けます。
