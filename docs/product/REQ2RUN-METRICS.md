---
docRole: ssot
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: pnpm -s run metrics:req2run -- --fixture fixtures/metrics/req2run/offline-input.json --generated-at 2026-07-01T00:00:00.000Z --output-json artifacts/metrics/req2run-metrics.json --output-md artifacts/metrics/req2run-metrics.md
---

# Req2run Metrics for Adoption Evidence

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

Req2run metrics measure whether a requirement can become a runnable,
reviewable, evidence-backed change through the ae-framework reference flow. They
extend the product-effectiveness vocabulary in
`docs/product/EFFECTIVENESS-METRICS.md` with adoption-readiness signals for the
path documented in `docs/getting-started/REFERENCE-FLOW.md`.

These metrics evaluate the **ae-framework workflow**: Issue/spec input,
Context Pack and boundary-map preflight, ExecPlan v2, verification artifacts,
assurance summaries, and PR review surfaces. They do **not** benchmark raw
coding-agent intelligence and do **not** rank Codex, Claude Code, GitHub Copilot,
or any other producer.

### 2. Measurement boundary

| Boundary | Rule |
| --- | --- |
| Unit of observation | A requirement-to-runnable-evidence flow, not an agent run. |
| Product claim | Measure whether the workflow can turn a requirement into local runnable evidence with traceable review surfaces. |
| Producer boundary | Agents, CI, formal tools, and humans are evidence producers; human maintainers retain approval authority. |
| Enforcement default | Report-only. No req2run metric creates a `policy-gate` block condition by itself. |
| Privacy boundary | Raw PR text, reviewer identity, exact live timing, private comments, and repository-sensitive paths require approval before publication. |
| Comparison boundary | Compare workflow arms only under `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md`; do not compare agent vendors without a separate controlled protocol. |

### 3. Canonical req2run metrics

| Metric | Reviewer / adopter question | Source artifact | Calculation method | Interpretation | Limitation |
| --- | --- | --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | How long did it take for a requirement to produce the first runnable verification artifact? | Requirement/Issue timestamp, ExecPlan v2, `verify-lite-run-summary`, loop summary, or manual timing note. | Minutes from `requirementAcceptedAt` to the first passing runnable verification timestamp. | Lower values can indicate less setup friction for the reference flow. | Sensitive to queueing, task size, CI availability, and whether timestamps are synthetic, redacted, or live. |
| `spec_task_evidence_coverage` | How many spec or plan tasks have at least one linked evidence artifact? | ExecPlan v2 task graph, Spec Kit task import, claim-evidence manifest, assurance summary. | Required tasks with one or more `evidenceRefs` divided by all required tasks. | Higher coverage means more planned work is reviewable through evidence rather than prose alone. | Evidence existence does not prove evidence sufficiency, freshness, or correctness. |
| `deterministic_replay_pass_rate` | Can the same local inputs be replayed deterministically? | Loop-run summary replay section, fixture hashes, validation command outputs, variance report when available. | Passing deterministic replay attempts divided by all replay attempts. | Higher pass rate supports local reproducibility and onboarding readiness. | Fixture replay is not a live external-agent benchmark and does not measure raw coding quality. |
| `manual_intervention_count` | How many human interventions were required before runnable evidence existed? | Operator notes, loop summary stop/next-action fields, Issue comments, private pilot tracker. | Count intervention records within the flow, grouped by taxonomy such as approval, redaction, missing evidence, or environment setup. | Lower counts can indicate smoother onboarding; non-zero counts identify where docs or automation should improve. | The taxonomy must be stable before comparing teams, repositories, or observation windows. |
| `evidence_review_completeness` | How complete is the review-ready evidence set for the requirement-to-run path? | Required evidence checklist, claim-evidence manifest, assurance summary, PR review surface, policy summary. | Required evidence items marked present and reviewed divided by all required evidence items. | Higher completeness means fewer missing local artifacts for reviewers to inspect. | Completeness does not replace human approval and should not be promoted to blocking without policy work. |

### 4. Offline fixture and command

The local collector demonstrates collection without live GitHub calls or live
external agent APIs:

```bash no-doctest
pnpm -s run metrics:req2run -- \
  --fixture fixtures/metrics/req2run/offline-input.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/metrics/req2run-metrics.json \
  --output-md artifacts/metrics/req2run-metrics.md
```

Fixture and expected report surfaces:

| Surface | Path | Purpose |
| --- | --- | --- |
| Offline input | `fixtures/metrics/req2run/offline-input.json` | Synthetic requirement-to-runnable flow with source artifact references, tasks, evidence items, replay attempts, and manual interventions. |
| JSON report | `fixtures/metrics/req2run/expected.req2run-metrics.json` | Schema-valid `req2run-metrics/v1` report-only artifact. |
| Markdown report | `fixtures/metrics/req2run/expected.req2run-metrics.md` | Human-readable review surface for the sample. |
| Schema | `schema/req2run-metrics.schema.json` | Preview contract for local adoption-readiness evidence. |
| Collector | `scripts/metrics/collect-req2run-metrics.mjs` | Offline-only producer for the JSON and Markdown reports. |

The default output path is `artifacts/metrics/req2run-metrics.{json,md}`. The
fixture intentionally leaves public-claim approval evidence uncollected so the
sample demonstrates limitations instead of implying adoption proof.

### 5. Dogfooding and pilot report template

When adding req2run evidence to dogfooding or pilot reports, use this template:

| Field | Required value or rule |
| --- | --- |
| Observation id | Requirement, Issue, or task id. Use a redacted id for public reports. |
| Reference-flow profile | Baseline, structured assurance, Spec Kit import, Spec & Verification Kit, high-assurance selected claim, or report-only loop branch. |
| Source artifacts | List paths to ExecPlan v2, verification summary, assurance summary, loop summary, and PR review surface where available. |
| Metrics | Record the five canonical req2run metrics; use `not_collected` rather than zero for missing values. |
| Privacy status | `synthetic`, `approved`, `aggregate only`, `private`, or `not approved for publication`. |
| Interpretation | State whether the observation supports instrumentation readiness, onboarding friction analysis, or a controlled-comparison claim. |
| Limitation | State sample size, synthetic/live status, redaction, missing artifacts, and human intervention assumptions. |

### 6. Controlled comparison requirements

Req2run metrics can be included in a controlled comparison only when the protocol
controls are satisfied:

- define whether the comparison unit is a requirement-to-runnable flow or a PR
  review task;
- keep producer identity as a covariate, not the outcome;
- use the same requirement/task category and branch-policy assumptions for both
  arms;
- record exact denominators for tasks, evidence items, replay attempts, and
  interventions;
- keep synthetic fixture results separate from live pilot results;
- publish only approved aggregate or redacted values.

Allowed pre-comparison claim: "the repository has a local, report-only fixture
that demonstrates req2run metric collection." Forbidden without controlled data:
"ae-framework makes requirements runnable faster", "agent vendor X is better",
or "external adoption is proven".

---

## 日本語

### 1. 目的

Req2run metrics は、要求が ae-framework の reference flow を通じて runnable、reviewable、
evidence-backed な変更に到達できるかを測る adoption-readiness signal です。
`docs/product/EFFECTIVENESS-METRICS.md` の product-effectiveness vocabulary を拡張し、
`docs/getting-started/REFERENCE-FLOW.md` の Issue/spec input から PR assurance review までの経路を対象にします。

これらの metric は **ae-framework workflow** を評価します。Raw coding-agent intelligence や
Codex / Claude Code / GitHub Copilot 等の agent vendor 優劣は評価しません。

### 2. 測定境界

| Boundary | Rule |
| --- | --- |
| 観測単位 | agent run ではなく requirement-to-runnable-evidence flow。 |
| Product claim | 要求を local runnable evidence と traceable review surface に変換できるかを測る。 |
| Producer boundary | agent、CI、formal tool、人間は evidence producer。承認権限は human maintainer に残る。 |
| Enforcement default | report-only。metric 定義だけで `policy-gate` block 条件を作らない。 |
| Privacy boundary | raw PR text、reviewer identity、live timing、private comment、sensitive path は公開承認なしに出さない。 |
| Comparison boundary | 比較は `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md` に従う。agent vendor 比較は別 protocol がない限り行わない。 |

### 3. Canonical req2run metrics

| Metric | Reviewer / adopter question | Source artifact | Calculation method | Interpretation | Limitation |
| --- | --- | --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | 要求から最初の runnable verification artifact まで何分かかったか。 | Requirement/Issue timestamp、ExecPlan v2、`verify-lite-run-summary`、loop summary、manual timing note。 | `requirementAcceptedAt` から最初の passing runnable verification timestamp までの分数。 | 小さい値は reference flow の setup friction が低い可能性を示す。 | queue、task size、CI availability、timestamp が synthetic/redacted/live かに影響される。 |
| `spec_task_evidence_coverage` | spec / plan task のうち evidence artifact に接続されたものは何件か。 | ExecPlan v2 task graph、Spec Kit task import、claim-evidence manifest、assurance summary。 | evidenceRefs を持つ required task / 全 required task。 | planned work が prose だけでなく evidence で review 可能かを示す。 | evidence の存在は十分性・鮮度・正しさを証明しない。 |
| `deterministic_replay_pass_rate` | 同じ local input を deterministic に replay できるか。 | loop-run summary replay、fixture hash、validation output、variance report。 | passing replay attempt / 全 replay attempt。 | local reproducibility と onboarding readiness の signal。 | fixture replay は live external-agent benchmark ではない。 |
| `manual_intervention_count` | runnable evidence 到達までに人間の介入が何回必要だったか。 | operator note、loop summary、Issue comment、private pilot tracker。 | approval、redaction、missing evidence、environment setup 等の介入記録を数える。 | 小さい値は onboarding friction の低さを示し得る。非ゼロは改善対象を示す。 | taxonomy が安定するまで team / repo 間比較に使わない。 |
| `evidence_review_completeness` | requirement-to-run path の review-ready evidence set はどれだけ揃っているか。 | evidence checklist、claim-evidence manifest、assurance summary、PR review surface、policy summary。 | present かつ reviewed の required evidence item / 全 required evidence item。 | reviewer が確認すべき missing artifact が少ないことを示す。 | human approval を置き換えない。policy work なしに blocking へ昇格しない。 |

### 4. Offline fixture / command

live GitHub API や live external agent API を呼ばず、local fixture だけで collection を確認します。

```bash no-doctest
pnpm -s run metrics:req2run -- \
  --fixture fixtures/metrics/req2run/offline-input.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/metrics/req2run-metrics.json \
  --output-md artifacts/metrics/req2run-metrics.md
```

| Surface | Path | Purpose |
| --- | --- | --- |
| Offline input | `fixtures/metrics/req2run/offline-input.json` | synthetic な requirement-to-runnable flow。 |
| JSON report | `fixtures/metrics/req2run/expected.req2run-metrics.json` | schema-valid な `req2run-metrics/v1` report-only artifact。 |
| Markdown report | `fixtures/metrics/req2run/expected.req2run-metrics.md` | sample review surface。 |
| Schema | `schema/req2run-metrics.schema.json` | local adoption-readiness evidence の preview contract。 |
| Collector | `scripts/metrics/collect-req2run-metrics.mjs` | offline-only producer。 |

### 5. Dogfooding / pilot report template

Dogfooding report や pilot report へ記録する場合は、observation id、reference-flow profile、source artifacts、
5つの canonical metric、privacy status、interpretation、limitation を必ず分けて記録します。
未収集値は 0 ではなく `not_collected` とします。

### 6. Controlled comparison requirements

Req2run metrics を controlled comparison に含める場合は、comparison unit、task category、branch policy、
denominator、synthetic/live の区別、redaction/publication approval を固定します。
事前に許される claim は「local report-only fixture で req2run metric collection を確認できる」です。
Controlled data なしに、要求が速く runnable になる、agent vendor が優れる、external adoption が証明された、とは主張しません。
