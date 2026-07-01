---
docRole: derived
canonicalSource:
- docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md
- docs/product/evidence-packs/evidence-003-self-dogfood/README.md
- docs/getting-started/FIRST-RUN-DEMO.md
- docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md
- docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md
- docs/ci/completion-audit-report.md
- docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency && pnpm -s run docs:lint
---

# Evidence Sprint Release Assets 2026-07-01

> Language / 言語: English | 日本語

This file prepares outward-facing materials for Evidence Sprint Issue #3575. It
is intentionally claim-limited: every public-facing statement below is either
linked to observed repository evidence or marked as a future hypothesis.

---

## English

### 1. Release note draft

#### Title
Evidence Sprint: first-run demo, dogfood case study, and report-only pilot evidence

#### Summary
This Evidence Sprint packages ae-framework's agent-neutral assurance control
plane into a clearer public evidence path. The repository now has a one-command
first-run demo, an observed self-dogfood case study and evidence pack, a
completion-audit report contract, a measurement protocol, and two fixture-backed
domain pilot reports.

#### What's included

| Release note item | Evidence link | Public wording boundary |
| --- | --- | --- |
| One-command first-run demo | `docs/getting-started/FIRST-RUN-DEMO.md` | New evaluators can run `pnpm run demo:agent-assurance` after dependency installation and open `artifacts/review/agent-assurance-demo/assurance-review.md`. |
| Observed self-dogfood case study | `docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md` | Shows one repository-local Issue-to-PR assurance flow; not a generalized speed or quality benchmark. |
| Stable dogfood evidence pack | `docs/product/evidence-packs/evidence-003-self-dogfood/README.md` | Provides links to issue, PR, checked-in evidence, review completeness, local verification, and completion audit. |
| Completion audit report contract | `docs/ci/completion-audit-report.md` | Separates required merge checks from advisory workflow-run findings during PR closeout. |
| Measurement protocol | `docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md` | Defines report-only metrics such as evidence coverage, missing evidence, unresolved claims, review rework, deterministic replay, manual intervention, and audit discrepancy counts. |
| Fixture-backed Web API pilot | `docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md` | Demonstrates API-contract evidence and domain preset routing on repository fixtures; no live API behavior claim. |
| Fixture-backed event-driven pilot | `docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md` | Demonstrates selected-trace invariant/conformance evidence and domain preset routing on repository fixtures; no production event-ordering claim. |
| Live-pilot entry criteria | `docs/product/LIVE-PILOT-ENTRY-CRITERIA.md` | Defines consent, data handling, retention, evidence, measurement, baseline, and claim-boundary prerequisites before fixture-backed material can support a live external claim. |

#### Suggested changelog paragraph
Evidence Sprint adds a public, reproducible evidence route for ae-framework:
start with `pnpm run demo:agent-assurance`, inspect the generated assurance
review surface, then read the self-dogfood case study, evidence pack, and
fixture-backed Web API / event-driven pilots. The materials intentionally keep
runtime demos, dogfooding observations, fixture-backed pilots, and future
hypotheses separate. Supported claims are limited to review traceability,
evidence routing, report-only measurement readiness, and completion-audit
separation; review-speed, safety, adoption-impact, live API/event behavior, and
agent-vendor claims remain unsupported.

### 2. Concept article outline

#### Working title
Bring your own agent. Keep your assurance plane.

#### Target reader
Engineering leaders and senior developers evaluating coding-agent workflows who
need stable release judgment artifacts across Codex, Copilot, Claude Code,
human maintainers, CI jobs, and formal tools.

#### Thesis
Agents are replaceable producers; merge and release judgment should depend on a
stable assurance plane that records evidence, policy, review surfaces, and
claim boundaries.

#### Outline

1. **Problem: producer output is not approval**
   - Evidence: `docs/product/ASSURANCE-CONTROL-PLANE.md` and
     `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` define producer vs.
     judgment boundaries.
   - Claim boundary: do not say any agent is more reliable or productive.
2. **Agent-neutral assurance control plane**
   - Explain Context Pack, evidence aggregation, policy gate summaries,
     reviewer Markdown, and completion audit as judgment artifacts.
   - Evidence: `docs/ci/completion-audit-report.md` and the self-dogfood
     evidence pack.
3. **Report-only metrics before enforcement**
   - Explain measurement slots from the Evidence Sprint protocol.
   - Evidence: `docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md`.
4. **What changed in the Evidence Sprint**
   - First-run demo, case study, evidence pack, Web API pilot, event-driven pilot.
   - Evidence: release note table above.
5. **What is deliberately not claimed**
   - No speed, safety, quality, adoption, live behavior, or vendor benchmark
     claim without controlled baseline data.
6. **Call to action**
   - Run `pnpm run demo:agent-assurance`, open
     `artifacts/review/agent-assurance-demo/assurance-review.md`, then read the
     case study and evidence pack.

### 3. Practical dogfood article outline

#### Working title
Dogfooding an assurance control plane: from Issue to PR completion audit

#### Target reader
Practitioners who want to inspect a concrete repository-local flow before
adopting the first-run demo or evidence protocol.

#### Thesis
The practical value of ae-framework is not that it writes code; it keeps the
Issue intent, evidence, review surface, CI state, and completion audit connected
and reviewable.

#### Outline

1. **Start with the first-run demo**
   - Command: `pnpm run demo:agent-assurance`.
   - Output: `artifacts/review/agent-assurance-demo/assurance-review.md`.
   - Evidence: `docs/getting-started/FIRST-RUN-DEMO.md`.
2. **Read the observed case study**
   - Evidence: `docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md`.
   - Explain the Issue-to-PR assurance flow and report-only boundary.
3. **Inspect the evidence pack**
   - Evidence: `docs/product/evidence-packs/evidence-003-self-dogfood/README.md`.
   - Show where issue, PR, local verification, review completeness, and
     completion audit are linked.
4. **Compare the two domain pilots**
   - Web API pilot: API contract evidence and measurement fixture.
   - Event-driven pilot: selected trace, invariant assumptions, and conformance
     summary.
   - Boundary: both pilots are fixture-backed and report-only.
5. **Close the PR with audit evidence**
   - Evidence: completion audit contract and PR review-completeness outputs.
   - Explain the difference between required checks and advisory workflow-run
     findings.
6. **Operational lessons**
   - Keep first-run command singular.
   - Keep unsupported claims visible.
   - Promote findings to enforcement only after repeated evidence, not after one
     successful fixture run.

### 4. Announcement copy

#### Short post
Evidence Sprint for ae-framework is now packaged as a public evidence path:
`pnpm run demo:agent-assurance` → generated assurance review surface → dogfood
case study → evidence pack → fixture-backed Web API and event-driven pilots.

The claim boundary is explicit: this supports review traceability and evidence
routing in this repository, not review-speed, safety, adoption-impact, live
API/event behavior, or agent-vendor superiority claims.

Start here: `docs/getting-started/FIRST-RUN-DEMO.md`
Evidence pack: `docs/product/evidence-packs/evidence-003-self-dogfood/README.md`

#### Longer post
We finished an Evidence Sprint for ae-framework, focused on observed repository
evidence rather than abstract capability claims.

What is now available:

- one first-run command: `pnpm run demo:agent-assurance`;
- a reviewer-facing artifact to open first:
  `artifacts/review/agent-assurance-demo/assurance-review.md`;
- a self-dogfood case study and evidence pack;
- a completion-audit report contract that separates required merge checks from
  advisory workflow-run findings;
- a report-only measurement protocol;
- fixture-backed Web API and event-driven pilot reports.

The important boundary: these materials support claims about review
traceability, evidence routing, measurement readiness, and audit separation in
this repository. They do not support generalized productivity, safety, quality,
adoption, live API/event correctness, or agent-vendor benchmark claims.

If you want to evaluate the idea, start with
`docs/getting-started/FIRST-RUN-DEMO.md`, then inspect the dogfood evidence pack.

### 5. Supported / unsupported claims checklist

| Claim | Status | Evidence or disposition |
| --- | --- | --- |
| ae-framework has a one-command local first-run demo. | Supported | `docs/getting-started/FIRST-RUN-DEMO.md`; local validation uses `pnpm run demo:agent-assurance`. |
| The demo produces a reviewer-facing assurance surface. | Supported | First-run doc and demo output path `artifacts/review/agent-assurance-demo/assurance-review.md`. |
| Evidence Sprint includes an observed self-dogfood case study. | Supported | `docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md`. |
| The self-dogfood run has a stable evidence pack. | Supported | `docs/product/evidence-packs/evidence-003-self-dogfood/README.md`. |
| Completion audit separates required checks from advisory workflow-run findings. | Supported | `docs/ci/completion-audit-report.md` and the checked-in self-dogfood evidence pack `docs/product/evidence-packs/evidence-003-self-dogfood/README.md`. |
| Web API and event-driven domain pilot materials exist. | Supported | `docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md` and `docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md`. |
| The pilots prove live API or production event correctness. | Unsupported | Both pilot reports are fixture-backed/report-only. |
| ae-framework makes reviews faster. | Unsupported | The controlled comparison protocol has not been executed. |
| ae-framework makes code safer or higher quality in general. | Unsupported | Current evidence is traceability and evidence-routing evidence, not safety or quality outcome evidence. |
| ae-framework outperforms a specific coding-agent vendor. | Unsupported | Vendor benchmarking is a non-goal; agents are treated as producers, not benchmark subjects. |
| Future controlled comparison may evaluate review workflow differences. | Hypothesis / future work | `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md`; no result claim until comparable baseline data exists. |

### 6. Follow-up improvement issue candidates

These are not required for this release asset package, but they are concrete
follow-ups observed during the Evidence Sprint:

1. Parameterize the event-driven domain preset so selected trace fixtures are
   first-class in the preset starting command, not only in pilot-specific
   documentation.
2. Add an optional artifact checker focused on the first-run demo review surface
   so users can verify expected paths after local cleanup.
3. Apply the live-pilot entry criteria in
   `docs/product/LIVE-PILOT-ENTRY-CRITERIA.md` before turning fixture-backed
   evidence into external pilot claims.

---

## 日本語

### 1. Release note draft

Evidence Sprint では、ae-framework の agent-neutral assurance control plane を
外向きに説明できる evidence path として整理しました。新規 evaluator は
`pnpm run demo:agent-assurance` を実行し、生成された review surface を確認した後、
self-dogfood case study、evidence pack、fixture-backed Web API / event-driven
pilot を読む導線に進めます。

この release note が主張できる範囲は、review traceability、evidence routing、
report-only measurement readiness、completion-audit separation です。Review speed、
safety、quality、adoption impact、live API/event behavior、agent/vendor 優位性は、
現在の観測証跡からは主張しません。

### 2. Concept article outline

Working title: **Bring your own agent. Keep your assurance plane.**

1. Producer output は approval ではない。
2. ae-framework は agent-neutral assurance control plane として、evidence、policy、
   reviewer surface、claim boundary を安定化する。
3. Enforcement の前に report-only metrics と completion audit を置く。
4. Evidence Sprint で first-run demo、case study、evidence pack、domain pilots が
   public evidence route になった。
5. Speed、safety、quality、adoption、vendor benchmark は未支持 claim として分離する。
6. Call to action: `pnpm run demo:agent-assurance` を実行し、review surface と
   evidence pack を読む。

### 3. Practical dogfood article outline

Working title: **Dogfooding an assurance control plane: from Issue to PR completion audit**

1. `docs/getting-started/FIRST-RUN-DEMO.md` から開始する。
2. `docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md` で観測済み flow を読む。
3. `docs/product/evidence-packs/evidence-003-self-dogfood/README.md` で Issue、PR、local verification、review completeness、completion audit の link を確認する。
4. Web API pilot と event-driven pilot を fixture-backed/report-only evidence として比較する。
5. Required checks と advisory workflow-run findings を completion audit で分離する。
6. 単一の成功例から enforcement や一般 claim に昇格しない運用を説明する。

### 4. Announcement copy

Evidence Sprint for ae-framework is now packaged as a public evidence path:
`pnpm run demo:agent-assurance` → generated assurance review surface → dogfood
case study → evidence pack → fixture-backed Web API and event-driven pilots.

Supported claims are intentionally narrow: review traceability, evidence routing,
measurement readiness, and audit separation in this repository. Unsupported
claims remain out of scope: review-speed, safety, quality, adoption impact, live
API/event correctness, and agent/vendor superiority.

Start here: `docs/getting-started/FIRST-RUN-DEMO.md`
Evidence pack: `docs/product/evidence-packs/evidence-003-self-dogfood/README.md`

### 5. Supported / unsupported claims checklist

- Supported: one-command first-run demo, generated review surface, self-dogfood
  case study, stable evidence pack, completion-audit separation, fixture-backed
  Web API / event-driven pilot materials.
- Unsupported: live API correctness、production event ordering、review-speed、
  safety、quality、adoption impact、agent/vendor benchmark。
- Hypothesis / future work: controlled comparison protocol に基づく review
  workflow comparison。Comparable baseline data が揃うまでは結果 claim にしません。
