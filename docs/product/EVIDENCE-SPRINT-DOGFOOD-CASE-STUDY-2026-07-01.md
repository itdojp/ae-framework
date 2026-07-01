---
docRole: derived
canonicalSource:
- docs/product/EVIDENCE-SPRINT-SELF-DOGFOOD-2026-07-01.md
- docs/product/DOGFOODING-PILOT-MEASUREMENT-PROTOCOL.md
- docs/product/REQ2RUN-METRICS.md
- docs/ci/completion-audit-report.md
lastVerified: '2026-07-01'
owner: product-assurance
verificationCommand: node scripts/ci/validate-json.mjs && pnpm -s run check:doc-consistency
---
# Evidence Sprint Dogfood Case Study: Issue #3570 to PR #3578

> Language / 言語: English | 日本語

This case study packages the first Evidence Sprint self-dogfood run into a
public, repository-backed evidence reference. It is based only on observed
repository artifacts from Issue #3570, PR #3578, checked-in fixtures, local
verification, Copilot/Codex review disposition, and the post-merge completion
audit comment.

Use this page as the primary evidence reference for README, first-run, release,
and article preparation. Use the evidence pack at
`docs/product/evidence-packs/evidence-003-self-dogfood/README.md` when a reader
needs the underlying links.

---

## English

### 1. Reusable summary

The Evidence Sprint self-dogfood run shows that ae-framework can connect one
scoped Issue to a reviewable evidence chain: scope memo, ExecPlan v2,
measurement fixture, req2run reference, PR assurance review preview,
Copilot/Codex review closure, required CI checks, and completion audit. The run
also exposed a concrete instrumentation gap: the start timestamp was not fixed
at work start, so speed-like timing remains `not_collected` and cannot support
public speed claims.

### 2. Flow at a glance

| Step | Evidence | Result |
| --- | --- | --- |
| Issue intent | #3570 | Defines the self-dogfood requirement and required evidence path. |
| Scope memo | `docs/product/EVIDENCE-SPRINT-SELF-DOGFOOD-2026-07-01.md` | Fixes docs/fixtures-only scope, non-goals, claim boundary, and observations. |
| Plan | `fixtures/evidence-sprint/self-dogfood/exec-plan.v2.json` | Schema-valid ExecPlan v2 links task graph, verification, evidence, stop rules, and rollback. |
| Metrics | `fixtures/evidence-sprint/self-dogfood/measurement-report.json` | Uses the #3569 protocol and records `not_collected` where data was absent. |
| Domain preset | not applicable | This was a docs/fixtures self-dogfood flow; #3572 and #3573 cover domain preset reports. |
| Req2run reference | `fixtures/metrics/req2run/expected.req2run-metrics.json` | Reuses the report-only requirement-to-runnable metric surface. |
| Review surface | `fixtures/evidence-sprint/self-dogfood/pr-assurance-review.md` | Gives reviewers a pre-closeout traceability checklist. |
| PR | #3578 | Implements the case input as a docs/fixtures PR. |
| Review closure | `pr-review-completeness` for PR #3578 | Final state: `reviews=6`, `review_comments=8`, `review_threads=4`, `unresolved_threads=0`. |
| CI / verification | Required checks on final head `6c9a83f...` | `gate`, `policy-gate`, and `verify-lite` passed; full rollup had no non-pass entries. |
| Completion audit | #3570 completion audit comment | Separates required checks, advisory workflows, stale run handling, and local verification. |

### 3. Evidence pack

The stable evidence index is:

- `docs/product/evidence-packs/evidence-003-self-dogfood/README.md`

It contains direct links to:

- Issue #3570;
- PR #3578;
- the post-merge completion audit comment;
- checked-in scope memo, ExecPlan v2, measurement report, and review preview;
- final required-check job URLs;
- review-disposition evidence;
- public-claim limitations.

### 4. Observed outcomes

| Outcome | Evidence | Interpretation |
| --- | --- | --- |
| Traceability chain completed | #3570 -> #3578 -> completion audit comment | The repository can present one Issue-to-PR evidence chain without relying on prose alone. |
| Review feedback was actionable | Four Copilot/Codex threads | The review found fixture and wording issues before merge; all were fixed and resolved. |
| Required checks passed | PR #3578 final rollup | The final PR head reached `mergeStateStatus=CLEAN` with no non-pass status-check entries. |
| Timing was not collected | Measurement fixture and completion audit | The protocol correctly avoided a speed claim when the run-start timestamp was missing. |
| Scope memo was sufficient | Case report and ExecPlan v2 | A small docs/fixtures flow did not need a new Context Pack slice, but still had an explicit boundary. |

### 5. Report-only and public-claim boundary

Supported by this case study:

- One scoped ae-framework run produced a traceable evidence chain from Issue to
  completion audit.
- The repository can collect and publish Evidence Sprint metric surfaces from
  local artifacts and observed PR state.
- The run revealed concrete follow-up items: capture run-start timestamps and
  keep pre-merge planning evidence separate from post-merge audit evidence.

Not supported by this case study:

- generalized speed, review-efficiency, safety, quality, or adoption claims;
- agent/vendor comparison;
- autonomous approval or guaranteed merge readiness;
- claims about external repository pilots or controlled comparisons.

### 6. Follow-up backlog

| Follow-up | Linked Issue | Evidence trigger |
| --- | --- | --- |
| Use this case study as the public evidence reference. | #3571 | This page and the evidence pack. |
| Connect README first-run path to a concrete demo plus evidence reference. | #3574 | Case study needs a first-run route for new readers. |
| Prepare release/article/announcement copy from observed evidence only. | #3575 | Public copy must avoid unsupported speed/safety/adoption claims. |
| Run Web API and event-driven pilots with domain preset reports. | #3572, #3573 | Self-dogfood is internal; domain pilots are still needed. |
| Capture run-start timestamps before future timing metrics. | not yet split | `time_to_first_runnable_verification_minutes = not_collected`. |

---

## 日本語

### 1. 再利用可能な要約

Evidence Sprint の self-dogfood では、1つの Issue から scope memo、ExecPlan v2、measurement fixture、req2run reference、PR assurance review preview、Copilot/Codex review closure、required CI、completion audit までを接続できることを確認しました。同時に、作業開始 timestamp を固定していなかったため、速度系 metric は `not_collected` とし、公開の speed claim には使わない、という制限も明確になりました。

### 2. 読み方

詳細な証跡一覧は `docs/product/evidence-packs/evidence-003-self-dogfood/README.md` を参照してください。この case study は public evidence の入口であり、承認・merge authority ではありません。

### 3. 主張できること / できないこと

主張できるのは、この scoped run の Issue-to-PR evidence chain、metric collection readiness、具体的な follow-up です。速度改善、安全性、品質改善、外部 adoption、agent vendor 比較、自律承認はこの case study からは主張しません。
