---
docRole: derived
canonicalSource:
- docs/product/PILOT-RUNBOOK-2026Q3.md
- docs/product/PILOT-EVIDENCE-TEMPLATE.md
- docs/product/EFFECTIVENESS-METRICS.md
- docs/ci/agent-pr-assurance-metrics.md
- examples/pilot-redacted/README.md
lastVerified: '2026-06-23'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency
---

# Pilot Report 2026 Q3-01: Report-Only External Agent PR Assurance

> Language / 言語: English | 日本語

---

## English

### 1. Status summary

| Field | Value |
| --- | --- |
| Report status | `dry-run only` |
| Evidence window | 2026-06-23 UTC dry-run package preparation |
| Live external repository | `not_collected` |
| Planned pilot size | 1 repository / about 5 PRs |
| Live PRs collected | 0 |
| Dry-run artifacts | `examples/pilot-redacted/` |
| Review surface posting | preview-only example; no live external PR comment posted |
| Publication status | `not approved for publication` for per-PR data |
| Allowed public claim | Pilot readiness and redaction workflow only |

This report is the ACP-097 pilot-ready dry-run report. It does **not** record a
completed external repository pilot. The available evidence is the runbook,
evidence template, synthetic redacted example, and the PR review/CI feedback that
stabilized those artifacts before merge. It must not be used to claim faster
review, safer code, agent-vendor superiority, or production adoption impact.

### 2. Evidence sources

| Source | Role in this report | Publication boundary |
| --- | --- | --- |
| `docs/product/PILOT-RUNBOOK-2026Q3.md` | Defines report-only pilot execution, consent gate, per-PR commands, and abort criteria. | Public runbook. |
| `docs/product/PILOT-EVIDENCE-TEMPLATE.md` | Defines the five-PR evidence fields and ACP-097 aggregation block. | Public template; live copied rows stay private by default. |
| `examples/pilot-redacted/pilot-evidence-log.example.csv` | Synthetic five-row placeholder showing required fields. | Public synthetic example only. |
| `examples/pilot-redacted/pilot-pr-1.agent-pr-assurance-metrics.json` | Schema-valid synthetic `agentPrAssurance` metrics placeholder. | Public synthetic example only. |
| `examples/pilot-redacted/review-surface.example.md` | Preview body for the PR review surface posting helper. | Public synthetic example only; no live reviewer metadata. |
| PR #3542 review and CI evidence | Validated the report-only package, fixed review feedback, and showed stale-check operational friction. | Public repository PR evidence, not external pilot evidence. |

### 3. Metrics table

The table uses the canonical vocabulary in `docs/product/EFFECTIVENESS-METRICS.md`.
Values that are not collected remain explicit instead of being reported as zero.

| Metric | Dry-run value | Source | Interpretation | Limitation |
| --- | --- | --- | --- | --- |
| `review_decision_time` | `not_collected` | No live maintainer disposition timestamp. | No review-speed claim is supported. | Requires live review-ready and human disposition timestamps. |
| `time_to_merge` | `not_collected` for external pilot | No live external PR merge. | No throughput claim is supported. | Internal PR timing is not an external pilot baseline. |
| `reviewer_comment_count` | `not_collected` for external pilot | No live pilot review thread state. | Reviewer feedback categories below are dry-run implementation feedback only. | External reviewer style and disposition remain unknown. |
| `scope_drift_finding_count` | `not_collected` | No live boundary-map summary from an external PR. | Scope drift was not exercised by this dry run. | A value of zero would be misleading, so it is not reported. |
| `missing_evidence_finding_count` | `not_collected` | No live producer-normalization or assurance-summary artifact. | The placeholder intentionally leaves live evidence absent. | Missing live evidence is a pilot status limitation, not a product finding. |
| `unresolved_claim_count_before_merge` | `not_collected` | No live claim evidence manifest. | No claim closure result is available. | Dry-run artifacts do not establish live claim assurance. |
| `selected_high_risk_claim_count` | `not_collected` | No live assurance profile for pilot PRs. | No high-risk escalation conclusion is available. | Follow-up pilots should record selected claims explicitly. |
| `ci_rerun_count` | External pilot: `not_collected`; internal PR #3542: one empty-amend head refresh after review-thread resolution. | PR #3542 check rollup and task ledger. | Stale same-head gate state is an operator-friction risk to watch in the live pilot. | Internal PR operational recovery is not a pilot outcome metric. |
| `policy_gate_false_positive_count` | `not_collected` | No maintainer false-positive annotation. | No policy precision claim is supported. | A later green rerun is not a false positive without manual classification. |
| `policy_gate_false_negative_count` | `not_collected` | No delayed incident or post-review finding. | No policy recall claim is supported. | Absence of observations is not evidence of zero false negatives. |

### 4. Reviewer feedback classification

No external pilot reviewer feedback has been collected. The classification below
uses dry-run implementation review feedback from PR #3542 and must be treated as
product-preparation feedback, not external pilot evidence.

| Category | Dry-run observation | Product implication |
| --- | --- | --- |
| `helpful` | Schema-valid placeholder metrics and the redacted review surface make the pilot package reviewable before a live repository is selected. | Keep synthetic artifacts contract-valid so operators can rehearse the flow. |
| `friction` | The initial review surface wording could have directed operators to edit the committed template with live disposition data. | Live pilots need a private copied evidence row or tracker, not public example edits. |
| `unclear` | A generic `assurance-review.md` token looked like a repository-relative path and failed the intended doc-consistency model. | Reviewer surfaces and runbooks should point to existing paths or use prose that cannot be interpreted as a path. |
| `next improvement` | Required-check names, reviewer disposition, raw comments, and timing remain uncollected. | A live pilot must confirm repository-specific checks, consent, redaction, private evidence storage, and publication approval before collecting data. |

### 5. Required observations

| Observation area | Current report result |
| --- | --- |
| Scope drift | `not_collected`; no live external PR boundary summary was produced. |
| Missing evidence | Live evidence is intentionally absent; only the runbook, template, and synthetic placeholder are available. |
| Stale check / CI recovery | Internal PR #3542 required a fresh head after stale same-head gate cancellations; record this as a watch item for pilot operators. |
| PR comment usability | `examples/pilot-redacted/review-surface.example.md` is preview-only and has not been posted to a live external PR. The posting helper path is ready, but `--mode comment` still requires maintainer approval. |

### 6. Limitations and residual risk

- No live external repository pilot has run.
- No human review decision time, time-to-merge, reviewer disposition, or raw
  comment evidence has been collected.
- No controlled baseline, statistical benchmark, or randomized comparison exists.
- The report uses one schema-valid synthetic metrics JSON and five placeholder
  evidence rows; this is not a representative production sample.
- Repository identity, PR URLs, reviewer identity, comments, file paths, exact
  timestamps, and business context remain absent by design.
- CI stale-check friction was observed on the internal PR that delivered the
  report package, but it has not been measured on an external pilot repository.
- Policy-gate false positives and false negatives require manual annotations or
  delayed post-review evidence; neither exists for this dry run.

### 7. Launch-kit summary paragraph

The ACP-097 pilot report is currently `dry-run only`: ae-framework has a
report-only external pilot runbook, evidence template, schema-valid synthetic
metrics JSON, and redacted review surface example, but zero live external PRs
have been collected. This supports a readiness claim for consent-safe pilot
execution and redacted reporting. It does not support claims about faster review,
safer code, agent-vendor superiority, or production adoption impact. Public
launch material should use this report only to describe the pilot path and its
limitations until maintainer-approved aggregate or redacted live data is
available.

### 8. Follow-up inputs

- Run the first live external pilot only after a maintainer approves repository
  selection, raw-output viewers, redaction rules, and publication status.
- Store live per-PR rows in a private copied evidence tracker derived from
  `docs/product/PILOT-EVIDENCE-TEMPLATE.md`.
- Collect repository-specific required-check names before running the metrics
  collector.
- Record reviewer disposition as `merge`, `request changes`, `defer`, `block`,
  or `not_collected`.
- Keep ACP-098 / launch-kit updates limited to this dry-run status until a live
  pilot report replaces the placeholder metrics.

---

## 日本語

### 1. Status summary

| Field | Value |
| --- | --- |
| Report status | `dry-run only` |
| Evidence window | 2026-06-23 UTC の dry-run package 準備 |
| Live external repository | `not_collected` |
| Planned pilot size | 1 repository / 約5 PR |
| Live PRs collected | 0 |
| Dry-run artifacts | `examples/pilot-redacted/` |
| Review surface posting | preview-only example。live external PR comment は未投稿 |
| Publication status | PR別 data は `not approved for publication` |
| Allowed public claim | pilot readiness と redaction workflow のみ |

この report は ACP-097 の pilot-ready dry-run report であり、完了済みの
external repository pilot ではありません。利用できる evidence は runbook、evidence
template、synthetic redacted example、それらを merge 前に安定化した PR review / CI
feedback です。Review speed、safer code、agent vendor superiority、production
adoption impact は主張できません。

### 2. Evidence sources

| Source | この report での役割 | Publication boundary |
| --- | --- | --- |
| `docs/product/PILOT-RUNBOOK-2026Q3.md` | report-only pilot の実行、consent gate、PR別 command、abort criteria を定義。 | 公開 runbook。 |
| `docs/product/PILOT-EVIDENCE-TEMPLATE.md` | 5 PR evidence field と ACP-097 aggregation block を定義。 | 公開 template。live copy は原則 private。 |
| `examples/pilot-redacted/pilot-evidence-log.example.csv` | 必須 field を示す synthetic 5行 placeholder。 | 公開 synthetic example のみ。 |
| `examples/pilot-redacted/pilot-pr-1.agent-pr-assurance-metrics.json` | schema-valid な synthetic `agentPrAssurance` metrics placeholder。 | 公開 synthetic example のみ。 |
| `examples/pilot-redacted/review-surface.example.md` | PR review surface posting helper 用の preview body。 | 公開 synthetic example のみ。live reviewer metadata は含めない。 |
| PR #3542 review / CI evidence | report-only package を検証し、review feedback と stale-check friction を確認。 | 公開 repository PR evidence。external pilot evidence ではない。 |

### 3. Metrics table

`docs/product/EFFECTIVENESS-METRICS.md` の canonical vocabulary を使います。未収集の値は 0 と見せず `not_collected` として残します。

| Metric | Dry-run value | Source | Interpretation | Limitation |
| --- | --- | --- | --- | --- |
| `review_decision_time` | `not_collected` | live maintainer disposition timestamp なし。 | review-speed claim は不可。 | live review-ready / human disposition timestamp が必要。 |
| `time_to_merge` | external pilot は `not_collected` | live external PR merge なし。 | throughput claim は不可。 | internal PR timing は external pilot baseline ではない。 |
| `reviewer_comment_count` | external pilot は `not_collected` | live pilot review thread state なし。 | 下記 feedback は dry-run implementation feedback に限定。 | external reviewer style / disposition は未知。 |
| `scope_drift_finding_count` | `not_collected` | external PR の boundary-map summary なし。 | scope drift は未検証。 | 0 と報告すると誤解を招くため未収集。 |
| `missing_evidence_finding_count` | `not_collected` | live producer-normalization / assurance-summary artifact なし。 | placeholder は live evidence 欠落を意図的に残す。 | live evidence 欠落は pilot status limitation であり product finding ではない。 |
| `unresolved_claim_count_before_merge` | `not_collected` | live claim evidence manifest なし。 | claim closure result は未取得。 | dry-run artifact は live claim assurance を示さない。 |
| `selected_high_risk_claim_count` | `not_collected` | pilot PR用 live assurance profile なし。 | high-risk escalation conclusion はなし。 | follow-up pilot で selected claim を明示記録する。 |
| `ci_rerun_count` | external pilot は `not_collected`; internal PR #3542 は review-thread resolution 後に empty-amend head refresh 1回。 | PR #3542 check rollup / task ledger。 | stale same-head gate state は live pilot operator の watch item。 | internal PR recovery は pilot outcome metric ではない。 |
| `policy_gate_false_positive_count` | `not_collected` | maintainer false-positive annotation なし。 | policy precision claim は不可。 | 後続 rerun が green でも manual classification なしでは false positive ではない。 |
| `policy_gate_false_negative_count` | `not_collected` | delayed incident / post-review finding なし。 | policy recall claim は不可。 | 観測なしは false negative 0 の evidence ではない。 |

### 4. Reviewer feedback classification

External pilot reviewer feedback は未収集です。以下は PR #3542 の dry-run implementation
review feedback であり、external pilot evidence ではありません。

| Category | Dry-run observation | Product implication |
| --- | --- | --- |
| `helpful` | schema-valid placeholder metrics と redacted review surface により、live repo 選定前に pilot package を確認できる。 | synthetic artifact も contract-valid に保ち、operator が手順を rehearsal できるようにする。 |
| `friction` | 初期 wording は live disposition data を committed template に書かせるように読めた。 | live pilot では公開 example ではなく private copied evidence row / tracker を使う。 |
| `unclear` | generic `assurance-review.md` token が repository-relative path と解釈され得た。 | review surface / runbook は存在する path を指すか、path と誤解されない prose にする。 |
| `next improvement` | required-check name、reviewer disposition、raw comment、timing は未収集。 | live pilot では repository-specific check、consent、redaction、private evidence storage、publication approval を先に固定する。 |

### 5. Required observations

| Observation area | Current report result |
| --- | --- |
| Scope drift | `not_collected`。live external PR boundary summary は未生成。 |
| Missing evidence | live evidence は意図的に未収集。runbook、template、synthetic placeholder のみ。 |
| Stale check / CI recovery | internal PR #3542 で stale same-head gate cancellation 後に fresh head が必要だった。pilot operator の watch item とする。 |
| PR comment usability | `examples/pilot-redacted/review-surface.example.md` は preview-only であり、live external PR には未投稿。posting helper path は用意済みだが、`--mode comment` は maintainer approval 後に限定する。 |

### 6. Limitations and residual risk

- live external repository pilot は未実施。
- human review decision time、time-to-merge、reviewer disposition、raw comment evidence は未収集。
- controlled baseline、statistical benchmark、randomized comparison はない。
- report は 1件の schema-valid synthetic metrics JSON と 5件の placeholder evidence row に依存しており、production sample ではない。
- repository identity、PR URL、reviewer identity、comment、file path、exact timestamp、business context は設計上含めていない。
- CI stale-check friction は report package の internal PR で観測したが、external pilot repository では未計測。
- policy-gate false positive / false negative には manual annotation または delayed post-review evidence が必要だが、この dry run には存在しない。

### 7. Launch-kit summary paragraph

ACP-097 pilot report は現時点で `dry-run only` です。ae-framework には report-only external
pilot runbook、evidence template、schema-valid synthetic metrics JSON、redacted
review surface example が揃いましたが、live external PR の収集件数は 0 です。これは
consent-safe pilot execution と redacted reporting の readiness claim は支えますが、review
speed、safer code、agent vendor superiority、production adoption impact は支えません。Public launch material は、maintainer-approved aggregate / redacted live data が得られるまで、この report を pilot path と limitation の説明に限定して使います。

### 8. Follow-up inputs

- live external pilot は、maintainer が repository selection、raw-output viewers、redaction rules、publication status を承認してから開始する。
- live per-PR row は `docs/product/PILOT-EVIDENCE-TEMPLATE.md` から派生した private copied evidence tracker に保存する。
- metrics collector 実行前に repository-specific required-check name を収集する。
- reviewer disposition は `merge`、`request changes`、`defer`、`block`、`not_collected` のいずれかで記録する。
- live pilot report が placeholder metrics を置き換えるまでは、ACP-098 / launch-kit update はこの dry-run status に限定する。
