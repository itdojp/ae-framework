---
docRole: ssot
lastVerified: '2026-06-23'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency
---

# Product Effectiveness Metrics for Agent-Generated PR Assurance

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This document defines the shared metric vocabulary for proving ae-framework's
product effectiveness in agent-generated pull request assurance. The primary
claim is:

> ae-framework helps reviewers judge agent-generated PRs faster and more
> correctly by turning producer output into reviewable evidence, policy-gated
> summaries, and unresolved-risk surfaces.

The metrics below measure the **review and judgment workflow**, not raw agent
performance. They must be reused by the 15-minute quickstart, local demos,
dogfooding reports, controlled benchmarks, and public launch material so that
all product claims use the same evidence vocabulary.

Current internal dogfooding report: `docs/product/DOGFOODING-REPORT-2026Q3.md`.
Current external pilot report: `docs/product/PILOT-REPORT-2026Q3-01.md` (`dry-run only`; no live external PRs collected).
Controlled comparison protocol: `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md` (`protocol-ready, not executed`).
External pilot onboarding and consent boundary: `docs/guides/external-pilot-onboarding.md`.
Req2run adoption-readiness extension: `docs/product/REQ2RUN-METRICS.md`.

### 2. Measurement boundary

| Boundary | Rule |
| --- | --- |
| Product claim | Measure whether the reviewer can reach a merge, request changes, defer, or block decision with clearer evidence. |
| Producer boundary | Codex, Claude Code, GitHub Copilot, CI, formal tools, and human maintainers are evidence producers, not approval authorities by themselves. |
| Primary surfaces | Prefer summary artifacts and PR review surfaces over raw logs. Raw logs are supporting evidence only. |
| Enforcement default | Metrics start report-only. A metric definition does not create a new `policy-gate` block condition. |
| Comparison scope | Compare ae-framework-assisted review against a baseline review workflow when controlled data exists. Do not rank agent vendors unless the study design explicitly supports that claim. |
| Privacy boundary | Repository-sensitive PR text, timing data, reviewer names, and internal comments must be aggregated, redacted, or kept private unless publication is explicitly approved. |

### 3. Canonical metrics

| Metric | Reviewer question | Source artifact / source | Collection method | Interpretation | Limitation |
| --- | --- | --- | --- | --- | --- |
| `review_decision_time` | How long did it take from review-ready state to a defensible reviewer decision? | PR review timeline, review thread state, PR summary, optional manual timing note. | Record minutes from the review-ready timestamp (PR opened for non-draft PRs, or draft marked ready) to the first human `APPROVED` / `CHANGES_REQUESTED` review, or an explicitly tagged maintainer disposition comment such as `defer` / `block`. | Lower time can indicate a clearer review surface when decision quality is not worse. | Timing is sensitive to reviewer availability, timezone, queueing, and PR size. Non-GitHub dispositions require manual annotation; do not claim causality without a controlled baseline. |
| `scope_drift_finding_count` | How many findings show the change moved outside the declared Issue / Context Pack / boundary-map scope? | `boundary-map-summary`, `producer-normalization-summary/v1`, `assurance-summary/v1`, PR review comments. | Count report-only findings categorized as scope drift or boundary mismatch. Keep resolved and unresolved counts separate. | Higher count may mean the control plane found review-relevant drift; lower count after fixes may show better scoping. | A count of zero does not prove absence of drift unless the relevant boundary checks covered the changed files. |
| `missing_evidence_finding_count` | How many claims or producer assertions lacked supporting evidence? | `producer-normalization-summary/v1`, `assurance-summary/v1`, `claim-evidence-manifest/v1`, `policy-gate-summary/v1`. | Count missing-evidence findings by severity and source artifact; dedupe identical claim/finding pairs. | Helps reviewers focus on unsupported claims before merge. | Producer assertions vary in quality; missing evidence may be intentionally report-only for routine changes. |
| `unresolved_claim_count_before_merge` | How many PR-relevant claims remained unresolved at final merge readiness? | `claim-evidence-manifest/v1`, `claim-level-summary/v1`, `assurance-summary/v1`, `policy-decision/v1`. | Capture unresolved count at the final pre-merge review snapshot. Include waived claims separately. | Lower counts can indicate stronger evidence closure; non-zero may be acceptable when policy keeps them report-only or waived. | Requires a stable definition of PR-relevant claims and cannot be compared across unrelated PR sizes without normalization. |
| `selected_high_risk_claim_count` | How many `high` / `critical` claims were intentionally selected for high-assurance escalation? | `assurance-profile`, `assurance-summary/v1`, PR review Markdown, `policy-gate-summary/v1`. | Count only claims explicitly selected by the profile, Issue, or reviewer policy. Do not infer selection from producer confidence. | Shows that high assurance is scoped to selected claims instead of forcing heavy lanes on every PR. | A higher count is not automatically better; the denominator and domain risk must be stated. |
| `policy_gate_false_positive_count` | How many policy blocks were later judged unnecessary? | `policy-gate-summary/v1`, GitHub checks, PR comments, manual operator annotation. | Count block/fail decisions annotated as false positive within a fixed observation window. | Tracks policy precision and operational friction. | Requires manual classification; do not infer false positives from a later green rerun alone. |
| `policy_gate_false_negative_count` | How many policy passes missed a finding later judged policy-relevant? | Post-review findings, incident/defect notes, manual operator annotation, policy decision history. | Count policy-relevant misses discovered after a pass and classify root cause. | Tracks policy recall and missed-risk exposure. | Usually sparse and delayed; absence of observations is not proof of zero false negatives. |
| `ci_rerun_count` | How many CI reruns or head refreshes were needed to reach a clean PR state? | GitHub check runs, PR maintenance comments, workflow run history. | Count reruns and empty-amend head refreshes; separate flaky/stale-check recovery from code-fix reruns. | High counts indicate review-loop friction or flaky automation. | GitHub Actions cancellations and stale same-head checks must be classified before comparison. |
| `reviewer_comment_count` | How much human/AI review discussion was needed before the decision? | PR review bodies, inline comments, unresolved/resolved review threads. | Count actionable comments and informational comments separately; record unresolved count at decision time. | Lower actionable count can mean clearer evidence, but increased comments can also show better risk discovery. | Comment style varies by reviewer/team and should not be used as a standalone quality metric. |
| `time_to_merge` | How long did the PR take from review-ready state to merge? | PR timeline, merge timestamp, review and CI state. | Measure elapsed minutes from the review-ready timestamp (PR opened for non-draft PRs, or draft marked ready) to merge; optionally split waiting-for-review, waiting-for-CI, fixing-review, and blocked segments. | Useful adoption and throughput metric when segmented. | Strongly affected by queueing, reviewer availability, branch protection, and release windows. |

### 4. Metric mapping to existing artifacts

| Metric | Preferred existing artifact | Secondary source | Downstream use |
| --- | --- | --- | --- |
| `review_decision_time` | PR review timeline / PR summary | Manual reviewer timing note | Dogfooding report, controlled benchmark. |
| `scope_drift_finding_count` | `boundary-map-summary`, `assurance-summary/v1` review surface | Inline review comments | Scope drift scenario demo, launch kit. |
| `missing_evidence_finding_count` | `producer-normalization-summary/v1`, `assurance-summary/v1`, `policy-gate-summary/v1` | PR summary comments | Quickstart, review Markdown surface, dogfooding report. |
| `unresolved_claim_count_before_merge` | `claim-evidence-manifest/v1`, `assurance-summary/v1` | `policy-decision/v1` | High-risk escalation demo, dogfooding report. |
| `selected_high_risk_claim_count` | `assurance-profile`, `assurance-summary/v1`, PR review Markdown | `policy-gate-summary/v1` | High-risk escalation demo, launch kit. |
| `policy_gate_false_positive_count` / `policy_gate_false_negative_count` | `policy-gate-summary/v1` plus manual annotation | PR comments and issue follow-ups | Policy tuning and launch risk notes. |
| `ci_rerun_count` | GitHub check runs / PR maintenance state | Local verification notes | Dogfooding report operational friction section. |
| `reviewer_comment_count` | Review thread state | Review completeness report | Review Markdown surface iteration and dogfooding report. |
| `time_to_merge` | PR timeline | Release notes / merge queue state | Adoption proof and launch kit claims. |

`docs/ci/agent-pr-assurance-metrics.md` and the optional
`agentPrAssurance` extension in `schema/agentic-metrics.schema.json` define a
lower-level report-only contract for PR assurance metrics. This product document
uses a broader product-effectiveness vocabulary and may map to those lower-level
metrics when a machine-readable report is available. The report-only collector
`pnpm run metrics:agent-pr-assurance` writes `artifacts/metrics/agent-pr-assurance-metrics.{json,md}`
and stores this vocabulary under `agentPrAssurance.productMetrics`.
`time_to_merge_minutes` is only collected when a review-ready timestamp is
explicitly available, because PR creation time is not equivalent to review-ready
time for draft or delayed-review PRs. Missing optional inputs must remain
`not_collected` / `unknown` rather than being reported as zero.

### 4.1 Req2run adoption-readiness extension

Req2run metrics measure whether a requirement can become runnable, reviewable,
evidence-backed work through the reference flow. They are defined in
`docs/product/REQ2RUN-METRICS.md` and produced locally by
`pnpm run metrics:req2run`. They extend the vocabulary without changing the
claim boundary: the metrics evaluate ae-framework workflow effectiveness, not
agent vendor quality.

| Metric | Preferred existing artifact | Collection boundary | Downstream use |
| --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | requirement/Issue timing, ExecPlan v2, `verify-lite-run-summary`, loop summary | report-only timing from requirement acceptance to first passing runnable verification | onboarding friction, controlled comparison covariate |
| `spec_task_evidence_coverage` | ExecPlan v2 task graph, Spec Kit task import, claim-evidence manifest | required tasks with at least one evidence reference / all required tasks | adoption readiness, dogfooding report template |
| `deterministic_replay_pass_rate` | loop-run summary replay evidence, fixture hashes, validation outputs | passing local replay attempts / all replay attempts | reproducibility and variance-reduction evidence |
| `manual_intervention_count` | operator note, loop summary stop/next-action, Issue or private tracker annotation | count of human interventions before runnable evidence exists | onboarding friction and docs/automation improvement |
| `evidence_review_completeness` | claim-evidence manifest, assurance summary, PR assurance review surface | required evidence items present and reviewed / all required evidence items | PR review readiness and launch-material limitations |

### 5. Collection rules

1. **Keep denominators explicit.** Always record the number of PRs, claims,
   findings, comments, or check runs behind a ratio.
2. **Separate discovery from failure.** A scope-drift or missing-evidence finding
   may show that the control plane found useful risk; it is not automatically a
   product failure.
3. **Separate current from stale CI state.** Stale/cancelled checks from an older
   head must not be counted as current regressions without classification.
   Use `current_required_failure` / `policy_semantic_failure` for semantic
   blocking states and `stale_cancelled`, `superseded`, `same_head_stale`, or
   `manual_rerun_required` for operational CI recovery notes. Later green reruns
   are not policy-gate false positives unless a maintainer manually annotates
   the original block as unnecessary. When `ci_rerun_classification_counts` is
   available, treat it as non-additive classification facets: `same_head_stale`
   may overlap with `stale_cancelled` or `superseded`.
4. **Segment time metrics.** Queueing, human review, CI, review-fix, and merge
   waiting time should be separated when data is available.
5. **Use summary artifacts first.** Prefer `assurance-summary/v1`,
   `policy-gate-summary/v1`, `claim-evidence-manifest/v1`, and PR review
   Markdown before raw logs.
6. **Retain report-only semantics.** Metrics can inform `risk:high` or
   `enforce-assurance` decisions, but this document does not promote any metric
   into a blocking gate.

### 6. Public-claim rules

Public material, demos, and launch notes must follow these rules:

- Do not claim faster review unless `review_decision_time` or `time_to_merge`
  was measured with comparable baselines or the wording is explicitly scoped to
  the demo scenario.
- Do not claim requirements become runnable faster unless
  `time_to_first_runnable_verification_minutes` was measured under the req2run
  protocol with comparable baselines; local fixture output only supports
  instrumentation readiness.
- Do not claim safer code solely from fewer comments, fewer unresolved claims, or
  green CI.
- Do not claim agent vendor superiority from these metrics. They measure the
  ae-framework assurance plane around producer output.
- Do not publish repository-sensitive PR text, reviewer identity, or raw timing
  data without approval.
- For external pilots, follow `docs/guides/external-pilot-onboarding.md` and
  record whether each PR is approved for publication, aggregate-only, private, or
  not approved for publication.
- State whether a metric is measured, estimated, manually annotated, or not yet
  collected.

### 7. How later work should reuse this document

| Later surface | Required use of this metric vocabulary |
| --- | --- |
| 15-minute quickstart / local demo | Show a small, deterministic subset of `missing_evidence_finding_count`, `scope_drift_finding_count`, and reviewer-surface artifacts without claiming real-world improvement. |
| Req2run local fixture | Use `docs/product/REQ2RUN-METRICS.md` and `pnpm run metrics:req2run` to demonstrate requirement-to-runnable metric collection without live external agent APIs; do not convert fixture timing into an adoption-speed claim. |
| PR assurance review Markdown | Use the same metric names for counts and unresolved-risk summaries. |
| Scope drift / high-risk demos | Report findings with these metric names and clearly distinguish report-only from blocking behavior. |
| Cross-agent fixtures | Keep producer identity separate from reviewer-effectiveness metrics. |
| Dogfooding report | Aggregate the canonical metrics over ae-framework PRs and record limitations. |
| External pilot onboarding / ACP-097 report | Start from report-only collection, preserve consent/redaction status per PR, publish only approved aggregate or redacted data, and link `docs/product/PILOT-REPORT-2026Q3-01.md` when the current pilot status is needed. |
| Controlled comparison protocol | Compare `without ae-framework` and `with ae-framework` review workflows only when the baseline, sample categories, controls, and redaction boundaries in `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md` are satisfied. |
| Public launch kit | Use only measured or explicitly demo-scoped claims from this vocabulary. |

---

## 日本語

### 1. 目的

この文書は、agent-generated pull request assurance における ae-framework の
product effectiveness を示すための共通 metric vocabulary を定義します。Primary claim は次です。

> ae-framework は producer output を reviewable evidence、policy-gated summary、
> unresolved-risk surface に変換し、reviewer が agent-generated PR をより速く、より正しく判断できるようにする。

以下の metric は **review / judgment workflow** を測ります。raw agent performance は主対象ではありません。15分 quickstart、local demo、dogfooding report、controlled benchmark、public launch material は、同じ evidence vocabulary を再利用します。

現在の internal dogfooding report: `docs/product/DOGFOODING-REPORT-2026Q3.md`。
現在の external pilot report: `docs/product/PILOT-REPORT-2026Q3-01.md`（`dry-run only`、live external PR 収集 0件）。
Controlled comparison protocol: `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md`（`protocol-ready, not executed`）。
External pilot onboarding と consent boundary: `docs/guides/external-pilot-onboarding.md`。
Req2run adoption-readiness extension: `docs/product/REQ2RUN-METRICS.md`。

### 2. 測定境界

| Boundary | Rule |
| --- | --- |
| Product claim | reviewer が merge / request changes / defer / block を、より明確な evidence で判断できるかを測る。 |
| Producer boundary | Codex、Claude Code、GitHub Copilot、CI、formal tool、人間の maintainer は evidence producer であり、それだけで approval authority ではない。 |
| Primary surfaces | raw log より summary artifact と PR review surface を優先する。Raw log は補助証跡。 |
| Enforcement default | metric は report-only から始める。Metric 定義だけで新しい `policy-gate` block 条件を作らない。 |
| Comparison scope | controlled data がある場合に ae-framework-assisted review と baseline review workflow を比較する。研究設計がない限り agent vendor を順位付けしない。 |
| Privacy boundary | repository-sensitive な PR text、timing data、reviewer name、internal comment は、公開承認がない限り集約・redact・非公開にする。 |

### 3. Canonical metrics

| Metric | Reviewer question | Source artifact / source | Collection method | Interpretation | Limitation |
| --- | --- | --- | --- | --- | --- |
| `review_decision_time` | review-ready state から defensible reviewer decision までにどれくらいかかったか。 | PR review timeline、review thread state、PR summary、optional manual timing note。 | review-ready timestamp（非draft PRはopen時刻、draft PRはready化時刻）から、最初の human `APPROVED` / `CHANGES_REQUESTED` review、または `defer` / `block` と明示tagされた maintainer disposition comment までの分数を記録する。 | decision quality が悪化していない場合、短縮は review surface の明確化を示し得る。 | reviewer availability、timezone、queue、PR size の影響が大きい。GitHub標準外のdispositionはmanual annotationが必要。Controlled baseline なしで因果を主張しない。 |
| `scope_drift_finding_count` | 変更が declared Issue / Context Pack / boundary-map scope から外れた finding は何件か。 | `boundary-map-summary`、`producer-normalization-summary/v1`、`assurance-summary/v1`、PR review comments。 | scope drift または boundary mismatch と分類された report-only finding を数える。resolved / unresolved を分ける。 | count が多いことは、review-relevant drift を発見できたことを示す場合がある。修正後の減少は scope 改善を示し得る。 | 0件は drift 不在の証明ではない。対象fileを boundary check が覆っていることを確認する必要がある。 |
| `missing_evidence_finding_count` | claim または producer assertion のうち supporting evidence が不足したものは何件か。 | `producer-normalization-summary/v1`、`assurance-summary/v1`、`claim-evidence-manifest/v1`、`policy-gate-summary/v1`。 | severity と source artifact ごとに missing-evidence finding を数え、同一 claim/finding pair は dedupe する。 | reviewer が merge 前に unsupported claim へ集中できる。 | producer assertion の品質に依存する。通常変更では意図的に report-only の場合がある。 |
| `unresolved_claim_count_before_merge` | final merge readiness 時点で未解決の PR-relevant claim は何件か。 | `claim-evidence-manifest/v1`、`claim-level-summary/v1`、`assurance-summary/v1`、`policy-decision/v1`。 | 最終 pre-merge review snapshot の unresolved count を取得する。waived claim は別に記録する。 | count 低下は evidence closure の改善を示し得る。policy が report-only / waiver として許容する場合は非0でもよい。 | PR-relevant claim の定義が必要。PR size の異なる比較では正規化が必要。 |
| `selected_high_risk_claim_count` | high-assurance escalation に明示的に選ばれた `high` / `critical` claim は何件か。 | `assurance-profile`、`assurance-summary/v1`、PR review Markdown、`policy-gate-summary/v1`。 | profile、Issue、reviewer policy が明示した claim だけを数える。producer confidence から推測しない。 | heavy lane を全PRへ強制せず、selected claim に限定していることを示す。 | count が多いこと自体は良し悪しではない。分母と domain risk を明示する。 |
| `policy_gate_false_positive_count` | 後で不要と判断された policy block は何件か。 | `policy-gate-summary/v1`、GitHub checks、PR comments、manual operator annotation。 | 固定観測期間で false positive と注記された block/fail decision を数える。 | policy precision と operational friction を追跡する。 | manual classification が必要。後続rerunで green になっただけでは false positive と推定しない。 |
| `policy_gate_false_negative_count` | policy pass 後に policy-relevant と判断された finding は何件か。 | post-review findings、incident/defect notes、manual operator annotation、policy decision history。 | pass 後に発見された policy-relevant miss を数え、root cause を分類する。 | policy recall と missed-risk exposure を追跡する。 | 発見が遅く sparse になりやすい。観測がないことは false negative 0 の証明ではない。 |
| `ci_rerun_count` | clean PR state 到達までに CI rerun / head refresh が何回必要だったか。 | GitHub check runs、PR maintenance comments、workflow run history。 | rerun と empty-amend head refresh を数え、flaky/stale-check recovery と code-fix rerun を分ける。 | count が多い場合、review-loop friction または flaky automation を示す。 | GitHub Actions cancellation や stale same-head check を分類してから比較する必要がある。 |
| `reviewer_comment_count` | 判断前にどれだけ review discussion が必要だったか。 | PR review bodies、inline comments、unresolved/resolved review threads。 | actionable comments と informational comments を分け、decision time の unresolved count を記録する。 | actionable count の低下は evidence 明確化を示す場合がある。一方、comment 増加は risk discovery 改善の可能性もある。 | reviewer/team の comment style に依存するため単独quality metricにしない。 |
| `time_to_merge` | review-ready state から merge までどれくらいかかったか。 | PR timeline、merge timestamp、review and CI state。 | review-ready timestamp（非draft PRはopen時刻、draft PRはready化時刻）から merge までの分数を測り、可能なら waiting-for-review、waiting-for-CI、fixing-review、blocked segment に分ける。 | segment付きなら adoption / throughput metric として使える。 | queue、reviewer availability、branch protection、release window の影響が大きい。 |

### 4. 既存 artifact への対応

| Metric | Preferred existing artifact | Secondary source | Downstream use |
| --- | --- | --- | --- |
| `review_decision_time` | PR review timeline / PR summary | manual reviewer timing note | dogfooding report、controlled benchmark。 |
| `scope_drift_finding_count` | `boundary-map-summary`, `assurance-summary/v1` review surface | inline review comments | scope drift scenario demo、launch kit。 |
| `missing_evidence_finding_count` | `producer-normalization-summary/v1`, `assurance-summary/v1`, `policy-gate-summary/v1` | PR summary comments | quickstart、review Markdown surface、dogfooding report。 |
| `unresolved_claim_count_before_merge` | `claim-evidence-manifest/v1`, `assurance-summary/v1` | `policy-decision/v1` | high-risk escalation demo、dogfooding report。 |
| `selected_high_risk_claim_count` | `assurance-profile`, `assurance-summary/v1`, PR review Markdown | `policy-gate-summary/v1` | high-risk escalation demo、launch kit。 |
| `policy_gate_false_positive_count` / `policy_gate_false_negative_count` | `policy-gate-summary/v1` + manual annotation | PR comments / follow-up issue | policy tuning、launch risk notes。 |
| `ci_rerun_count` | GitHub check runs / PR maintenance state | local verification notes | dogfooding report の operational friction section。 |
| `reviewer_comment_count` | review thread state | review completeness report | review Markdown surface iteration、dogfooding report。 |
| `time_to_merge` | PR timeline | release notes / merge queue state | adoption proof、launch kit claims。 |

`docs/ci/agent-pr-assurance-metrics.md` と `schema/agentic-metrics.schema.json` の optional `agentPrAssurance` extension は、PR assurance metrics の低レベルな report-only contract です。この product 文書はより広い product-effectiveness vocabulary を定義し、machine-readable report がある場合はそれらの低レベルmetricへ対応付けます。report-only collector の `pnpm run metrics:agent-pr-assurance` は `artifacts/metrics/agent-pr-assurance-metrics.{json,md}` を出力し、この vocabulary を `agentPrAssurance.productMetrics` に保存します。`time_to_merge_minutes` は review-ready timestamp が明示的に利用できる場合だけ収集します。draft PR や review 開始が遅れた PR では PR 作成時刻と review-ready 時刻が一致しないためです。任意入力が不足する場合は、0件と見せかけず `not_collected` / `unknown` のまま扱います。

### 4.1 Req2run adoption-readiness extension

Req2run metrics measure whether a requirement can become runnable, reviewable,
evidence-backed work through the reference flow. They are defined in
`docs/product/REQ2RUN-METRICS.md` and produced locally by
`pnpm run metrics:req2run`. They extend the vocabulary without changing the
claim boundary: the metrics evaluate ae-framework workflow effectiveness, not
agent vendor quality.

| Metric | Preferred existing artifact | Collection boundary | Downstream use |
| --- | --- | --- | --- |
| `time_to_first_runnable_verification_minutes` | requirement/Issue timing, ExecPlan v2, `verify-lite-run-summary`, loop summary | report-only timing from requirement acceptance to first passing runnable verification | onboarding friction, controlled comparison covariate |
| `spec_task_evidence_coverage` | ExecPlan v2 task graph, Spec Kit task import, claim-evidence manifest | required tasks with at least one evidence reference / all required tasks | adoption readiness, dogfooding report template |
| `deterministic_replay_pass_rate` | loop-run summary replay evidence, fixture hashes, validation outputs | passing local replay attempts / all replay attempts | reproducibility and variance-reduction evidence |
| `manual_intervention_count` | operator note, loop summary stop/next-action, Issue or private tracker annotation | count of human interventions before runnable evidence exists | onboarding friction and docs/automation improvement |
| `evidence_review_completeness` | claim-evidence manifest, assurance summary, PR assurance review surface | required evidence items present and reviewed / all required evidence items | PR review readiness and launch-material limitations |

### 5. Collection rules

1. **分母を明示する。** ratio の背後にある PR、claim、finding、comment、check run の件数を必ず記録する。
2. **発見と失敗を分ける。** scope drift / missing evidence finding は、有用な risk 発見を示す場合があり、自動的に product failure ではない。
3. **current と stale CI state を分ける。** 古い head の stale/cancelled check は、分類なしに current regression と数えない。semantic blocking state は `current_required_failure` / `policy_semantic_failure` とし、operational CI recovery note は `stale_cancelled`、`superseded`、`same_head_stale`、`manual_rerun_required` に分ける。後続 rerun が green になっただけでは policy-gate false positive とは扱わず、不要な block だったという maintainer の manual annotation が必要。`ci_rerun_classification_counts` がある場合、これは加算可能な内訳ではなく classification facet として扱う。`same_head_stale` は `stale_cancelled` または `superseded` と重複し得る。
4. **time metric を segment 化する。** queueing、human review、CI、review-fix、merge waiting time を、データがあれば分ける。
5. **summary artifact を先に使う。** raw log より `assurance-summary/v1`、`policy-gate-summary/v1`、`claim-evidence-manifest/v1`、PR review Markdown を優先する。
6. **report-only semantics を維持する。** metric は `risk:high` / `enforce-assurance` の判断材料になり得るが、この文書はどの metric も blocking gate へ昇格しない。

### 6. Public claim rules

Public material、demo、launch note は次を守ります。

- comparable baseline で `review_decision_time` または `time_to_merge` を測っていない限り、review が速くなると断定しない。断定する場合も demo scenario に限定する。
- req2run protocol で comparable baseline を用いて `time_to_first_runnable_verification_minutes` を測っていない限り、要求がより速く runnable になると主張しない。Local fixture output は instrumentation readiness の evidence に限定する。
- comment 減少、unresolved claim 減少、green CI だけで code が safer になったと主張しない。
- これらの metric から agent vendor superiority を主張しない。測っているのは producer output の周辺にある ae-framework assurance plane である。
- 承認なしに repository-sensitive な PR text、reviewer identity、raw timing data を公開しない。
- External pilot では `docs/guides/external-pilot-onboarding.md` に従い、PR ごとの publication status を `approved` / `aggregate only` / `private` / `not approved for publication` として記録する。
- metric が measured / estimated / manually annotated / not yet collected のどれかを明記する。

### 7. 後続作業での再利用方法

| Later surface | Required use of this metric vocabulary |
| --- | --- |
| 15-minute quickstart / local demo | `missing_evidence_finding_count`、`scope_drift_finding_count`、reviewer-surface artifact の小さな deterministic subset を示し、実世界の改善とは主張しない。 |
| Req2run local fixture | `docs/product/REQ2RUN-METRICS.md` と `pnpm run metrics:req2run` で live external agent API なしの requirement-to-runnable metric collection を示す。Fixture timing を adoption-speed claim に変換しない。 |
| PR assurance review Markdown | count と unresolved-risk summary に同じ metric 名を使う。 |
| Scope drift / high-risk demo | この metric 名で finding を表示し、report-only と blocking behavior を明確に分ける。 |
| Cross-agent fixtures | producer identity と reviewer-effectiveness metric を分離する。 |
| Dogfooding report | ae-framework PR群で canonical metric を集約し、limitation を記録する。 |
| External pilot onboarding / ACP-097 report | report-only collection から始め、PR ごとの consent / redaction status を保持し、承認済みの aggregate または redacted data だけを公開する。現在の pilot status が必要な場合は `docs/product/PILOT-REPORT-2026Q3-01.md` を参照する。 |
| Controlled comparison protocol | `docs/product/CONTROLLED-COMPARISON-PROTOCOL.md` の baseline、sample category、control、redaction boundary が満たされた場合だけ、`without ae-framework` と `with ae-framework` の review workflow を比較する。 |
| Public launch kit | この vocabulary の measured claim または demo-scoped claim だけを使う。 |
