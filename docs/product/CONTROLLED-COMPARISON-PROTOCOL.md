---
docRole: derived
canonicalSource:
- docs/product/EFFECTIVENESS-METRICS.md
- docs/product/REQ2RUN-METRICS.md
- docs/product/PILOT-REPORT-2026Q3-01.md
- docs/product/PILOT-RUNBOOK-2026Q3.md
- docs/guides/external-pilot-onboarding.md
lastVerified: '2026-06-23'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency
---

# Controlled Comparison Protocol for ae-assisted PR Review

> Language / 言語: English | 日本語

---

## English

### 1. Status and purpose

This protocol is **protocol-ready, not executed**. It defines how a future
controlled comparison should measure the review workflow around
agent-generated pull requests. It does not run the comparison, recruit
participants, perform statistical analysis, or publish benchmark claims.

The comparison unit is a **PR review task**, not an agent run. The study compares
two review workflows:

- **without ae-framework**: ordinary PR review using the producer output, raw CI
  state, review comments, and repository policy already available to the team;
- **with ae-framework**: the same producer output plus ae-framework review
  surfaces, evidence artifacts, policy summaries, and report-only metrics.

The protocol does **not** rank Codex, Claude Code, GitHub Copilot, or any other
agent vendor. Agent and CI outputs remain evidence producers. Human maintainers
still make the merge, request-changes, defer, or block decision.

This protocol follows the ACP-097 pilot report
(`docs/product/PILOT-REPORT-2026Q3-01.md`), which is currently `dry-run only`.
The pilot package validates the readiness of collection artifacts and redaction
boundaries; it does not provide a controlled baseline. This protocol is the
next step required before any review-speed or decision-quality claim can be
made.

### 2. Comparison arms

| Arm | Review workflow | Inputs shown to reviewer | Decision authority | Claim boundary |
| --- | --- | --- | --- | --- |
| A: `without ae-framework` | Team's ordinary review workflow. | PR diff, producer summary or comments, CI checks, existing branch policy, and normal reviewer discussion. | Human reviewer / maintainer. | Baseline workflow only; do not treat missing ae-framework artifacts as a product failure. |
| B: `with ae-framework` | Ordinary review plus ae-framework assurance surface. | Same producer output as Arm A, plus `producer-normalization-summary/v1`, `assurance-summary/v1`, `claim-evidence-manifest/v1`, `policy-gate-summary/v1`, Boundary Map summary when applicable, and PR review Markdown. | Human reviewer / maintainer. | Measures the review surface and evidence workflow, not raw agent intelligence or autonomous approval. |

Run both arms under the repository's normal branch-protection and merge policy.
Do not add a new blocking gate only for the comparison unless the team already
uses that gate in normal operation.

### 3. Sample task categories

Use a balanced set of PR review tasks so the result is not dominated by one easy
or unusually risky change type.

| Category | Example task shape | Why it is included | Required notes |
| --- | --- | --- | --- |
| docs&#47;fixture | Documentation, fixture, or sample-only change with low execution risk. | Validates that the workflow is lightweight enough for routine changes. | Mark as weak evidence for code-safety claims. |
| `ordinary code` | Normal implementation or test change covered by the repository's usual CI. | Represents day-to-day agent-assisted development. | Record PR size, changed file count, and required checks. |
| `scope-sensitive` | Change where Issue scope, Context Pack, or Boundary Map drift is plausible. | Tests whether review surfaces expose scope drift and boundary mismatch. | Capture `scope_drift_finding_count` and whether findings were resolved. |
| `high-risk selected claim` | Change with explicitly selected `high` / `critical` claims or stricter assurance profile. | Confirms that stronger evidence can be scoped to selected claims. | Record selected claims and whether strict evidence was report-only, manual-approval, or blocking. |

Exclude tasks when consent, redaction, CI stability, or branch-policy changes
would make the two arms incomparable.

### 4. Metrics and collection method

Use the vocabulary from `docs/product/EFFECTIVENESS-METRICS.md`. Values that are
not collected must remain `not_collected` or `unknown`; do not report them as
zero.

| Metric | Role in this protocol | Preferred source | Collection method | Limitation |
| --- | --- | --- | --- | --- |
| `review_decision_time` | Primary review-efficiency metric. | PR timeline, review thread state, PR summary, optional manual timing note. | Measure minutes from review-ready timestamp to first human `APPROVED` / `CHANGES_REQUESTED` review or explicitly tagged maintainer disposition (`merge`, `defer`, `block`). | Queueing, timezone, reviewer availability, and PR size can dominate the value; no causal claim without a controlled baseline. |
| `reviewer_comment_count` | Review-discussion volume and risk-discovery signal. | PR review bodies, inline comments, review-thread state. | Count actionable and informational comments separately before final decision. | Comment style varies; fewer comments are not automatically better. |
| `review_threads_unresolved_final` | Final review-thread closure indicator for the protocol. | `pr-review-completeness` output or equivalent review-thread state. | Record unresolved review-thread count at final decision or merge-readiness snapshot. Treat `unresolved_threads_final` as a prose alias only; machine-readable pilot metrics must use the canonical `agentPrAssurance.productMetrics.review_threads_unresolved_final` key. | This is not the same as `unresolved_claim_count_before_merge`; thread closure does not prove evidence closure. |
| `scope_drift_finding_count` | Scope and boundary-drift discovery metric. | Boundary Map summary, assurance summary, producer-normalization summary, review comments. | Count findings classified as scope drift or boundary mismatch; separate resolved and unresolved findings. | Zero does not prove absence of drift unless the relevant files were covered. |
| `missing_evidence_finding_count` | Unsupported-claim discovery metric. | Producer-normalization summary, assurance summary, claim evidence manifest, policy-gate summary. | Count missing-evidence findings by severity and dedupe identical claim/finding pairs. | Missing evidence may be intentionally report-only for routine changes. |
| `ci_rerun_count` | Operational friction metric. | GitHub check runs, PR maintenance comments, workflow run history. | Count reruns and empty-amend head refreshes; classify stale/superseded recovery separately from code-fix reruns. | Stale GitHub check state must not be mixed with assurance semantics. |
| `policy_gate_false_positive_count` | Policy precision follow-up metric. | Policy-gate summary, PR comments, maintainer annotation. | Count only blocks or failures manually classified as false positives within the observation window. | A later green rerun alone is not a false positive. |
| `policy_gate_false_negative_count` | Policy recall follow-up metric. | Post-review findings, incident notes, maintainer annotation, policy decision history. | Count policy-relevant misses discovered after a pass and classify root cause. | Sparse and delayed; absence of observations is not evidence of zero false negatives. |
| `time_to_first_runnable_verification_minutes` | Req2run adoption-readiness timing metric for requirement-to-runnable tasks. | Req2run metrics report, Issue/spec timing, first passing runnable verification artifact. | Measure minutes from requirement acceptance to first passing runnable verification. Keep synthetic fixture timing separate from live pilot timing. | Do not claim faster requirements-to-run without comparable baseline data and queueing controls. |
| `spec_task_evidence_coverage` | Requirement/task traceability metric for req2run tasks. | ExecPlan v2 task graph, Spec Kit task import, claim-evidence manifest, req2run report. | Required tasks with at least one evidence reference divided by all required tasks. | Evidence existence is not evidence sufficiency. |
| `deterministic_replay_pass_rate` | Local reproducibility metric for req2run tasks. | Loop-run summary replay evidence, fixture hashes, validation output, req2run report. | Passing local replay attempts divided by all replay attempts. | Offline fixture replay is not a live agent benchmark. |
| `manual_intervention_count` | Onboarding friction metric for req2run tasks. | Operator notes, loop summary stop/next-action fields, private tracker annotation. | Count interventions before runnable evidence exists and classify by reason. | Intervention taxonomy must be stable before cross-team comparison. |
| `evidence_review_completeness` | Review-readiness metric for req2run tasks. | Claim-evidence manifest, assurance summary, PR review surface, req2run report. | Required evidence items present and reviewed divided by all required evidence items. | Completeness does not replace approval or prove correctness. |

Optional supporting metrics such as `time_to_merge`,
`unresolved_claim_count_before_merge`, and `selected_high_risk_claim_count` may
be reported when the artifacts exist. Req2run metrics are required only for
requirement-to-runnable comparison tasks. Keep them separate from raw agent
performance or vendor-quality claims.

### 5. Minimum sample size thinking

This document intentionally avoids declaring a universal sample size. The
minimum depends on repository size, PR complexity, reviewer availability, and
the variance observed during the first rehearsal. Use the following progression:

1. **Instrumentation rehearsal**: at least one task from each sample category in
   each arm. This validates collection, redaction, and reviewer instructions
   only. It is not enough for product-effect claims.
2. **Balanced pilot comparison**: repeat each category across multiple PRs and
   reviewers, or use paired/counterbalanced tasks where feasible. Record
   denominators by arm, category, reviewer role, PR size band, and producer.
3. **Statistical claim gate**: before claiming faster review or better decision
   quality, pre-register the analysis window, inclusion/exclusion rules,
   primary metric, minimum per-cell count, and handling of missing values. Do
   not introduce p-values, confidence intervals, or effect-size language after
   looking at an underpowered result.

If the completed sample lacks balanced categories, has one dominant author,
uses one reviewer for almost all tasks, or has mismatched PR size between arms,
publish descriptive findings only.

### 6. Required controls

| Risk | Control |
| --- | --- |
| Selection bias | Predefine eligible PR categories and inclusion/exclusion rules before collecting outcomes. |
| Learning effect | Counterbalance arm order where possible; do not run all `without` tasks before all `with` tasks for the same reviewer. |
| Same author/operator effect | Record author and operator roles; avoid having one operator prepare only one arm. |
| Reviewer availability | Capture review-ready time, reviewer queue time, and disposition time separately when possible. |
| PR size / complexity | Bucket by changed file count, lines changed, risk label, and sample category before comparing. |
| CI flakiness and stale checks | Classify stale, superseded, same-head-stale, and code-fix reruns separately. |
| Reviewer expectation bias | Use the same task description and decision criteria in both arms; do not frame Arm B as the desired outcome. |
| Producer variance | Keep producer identity as a covariate; do not infer agent-vendor performance from the review-workflow comparison. |
| Req2run task comparability | For requirement-to-runnable tasks, freeze requirement size, starting artifacts, allowed reference-flow branch, and replay environment before collecting `time_to_first_runnable_verification_minutes` or replay rates. |
| Branch-policy changes | Freeze required-check and merge-policy assumptions for the observation window or exclude affected PRs. |

### 7. Redaction and publication boundary

Follow `docs/guides/external-pilot-onboarding.md` and the publication status
vocabulary from `docs/product/PILOT-EVIDENCE-TEMPLATE.md`.

- Keep raw PR text, exact timestamps, reviewer identity, private review
  comments, repository identifiers, file paths, and business context private by
  default.
- Publish only maintainer-approved aggregate or redacted data.
- Preserve per-PR publication status: `approved`, `aggregate only`, `private`,
  or `not approved for publication`.
- Use duration buckets or aggregate timing unless exact timestamps are approved.
- Do not quote private reviewer comments unless explicit publication approval is
  recorded.
- Keep any live per-PR tracker private; public docs may contain only templates,
  synthetic examples, or approved redacted case notes.

### 8. Analysis and claim rules

Allowed analysis before a full controlled sample:

- instrumentation readiness;
- whether collection fields were obtainable;
- descriptive counts by arm and category;
- reviewer-feedback themes such as useful, missing, confusing, or noisy.

Forbidden claims without a controlled baseline and approved analysis plan:

- "ae-framework makes review faster";
- "ae-framework improves decision quality" without a defined quality endpoint;
- "ae-framework makes code safer" based only on comments, green CI, or fewer
  unresolved threads;
- "agent vendor X is better than agent vendor Y";
- "the workflow guarantees auto-merge";
- "all PRs are formally proved";
- "external adoption is proven" from a dry-run or synthetic pilot package.

When publishing results, state whether each metric is measured, estimated,
manually annotated, or not collected.

### 9. Abort and exclusion criteria

Abort or exclude a task from comparison if:

- consent or publication status is unresolved;
- the PR cannot be redacted safely;
- required-check configuration changes during the observation window;
- CI is unstable enough that `ci_rerun_count` cannot be classified;
- one arm receives materially different reviewer instructions;
- the ae-framework surface is treated as approval instead of review evidence;
- the task falls outside the declared Issue / Context Pack / Boundary Map scope
  and cannot be categorized as a `scope-sensitive` scenario.

### 10. Handoff from ACP-097 to ACP-098

ACP-097 established a `dry-run only` external pilot report: the runbook,
template, synthetic metrics JSON, and redacted review surface are ready, but no
live external PRs or controlled baseline exist. ACP-098 turns that readiness
work into an experimental protocol. The next valid public statement is that the
team has a consent-safe pilot path and a controlled-comparison design. Actual
review-speed, decision-quality, or policy-precision claims must wait until this
protocol is executed with comparable baseline data.

---

## 日本語

### 1. Status / 目的

この protocol は **protocol-ready, not executed** です。将来、agent-generated
pull request 周辺の review workflow を controlled comparison として測定するための
設計を定義します。この文書では比較の実施、被験者募集、統計解析、benchmark
claim の公開は行いません。

比較単位は **agent run ではなく PR review task** です。比較対象は次の2つの
review workflow です。

- **without ae-framework**: producer output、raw CI state、review comment、
  repository policy を使う通常の PR review。
- **with ae-framework**: 同じ producer output に加えて、ae-framework の review
  surface、evidence artifact、policy summary、report-only metric を使う review。

この protocol は Codex、Claude Code、GitHub Copilot、その他 agent vendor を順位付けしません。
Agent / CI output は evidence producer であり、approval authority ではありません。
Merge、request changes、defer、block の判断は引き続き human maintainer が行います。

この protocol は、現在 `dry-run only` である ACP-097 pilot report
（`docs/product/PILOT-REPORT-2026Q3-01.md`）の次段階です。Pilot package は collection
artifact と redaction boundary の readiness を確認しましたが、controlled baseline はありません。
Review-speed や decision-quality の claim を出す前に、この protocol が必要です。

### 2. 比較アーム

| Arm | Review workflow | Reviewer に見せる input | Decision authority | Claim boundary |
| --- | --- | --- | --- | --- |
| A: `without ae-framework` | team の通常 review workflow。 | PR diff、producer summary/comment、CI check、既存 branch policy、通常の review discussion。 | human reviewer / maintainer。 | baseline workflow のみ。ae-framework artifact がないことを product failure と扱わない。 |
| B: `with ae-framework` | 通常 review に ae-framework assurance surface を追加する。 | Arm A と同じ producer output に加え、`producer-normalization-summary/v1`、`assurance-summary/v1`、`claim-evidence-manifest/v1`、`policy-gate-summary/v1`、必要に応じて Boundary Map summary、PR review Markdown。 | human reviewer / maintainer。 | review surface と evidence workflow を測る。raw agent intelligence や autonomous approval は測らない。 |

両アームは repository の通常の branch protection / merge policy のもとで実行します。
チームが通常運用で使っていない新しい blocking gate を、比較のためだけに追加しません。

### 3. Sample task categories

1つの簡単な変更や特殊な高リスク変更に結果が偏らないよう、PR review task を balanced
に選びます。

| Category | Example task shape | 含める理由 | 必須 notes |
| --- | --- | --- | --- |
| docs&#47;fixture | documentation、fixture、sample-only など実行リスクが低い変更。 | routine change に対して workflow が軽量であることを確認する。 | code-safety claim の evidence としては弱いと明記する。 |
| `ordinary code` | 通常 CI で覆われる implementation / test change。 | 日常的な agent-assisted development を表す。 | PR size、changed file count、required check を記録する。 |
| `scope-sensitive` | Issue scope、Context Pack、Boundary Map の drift が起こり得る変更。 | scope drift / boundary mismatch が review surface に出るかを確認する。 | `scope_drift_finding_count` と finding の resolved / unresolved を記録する。 |
| `high-risk selected claim` | `high` / `critical` claim または stricter assurance profile が明示された変更。 | stronger evidence を selected claim に限定できることを確認する。 | selected claim と、strict evidence が report-only / manual-approval / blocking のどれかを記録する。 |

Consent、redaction、CI stability、branch-policy change により2つの arm が比較不能になる
task は除外します。

### 4. Metrics / collection method

`docs/product/EFFECTIVENESS-METRICS.md` の vocabulary を使います。未収集の値は 0 と
見せず、`not_collected` または `unknown` として残します。

| Metric | この protocol での役割 | Preferred source | Collection method | Limitation |
| --- | --- | --- | --- | --- |
| `review_decision_time` | review 効率の primary metric。 | PR timeline、review thread state、PR summary、optional manual timing note。 | review-ready timestamp から最初の human `APPROVED` / `CHANGES_REQUESTED` review、または `merge` / `defer` / `block` と明示tagされた maintainer disposition までの分数を測る。 | queue、timezone、reviewer availability、PR size の影響が大きい。Controlled baseline なしで因果を主張しない。 |
| `reviewer_comment_count` | review discussion 量と risk discovery の signal。 | PR review body、inline comment、review-thread state。 | final decision 前の actionable comment と informational comment を分けて数える。 | reviewer style に依存し、少ないこと自体が良いとは限らない。 |
| `review_threads_unresolved_final` | protocol 用の最終 review-thread closure indicator。 | `pr-review-completeness` output または同等の review-thread state。 | final decision または merge-readiness snapshot の unresolved review-thread count を記録する。`unresolved_threads_final` は prose alias としてだけ扱い、machine-readable pilot metrics は canonical な `agentPrAssurance.productMetrics.review_threads_unresolved_final` key を使う。 | `unresolved_claim_count_before_merge` とは別物。thread closure は evidence closure の証明ではない。 |
| `scope_drift_finding_count` | scope / boundary drift discovery metric。 | Boundary Map summary、assurance summary、producer-normalization summary、review comment。 | scope drift / boundary mismatch と分類された finding を数え、resolved / unresolved を分ける。 | 関連 file が check coverage に含まれていない場合、0件は drift 不在の証明ではない。 |
| `missing_evidence_finding_count` | unsupported claim discovery metric。 | producer-normalization summary、assurance summary、claim evidence manifest、policy-gate summary。 | severity と source artifact ごとに missing-evidence finding を数え、同一 claim/finding pair は dedupe する。 | routine change では missing evidence が意図的に report-only の場合がある。 |
| `ci_rerun_count` | operational friction metric。 | GitHub check run、PR maintenance comment、workflow run history。 | rerun と empty-amend head refresh を数え、stale/superseded recovery と code-fix rerun を分ける。 | stale GitHub check state を assurance semantics と混同しない。 |
| `policy_gate_false_positive_count` | policy precision follow-up metric。 | policy-gate summary、PR comment、maintainer annotation。 | observation window 内で false positive と手動分類された block/fail decision だけを数える。 | 後続 rerun が green になっただけでは false positive ではない。 |
| `policy_gate_false_negative_count` | policy recall follow-up metric。 | post-review finding、incident note、maintainer annotation、policy decision history。 | pass 後に見つかった policy-relevant miss を数え、root cause を分類する。 | sparse / delayed になりやすい。観測なしは false negative 0 の evidence ではない。 |
| `time_to_first_runnable_verification_minutes` | requirement-to-runnable task の adoption-readiness timing。 | req2run metrics report、Issue/spec timing、最初の passing runnable verification artifact。 | requirement acceptance から最初の passing runnable verification までの分数。synthetic fixture timing と live pilot timing を分ける。 | comparable baseline と queueing control なしに高速化を主張しない。 |
| `spec_task_evidence_coverage` | req2run task の requirement/task traceability。 | ExecPlan v2 task graph、Spec Kit task import、claim-evidence manifest、req2run report。 | evidence reference を持つ required task / 全 required task。 | evidence の存在は十分性を証明しない。 |
| `deterministic_replay_pass_rate` | req2run task の local reproducibility。 | loop-run summary replay evidence、fixture hash、validation output、req2run report。 | passing local replay attempt / 全 replay attempt。 | offline fixture replay は live agent benchmark ではない。 |
| `manual_intervention_count` | req2run task の onboarding friction。 | operator note、loop summary stop/next-action、private tracker annotation。 | runnable evidence 到達前の intervention を理由別に数える。 | taxonomy 安定前に cross-team 比較へ使わない。 |
| `evidence_review_completeness` | req2run task の review-readiness。 | claim-evidence manifest、assurance summary、PR review surface、req2run report。 | present かつ reviewed の required evidence item / 全 required evidence item。 | approval の代替ではなく、正しさの証明でもない。 |

Artifact が存在する場合は `time_to_merge`、`unresolved_claim_count_before_merge`、
`selected_high_risk_claim_count` などの supporting metric も記録できます。Req2run metrics は
requirement-to-runnable comparison task の場合だけ必須です。Raw agent performance /
vendor-quality claim とは分けて扱います。

### 5. Minimum sample size の考え方

この文書は universal な sample size を宣言しません。必要数は repository size、PR
complexity、reviewer availability、最初の rehearsal で観測した分散に依存します。次の
段階で進めます。

1. **Instrumentation rehearsal**: 各 sample category から各 arm に最低1 task を用意する。
   これは collection、redaction、reviewer instruction を検証するだけで、product-effect
   claim には不足です。
2. **Balanced pilot comparison**: 各 category を複数 PR / 複数 reviewer で反復するか、
   可能なら paired / counterbalanced task を使う。Arm、category、reviewer role、PR size
   band、producer ごとの denominator を記録する。
3. **Statistical claim gate**: faster review / better decision quality を主張する前に、
   analysis window、inclusion/exclusion rule、primary metric、minimum per-cell count、missing
   value の扱いを事前登録する。Underpowered な結果を見た後で p-value、confidence
   interval、effect-size language を追加しない。

完了 sample が category balance を欠く、1人の author に偏る、ほぼ1人の reviewer に依存する、
または arm 間の PR size が不一致の場合は、descriptive finding のみ公開します。

### 6. 必須 control

| Risk | Control |
| --- | --- |
| Selection bias | outcome 収集前に eligible PR category と inclusion/exclusion rule を定義する。 |
| Learning effect | 可能なら arm order を counterbalance し、同一 reviewer に対して `without` をすべて先に実施しない。 |
| Same author/operator effect | author / operator role を記録し、片方の arm だけを同一 operator が準備する状態を避ける。 |
| Reviewer availability | 可能なら review-ready time、reviewer queue time、disposition time を分けて記録する。 |
| PR size / complexity | changed file count、lines changed、risk label、sample category で bucket してから比較する。 |
| CI flakiness / stale checks | stale、superseded、same-head-stale、code-fix rerun を分けて分類する。 |
| Reviewer expectation bias | 両 arm で同じ task description と decision criteria を使い、Arm B を期待結果として表現しない。 |
| Producer variance | producer identity は covariate として記録し、review-workflow 比較から agent-vendor performance を推論しない。 |
| Req2run task comparability | requirement-to-runnable task では、requirement size、starting artifact、allowed reference-flow branch、replay environment を collection 前に固定する。 |
| Branch-policy changes | observation window の required-check / merge-policy 前提を固定するか、影響 PR を除外する。 |

### 7. Redaction / publication boundary

`docs/guides/external-pilot-onboarding.md` と `docs/product/PILOT-EVIDENCE-TEMPLATE.md`
の publication status vocabulary に従います。

- raw PR text、exact timestamp、reviewer identity、private review comment、
  repository identifier、file path、business context は既定で private に保持する。
- maintainer が承認した aggregate / redacted data のみ公開する。
- PR別 publication status を `approved`、`aggregate only`、`private`、
  `not approved for publication` として保持する。
- exact timestamp の公開承認がない限り、duration bucket または aggregate timing を使う。
- 明示的な publication approval なしに private reviewer comment を引用しない。
- live per-PR tracker は private に保持し、public docs には template、synthetic example、
  approved redacted case note のみ置く。

### 8. Analysis / claim rules

Full controlled sample 前に許容される analysis は次に限定します。

- instrumentation readiness;
- collection field を取得できたか;
- arm / category ごとの descriptive count;
- useful / missing / confusing / noisy などの reviewer-feedback theme。

Controlled baseline と承認済み analysis plan なしに禁止する claim:

- 「ae-framework により review が速くなる」
- quality endpoint を定義せずに「decision quality が上がる」
- comment、green CI、unresolved thread 減少だけで「code が safer になる」
- 「agent vendor X が agent vendor Y より優れている」
- 「workflow が auto-merge を保証する」
- 「すべての PR が formal proof される」
- dry-run / synthetic pilot package から「external adoption が証明された」

結果公開時は、各 metric が measured、estimated、manually annotated、not collected のどれかを
明示します。

### 9. Abort / exclusion criteria

次の場合は task を比較から abort または exclude します。

- consent または publication status が未解決。
- PR を安全に redact できない。
- observation window 中に required-check configuration が変わった。
- CI が不安定で `ci_rerun_count` を分類できない。
- 片方の arm に materially different reviewer instruction が渡された。
- ae-framework surface が review evidence ではなく approval として扱われた。
- task が declared Issue / Context Pack / Boundary Map scope の外にあり、`scope-sensitive`
  scenario として分類できない。

### 10. ACP-097 から ACP-098 への引き継ぎ

ACP-097 は `dry-run only` external pilot report を整備しました。Runbook、template、
synthetic metrics JSON、redacted review surface は準備済みですが、live external PR と
controlled baseline はありません。ACP-098 は、この readiness を experimental protocol に
変換します。次に公開可能な statement は、consent-safe pilot path と controlled-comparison
design がある、という範囲に限られます。Review-speed、decision-quality、policy-precision の
claim は、この protocol を comparable baseline data で実行するまで保留します。
