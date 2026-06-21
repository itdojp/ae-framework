---
docRole: derived
canonicalSource:
- docs/product/EFFECTIVENESS-METRICS.md
- docs/product/AGENT-NEUTRAL-ASSURANCE-ROADMAP.md
- docs/guides/byo-agent-assurance-quickstart.md
- examples/assurance-control-plane/agent-assurance-demo/README.md
- examples/assurance-control-plane/scope-drift-demo/README.md
- examples/assurance-control-plane/high-risk-escalation-demo/README.md
- docs/agents/evidence-adapters.md
lastVerified: '2026-06-21'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency
---

# Dogfooding Report 2026 Q3: Agent-Generated PR Assurance

> Language / 言語: English | 日本語

---

## English

### 1. Executive summary

Between June 20 and June 21, 2026, the ae-framework repository used its own
agent-assurance control-plane work to dogfood the product claim defined in
`docs/product/EFFECTIVENESS-METRICS.md`: reviewer decisions become more
traceable when producer output is converted into reviewable evidence, policy
summaries, and unresolved-risk surfaces.

The observation window covered two related slices:

- **Foundation retrospective:** PR #3503 through PR #3506, closing the previous
  ACP roadmap work and ending with the BYO-agent onboarding guide in PR #3506.
- **ACP-080 adoption/effectiveness series:** PR #3516 through PR #3521, covering
  effectiveness metrics, the offline quickstart/demo, PR review surface renderer,
  scope-drift scenario, high-risk escalation sample, and cross-agent fixture set.

The result is positive but bounded. The repository now has deterministic local
surfaces that expose producer claims, missing evidence, scope drift, selected
high-risk claims, review-thread closure, and policy interpretation without using
live hosted agent APIs. The dogfooding evidence does **not** prove faster review
in a controlled benchmark, does **not** rank agent vendors, and does **not** show
external-repository adoption yet.

### 2. What was dogfooded

| Area | Dogfooded surface | Evidence source | What it showed |
| --- | --- | --- | --- |
| Metrics vocabulary | Canonical metric names and measurement boundaries | `docs/product/EFFECTIVENESS-METRICS.md`, PR #3516 | Product claims can reuse one vocabulary instead of ad hoc adoption claims. |
| Offline quickstart | Fixture-backed BYO-agent assurance demo and reviewer Markdown | `docs/guides/byo-agent-assurance-quickstart.md`, `examples/assurance-control-plane/agent-assurance-demo/`, PR #3517 | A reviewer can inspect summary artifacts before raw logs without a live PR or external LLM call. |
| PR review surface | Reusable renderer for producer, assurance, policy, Boundary Map, claim, and verify-lite artifacts | `scripts/assurance/render-pr-review-surface.mjs`, PR #3518 | Missing artifacts remain visible as `missing` / `not provided`; producer output is not promoted to approval. |
| Scope drift | Normal and high-risk scope-drift scenario surfaces | `examples/assurance-control-plane/scope-drift-demo/`, PR #3519 | The same drift can remain report-only in a normal lane and become blocking when strict assurance is selected. |
| High-risk selected claims | Tenant-isolation high-risk escalation sample | `examples/assurance-control-plane/high-risk-escalation-demo/`, PR #3520 | Selected critical/high claims can demand stronger evidence without forcing heavy lanes on every PR. |
| Cross-agent fixtures | Codex, Claude Code, Copilot, human, CI, and formal producer examples | `fixtures/agents/evidence-adapters/`, PR #3521 | Producers are represented as evidence inputs with common routing, not as approval sources. |

### 3. Observed PR dataset

The table below uses GitHub PR timestamps and `pr-review-completeness` output
collected on June 21, 2026. `time_to_merge` is measured from PR creation / ready
state to merge. It is not a controlled review-speed result because queueing,
automation, and author availability were not isolated.

| PR | Slice | Change type | `time_to_merge` | Review threads | Final unresolved threads | Notes |
| --- | --- | --- | ---: | ---: | ---: | --- |
| #3503 | Assurance escalation lanes | Policy/docs/tests | 28 min | 7 | 0 | Foundation retrospective; high-risk policy behavior, not docs-only. |
| #3504 | Codex Issue task exporter | Script/docs/tests | 22 min | 8 | 0 | Foundation retrospective; Codex CLI issue workflow helper. |
| #3505 | Change-package assurance demo | Demo/tests/docs | 16 min | 0 | 0 | Foundation retrospective; E2E demo with no review threads. |
| #3506 | BYO-agent onboarding guide | Docs-only | 12 min | 1 | 0 | Useful onboarding evidence, but docs-only and therefore limited. |
| #3516 | Effectiveness metrics | Docs-only | 14 min | 7 | 0 | Defined the metric vocabulary reused here. |
| #3517 | 15-minute quickstart / local demo | Demo/docs/tests | 27 min | 3 | 0 | Showed offline fixture-backed review flow. |
| #3518 | PR review surface renderer | Script/demo/docs/tests | 21 min | 5 | 0 | Made reviewer-first Markdown reusable. |
| #3519 | Scope drift scenario pack | Demo/fixtures/docs/tests | 22 min | 2 | 0 | Added normal vs strict-lane scope drift behavior. |
| #3520 | High-risk escalation sample | Demo/fixtures/docs/tests | 27 min | 3 | 0 | Added selected critical/high claim escalation. |
| #3521 | Cross-agent producer fixtures | Fixtures/docs/tests | 13 min | 2 | 0 | Added CI/formal fixtures and per-producer READMEs. |

For the ACP-080 series (#3516-#3521), the observed review-thread count was 22
threads and the final unresolved thread count before merge was 0 for every PR.
This supports the claim that review feedback can be tracked to closure. It does
not prove that fewer comments are better; some comments represented useful risk
discovery.

### 4. Metric observations

| Metric | Observed value in this dogfood | Evidence source | What helped reviewers | Limitation |
| --- | --- | --- | --- | --- |
| `review_decision_time` | Not measured for a human decision. | No tagged human `APPROVED` / `CHANGES_REQUESTED` timing note was collected. | The review surface made the decision inputs clearer, but the decision timestamp was not isolated. | Do not claim faster human decisions from this dataset. |
| `time_to_merge` | ACP-080 PRs ranged from 13 to 27 minutes; mean was about 21 minutes. | GitHub PR created/merged timestamps for #3516-#3521. | Segmented evidence in PR bodies and deterministic local verification made merge readiness auditable. | Queueing, automation, PR size, and author availability dominate this number. |
| `reviewer_comment_count` | ACP-080 PRs had 22 review threads total; all were resolved before merge. | `pr-review-completeness` for #3516-#3521. | Inline threads mapped to concrete files, fixes, replies, and resolved state. | Review style varies. More comments can mean better risk discovery, not worse quality. |
| `scope_drift_finding_count` | Scope-drift demo fixture has 2 Boundary Map findings. Normal lane is report-only; strict high-risk lane blocks. | `examples/assurance-control-plane/scope-drift-demo/expected/boundary-map-summary.json` and policy summaries. | Reviewers can see when a producer changed a file outside the declared Issue / Boundary Map scope. | Fixture evidence only; real PRs still need live boundary coverage and reviewer disposition. |
| `missing_evidence_finding_count` | Codex change-package demo records 2 missing-evidence findings; scope-drift demo records 2; high-risk sample records 4 missing-evidence findings. CI/formal cross-agent summaries record 0 missing-evidence findings but 2 known gaps each. | Producer-normalization summaries under `examples/assurance-control-plane/**/expected/` and `fixtures/agents/producer-normalization-summary.{ci,formal}.json`. | Missing evidence remains report-only until a stricter lane selects it; reviewers can prioritize unsupported claims. | Counts are fixture-specific and not normalized by PR size or claim count. |
| `unresolved_claim_count_before_merge` | Not measured as a live PR claim count. High-risk fixture intentionally shows 2 selected claims: 1 partial critical claim and 1 waived high claim. | `examples/assurance-control-plane/high-risk-escalation-demo/expected/claim-evidence-manifest.json`. | The fixture separates partial evidence from waiver metadata and strict-lane blocking. | Live PRs need stable claim extraction before this can be compared. |
| `selected_high_risk_claim_count` | High-risk escalation profile selects 2 claims: 1 critical and 1 high. | `examples/assurance-control-plane/high-risk-escalation-demo/assurance-profile.json`. | Escalation is explicit and scoped; it is not inferred from producer confidence. | The denominator and domain risk must be stated before comparing counts. |
| `policy_gate_false_positive_count` | 0 manually classified false positives in this report. | PR comments, policy summaries, and merge records. | Operational failures were tracked separately from policy semantics. | A green rerun alone is not counted as a false positive under the metric definition. |
| `policy_gate_false_negative_count` | Not observed, but not proven to be 0. | No post-merge incident or policy-relevant miss was collected in this window. | The report keeps absence of findings separate from proof of absence. | False negatives are sparse and delayed; this requires follow-up collection. |
| `ci_rerun_count` | Manual notes show stale-check/head-refresh friction across several PRs, including empty-amend head refreshes for #3516-#3520 and a clean merge with one stale cancelled gate on #3521. | Task ledger, PR check rollups, and PR comments. | The process exposed stale same-head gate state as operational friction instead of mixing it with assurance semantics. | Counts were manual and not segmented automatically; launch claims should avoid precision here. |

### 5. Reviewer impact

The strongest dogfooding result is not a speed claim. It is traceability:

1. **Producer output became review input.** Codex, Claude Code, Copilot, human,
   CI, and formal outputs are routed through existing artifact names and do not
   become approvals by themselves.
2. **Missing evidence stayed visible.** The quickstart and high-risk examples
   preserve missing evidence and waiver metadata gaps instead of hiding them in
   raw logs.
3. **Scope drift became inspectable.** The scope-drift pack shows a normal
   report-only path and a strict high-risk blocking path using the same evidence.
4. **Review closure was auditable.** Each dogfooded PR reached
   `pr-review-completeness status=ok` with zero unresolved review threads before
   merge.
5. **Policy interpretation remained separate from producer confidence.** The
   policy summaries and assurance profiles selected lanes by policy/risk inputs,
   not by agent vendor identity.

### 6. Friction and false positives

The dogfood also exposed adoption friction that needs product treatment:

- **Stale / superseded GitHub checks still add operational noise.** Several PRs
  needed reruns or head refreshes after review-thread resolution. PR #3521 ended
  with `mergeStateStatus=CLEAN`, while a stale cancelled Copilot Review Gate run
  remained in the rollup. This is operational CI state, not assurance semantics.
- **Docs-only PRs are weak effectiveness evidence.** PR #3506 and PR #3516 are
  useful onboarding/metric artifacts, but they cannot prove code or policy risk
  reduction by themselves.
- **Manual metric extraction is still required.** This report used GitHub PR
  metadata, review-completeness output, task ledger notes, and fixture JSON. The
  collection path is reproducible but not automated.
- **No controlled baseline exists yet.** The same author/operator drove most PRs,
  so the report cannot isolate product effect from operator familiarity.

### 7. Limitations and residual risk

- No external repository pilot was included.
- No statistical benchmark or randomized baseline was run.
- Human review decision time was not measured independently from automation and
  author activity.
- Fixture demos are representative examples; they are not complete simulations of
  live GitHub, hosted LLM, or formal-tool services.
- Policy gate false negatives require delayed incident or post-review evidence;
  none was collected in this short window.
- The cross-agent fixture set fixes vocabulary and routing, but it does not yet
  provide live fetchers for Codex, Claude Code, Copilot, CI, or formal providers.

### 8. Launch-kit summary paragraph

During internal dogfooding on ae-framework PRs #3516 through #3521, the
agent-neutral assurance control plane converted agent, CI, human, and formal
producer outputs into reviewer-facing artifacts without treating any producer as
an approval authority. The six adoption PRs reached merge with 22 review threads
resolved and zero unresolved review threads at final review-completeness checks.
The demos exposed two scope-drift findings, selected two high-risk claims for
strict escalation, and kept missing evidence / waiver gaps visible rather than
hiding them in raw logs. These results support a public claim about improved
review traceability, not a benchmark claim about faster review or agent vendor
quality.

### 9. Next improvement candidates

1. Add a small metrics collector that writes `agent-pr-assurance-metrics.json`
   from PR timestamps, review-thread state, and final check rollup.
2. Segment `time_to_merge` into waiting-for-review, fixing-review,
   waiting-for-CI, and stale-check recovery.
3. Store final review-completeness output and final required-check summary as a
   durable artifact for dogfooding PRs.
4. Add an external-repository pilot before making adoption-speed claims.
5. Add live adapters only after the fixture vocabulary remains stable across the
   launch-kit review.

---

## 日本語

### 1. 要約

2026年6月20日から2026年6月21日にかけて、ae-framework は自分自身の
agent-assurance control-plane 作業を dogfooding した。確認した中心仮説は、
producer output を reviewable evidence、policy summary、未解決リスク surface
へ変換すると、reviewer の判断根拠を追跡しやすくなる、というものである。

対象は、前段の ACP roadmap retrospective（PR #3503〜#3506）と、ACP-080 の
adoption / effectiveness series（PR #3516〜#3521）である。結果として、live hosted
agent API なしで、producer claim、missing evidence、scope drift、selected
high-risk claim、review-thread closure、policy interpretation を確認できる deterministic
local surface が揃った。

ただし、この結果は controlled benchmark ではない。人間 reviewer の判断時間短縮、
agent vendor 比較、外部 repository adoption はまだ確認していない。

### 2. 確認できたこと

| 領域 | Evidence | 確認内容 |
| --- | --- | --- |
| Metric vocabulary | `docs/product/EFFECTIVENESS-METRICS.md`, PR #3516 | dogfooding / launch kit / quickstart が同じ metric 名を使える。 |
| Offline quickstart | `docs/guides/byo-agent-assurance-quickstart.md`, PR #3517 | live PR や外部 LLM API なしで reviewer-facing Markdown を確認できる。 |
| Review surface | `scripts/assurance/render-pr-review-surface.mjs`, PR #3518 | missing artifact を `missing` / `not provided` として残し、producer output を approval にしない。 |
| Scope drift | `examples/assurance-control-plane/scope-drift-demo/`, PR #3519 | normal lane では report-only、strict lane では block として同じ drift evidence を扱える。 |
| High-risk claims | `examples/assurance-control-plane/high-risk-escalation-demo/`, PR #3520 | 2件の selected claim（critical 1件、high 1件）だけを strict escalation 対象にできる。 |
| Cross-agent fixtures | `fixtures/agents/evidence-adapters/`, PR #3521 | Codex / Claude Code / Copilot / human / CI / formal を approval source ではなく evidence producer として扱える。 |

### 3. 主要な観測値

| Metric | 観測値 | 限界 |
| --- | --- | --- |
| `time_to_merge` | ACP-080 PR #3516〜#3521 は 13〜27分、平均約21分。 | queue、automation、operator availability の影響が大きく、速度改善の因果は主張しない。 |
| `reviewer_comment_count` | ACP-080 PR は合計22 review thread、merge 前 unresolved thread は全PRで0。 | comment 数は reviewer style に依存し、単独の品質指標ではない。 |
| `scope_drift_finding_count` | scope-drift demo は Boundary Map finding 2件。 | fixture の代表例であり、live PR 全体の drift 不在を証明しない。 |
| `missing_evidence_finding_count` | codex change-package demo 2件、scope-drift demo 2件、high-risk sample 4件。CI/formal fixture は missing evidence 0件だが known gap 2件ずつ。 | fixture ごとの count であり、PR size / claim 数で正規化していない。 |
| `selected_high_risk_claim_count` | high-risk escalation profile は 2 claims（critical 1、high 1）を選択。 | count が多いこと自体は良し悪しではない。domain risk と分母が必要。 |
| `policy_gate_false_positive_count` | 手動分類された false positive は0件。 | 後続 rerun で green になっただけでは false positive と数えない。 |
| `policy_gate_false_negative_count` | 観測なし。ただし0件の証明ではない。 | post-merge incident / delayed finding の収集が必要。 |
| `ci_rerun_count` | 複数PRで stale check / head refresh の摩擦を確認。 | 手動記録であり、精密な自動計測ではない。 |

### 4. Reviewer への効果

- Producer output を approval ではなく evidence input として扱えるようになった。
- Missing evidence、waiver metadata gap、scope drift が raw log に埋もれず surface に残る。
- Scope drift と high-risk escalation は、通常 lane と strict lane の差分を同じ vocabulary で示せる。
- PR #3516〜#3521 はすべて `pr-review-completeness status=ok` かつ unresolved thread 0 で merge された。
- Policy interpretation は producer confidence ではなく、risk label / assurance profile / policy input に基づく。

### 5. 残余リスク

- 外部 repository pilot は未実施。
- Controlled baseline / statistical benchmark は未実施。
- Human review decision time は独立計測していない。
- Fixture demo は representative example であり、hosted agent service や live formal tool の完全再現ではない。
- False negative は短期観測では見つかりにくく、後続の defect / incident 収集が必要。

### 6. Launch kit 用 summary

内部 dogfooding では、PR #3516〜#3521 を通じて agent-neutral assurance control
plane が agent、CI、human、formal tool の output を approval ではなく reviewer-facing
evidence に変換できることを確認した。6件の adoption PR は合計22 review thread を
解決し、最終 review-completeness では unresolved thread 0 だった。demo は scope drift
2件、selected high-risk claim 2件、missing evidence / waiver gap を raw log ではなく
review surface に残した。これは review traceability の改善を示す evidence であり、review
speed や agent vendor quality の benchmark ではない。
