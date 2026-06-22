---
docRole: ssot
lastVerified: '2026-06-05'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Agent PR Assurance Metrics

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

Agent PR assurance metrics are report-only indicators for deciding whether an agent-created or agent-reviewed pull request is ready for human trust calibration. They supplement green checks; they do not replace review, branch protection, or policy decisions.

Initial operation is report-only. These metrics must not add new `policy-gate` block conditions unless a later policy explicitly promotes one of them through risk labels, assurance profiles, or critical-core rules.

Primary review surface:
- `artifacts/quality/quality-scorecard.json` for scorecard dimensions.
- `artifacts/agents/agent-pr-assurance-metrics.json` when an agentic metrics producer emits the report-only extension shown in `fixtures/agentic-metrics/agent-pr-assurance-metrics.example.json`.
- `claim-evidence-manifest/v1`, `claim-level-summary/v1`, `policy-decision/v1`, `policy-gate-summary/v1`, and PR summary comments for claim/policy projections.
- Raw logs are supporting evidence only.

### 2. Metrics

| Metric | Meaning | Primary input artifacts | Calculation guidance | Initial action |
| --- | --- | --- | --- | --- |
| `claim_coverage` | Share of changed or PR-relevant claims that have at least one linked evidence item. | `claim-evidence-manifest/v1`, `claim-level-summary/v1`, optional `change-package/v2` claim list | `claims_with_evidence / relevant_claims`; exclude `not-applicable` claims and keep denominator explicit. | Report percentage and denominator. |
| `unresolved_claim_count` | Count of claims with missing, stale, failed, or not-yet-judged evidence. | `claim-evidence-manifest/v1`, `claim-level-summary/v1`, `policy-decision/v1` | Count primary claim states of `unresolved` plus projection failures that still need evidence. | Show count; block only if existing policy already escalates the claim. |
| `waiver_count` | Number of active waivers used in the PR decision package. | `claim-evidence-manifest/v1`, `temporary-override/v1`, `policy-decision/v1`, `policy-gate-summary/v1` | Count waivers with owner/reason/expiry/affected claim/evidence link and active status. | Report count and link to waiver artifacts. |
| `waiver_expiry_risk` | Waivers that are expired or close to expiry. | Same waiver artifacts as `waiver_count` | Count expired waivers plus waivers within the configured expiry window; default observation window is 14 days unless policy says otherwise. | Report as warning; existing waiver policy handles blocking when applicable. |
| `required_lane_compliance` | Ratio of required validation lanes satisfied for the active risk/profile. | assurance profile, `policy-decision/v1`, `claim-evidence-manifest/v1`, `quality-scorecard/v1` | `required_lanes_satisfied / required_lanes`; keep absent requirements as `n/a`, represented as `required=0`, `ratio=null`, and `notApplicable=true` in `agentPrAssurance`. | Report compliance and missing lanes. |
| `evidence_completeness` | Presence ratio for required summary artifacts. | verify-lite summary, report envelope, quality scorecard, policy decision, claim evidence manifest, optional assurance/formal summaries | `present_required_summary_artifacts / required_summary_artifacts`; use Contract Catalog paths as the source of truth. | Report percentage and missing artifact names. |
| `agent_regression_signal` | Whether the agent-created PR introduced test/gate regression during its review loop. | GitHub checks, `verify-lite-run-summary`, `harness-health`, heavy-test trend summaries, review-gate history | Count or flag failed gate/test states on the PR head sequence; distinguish stale/superseded failures from current failures. | Report current/stale counts separately. |
| `blocked_to_merge_eligible_mttr` | Time from first blocked state to merge-eligible state. | PR state timeline, `policy-gate-summary`, automation observability reports | Measure from first `blocked`/failed-required-check observation to `mergeStateStatus=CLEAN` or equivalent merge-eligible state. | Trend metric; do not block a PR by itself. |
| `false_block_rate` | Rate of blocks later judged unnecessary. | manual annotation, automation observability reports, PR comments, policy-decision notes | Initially manual: `false_blocks / total_blocks` for a defined observation window. | Report-only until the annotation taxonomy is stable. |

Semantic validation uses a tolerance of `0.0001` for rounded ratio values. Count-based ratios must keep the numerator less than or equal to the denominator. When `claim_coverage.denominator` or `evidence_completeness.required` is `0`, the corresponding numerator must also be `0` and `ratio` is represented as `1` to mean there were no required items left uncovered. `required_lane_compliance` uses a stricter not-applicable representation: `required=0`, `satisfied=0`, `ratio=null`, and `notApplicable=true`. `false_block_rate.totalBlocks=0` has no meaningful percentage, so the metric uses `ratio=null`; if `annotatedFalseBlocks` is `null`, `annotationRequired=true` records that manual classification is still missing.

`required_lane_compliance.notApplicable` is a metric-level denominator state. It is not a claim-level assurance status. Producers must not emit `not-applicable` as a primary claim state unless the claim-level schema and migration policy explicitly allow it.

`agent_regression_signal.regressed` is producer-supplied rather than derived solely from `currentFailures` and `staleOrSupersededFailures`. Producers may incorporate trend history or external check classifications not represented by the two count fields, so the contract validates the shape and records the counts separately without over-constraining the flag.

### 3. Connection to existing artifacts

`quality-scorecard/v1` is the preferred aggregation surface when the metric can be expressed as one of its current dimensions:

- `assuranceCoverage`: `claim_coverage`, `unresolved_claim_count`, `waiver_count`, `waiver_expiry_risk`, and `required_lane_compliance`.
- `artifactIntegrity`: `evidence_completeness`.
- `executionHealth`: `agent_regression_signal`.
- `policyReadiness`: waiver validity and policy-decision readiness.
- `performanceRegression`: heavy-test or benchmark regressions when they are part of the PR evidence.

`agentic-metrics` remains the lightweight agent-observability envelope. The optional report-only extension key is `agentPrAssurance`, validated by `schema/agentic-metrics.schema.json`. It can carry the metric values without changing `quality-scorecard/v1`, requiring every PR to produce `artifacts/agents/agent-pr-assurance-metrics.json`, or blocking CI.

### 4. Metrics collector

`pnpm run metrics:agent-pr-assurance` runs `scripts/metrics/collect-agent-pr-assurance-metrics.mjs`. The collector writes a report-only JSON/Markdown pair, defaulting to:

- `artifacts/metrics/agent-pr-assurance-metrics.json`
- `artifacts/metrics/agent-pr-assurance-metrics.md`

The collector has two modes:

1. **Offline fixture mode**: `--fixture <path>` reads deterministic PR/check data and optional local artifact paths without calling GitHub. Use this mode for tests, docs, and pilot dry runs.
2. **Live GitHub mode**: `--repo <owner/repo> --pr <number>` uses read-only `gh pr view` to collect PR timestamps and check rollup state. Optional artifacts such as `--review-completeness-json`, `--producer-summary`, `--boundary-map-summary`, `--assurance-profile`, `--claim-evidence-manifest`, and `--policy-gate-summary` enrich the report. `time_to_merge_minutes` is measured from review-ready state to merge only when a review-ready timestamp is explicitly available through fixture `pullRequest.reviewReadyAt` or `--review-ready-at`; live mode does not infer it from PR creation time.

The collector adds `agentPrAssurance.productMetrics` for product-effectiveness vocabulary used by `docs/product/EFFECTIVENESS-METRICS.md`:

- `review_threads_total`
- `review_threads_unresolved_final`
- `required_checks`
- `scope_drift_finding_count`
- `missing_evidence_finding_count`
- `selected_high_risk_claim_count`
- `ci_rerun_count`
- `time_to_merge_minutes`
- `policy_gate_false_positive_count`
- `policy_gate_false_negative_count`

If live mode cannot collect an optional field, the field is emitted as `not_collected` instead of `0`. This also applies to the lower-level `metrics.unresolved_claim_count.count` when evidence artifacts are absent. If the source is ambiguous, use `unknown`. A later green rerun is not enough to classify a policy false positive; false-positive and false-negative counts require manual annotation. Required checks are collapsed by check name and newest timestamp/order, so an older cancelled run can appear as `stale_or_superseded_failure_count` without becoming a current required failure when the latest required check passed.

Privacy boundary: PR titles, URLs, review-thread counts, check statuses, and local artifact paths can be sensitive in external pilots. Redact or omit fields before publication, and prefer offline fixture mode when preparing public examples. The collector does not call external LLM APIs, does not rank agent vendors, and does not add policy-gate blocking rules.

### 5. PR comment shape

Keep PR comments compact. Prefer summary lines and links to summary artifacts instead of raw logs.

```text
Agent PR assurance metrics (report-only):
- claim coverage: 4/5 (80%)
- unresolved claims: 1
- waivers: active=1, expiry risk=0
- required lane compliance: 3/4 (75%)
- evidence completeness: 5/6 (83%)
- agent regression signal: current=0, stale/superseded=1
- blocked -> merge eligible MTTR: 18 min
- false block rate: n/a (manual annotation not available)
```

### 6. Promotion rules

- Baseline: report-only metrics, no new blocking conditions.
- Structured assurance: use the metrics to explain missing evidence and traceability before human review.
- High-assurance critical core: policy may promote missing required lanes, expired waivers, or unresolved high-risk claims to block or manual approval.
- Promotion requires an explicit policy change; a metric definition alone is not enforcement.

### 7. Validation

Use existing validation commands:

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
pnpm run metrics:agent-pr-assurance -- --fixture fixtures/metrics/agent-pr-assurance/offline-input.json
pnpm -s run quality:scorecard:v1
pnpm -s run quality:scorecard:validate
```

`quality:scorecard:v1` requires the current verify-lite summary and report envelope inputs in normal operation. If those artifacts are absent in a local docs-only change, validate the contract fixture path with `pnpm -s run check:schemas` and record why scorecard generation was not run.

---

## 日本語

### 1. 目的

Agent PR assurance metrics は、agent が作成またはreviewした pull request を人間が信頼してよいか判断するための report-only 指標です。green check を補足しますが、review、branch protection、policy decision の代替ではありません。

初期運用は report-only です。risk label、assurance profile、critical core rule による明示的な昇格がない限り、これらの metric は新しい `policy-gate` block 条件を増やしてはいけません。

一次review面:
- scorecard dimension は `artifacts/quality/quality-scorecard.json`。
- agentic metrics producer が report-only extension を出す場合は `artifacts/agents/agent-pr-assurance-metrics.json`。例は `fixtures/agentic-metrics/agent-pr-assurance-metrics.example.json`。
- claim / policy projection は `claim-evidence-manifest/v1`、`claim-level-summary/v1`、`policy-decision/v1`、`policy-gate-summary/v1`、PR summary comment。
- raw log は補助証跡に留めます。

### 2. Metrics

| Metric | 意味 | 主な入力artifact | 計算方針 | 初期アクション |
| --- | --- | --- | --- | --- |
| `claim_coverage` | 変更に関連するclaimのうち、1件以上のevidenceが紐づく割合。 | `claim-evidence-manifest/v1`, `claim-level-summary/v1`, optional `change-package/v2` claim list | `evidence付きclaims / 関連claims`。`not-applicable` は除外し、分母を明示する。 | 割合と分母を表示する。 |
| `unresolved_claim_count` | evidence不足、古い、失敗、未判断のclaim数。 | `claim-evidence-manifest/v1`, `claim-level-summary/v1`, `policy-decision/v1` | primary state `unresolved` と、evidence追加が必要なprojection failureを数える。 | 件数を表示する。既存policyが昇格する場合だけblock。 |
| `waiver_count` | PR判断packageで使われるactive waiver数。 | `claim-evidence-manifest/v1`, `temporary-override/v1`, `policy-decision/v1`, `policy-gate-summary/v1` | owner/reason/expiry/affected claim/evidence link を持つ active waiver を数える。 | 件数とwaiver artifactを表示する。 |
| `waiver_expiry_risk` | 期限切れまたは期限間近のwaiver数。 | `waiver_count` と同じ | expired waiver と、既定14日以内に期限が来る waiver を数える。policyが別期間を定める場合はpolicyを優先する。 | warningとして表示する。blockingは既存waiver policyに従う。 |
| `required_lane_compliance` | risk/profile が要求するvalidation laneの充足率。 | assurance profile, `policy-decision/v1`, `claim-evidence-manifest/v1`, `quality-scorecard/v1` | `満たしたrequired lanes / required lanes`。要求がない場合は0ではなく`n/a`とし、`agentPrAssurance` では `required=0`、`ratio=null`、`notApplicable=true` で表す。 | compliance と missing lane を表示する。 |
| `evidence_completeness` | required summary artifacts の存在率。 | verify-lite summary, report envelope, quality scorecard, policy decision, claim evidence manifest, optional assurance/formal summaries | `存在するrequired summary artifacts / required summary artifacts`。Contract Catalog のpathを基準にする。 | 割合と不足artifact名を表示する。 |
| `agent_regression_signal` | agent-created PR のreview loopで test/gate regression が発生したか。 | GitHub checks, `verify-lite-run-summary`, `harness-health`, heavy-test trend summaries, review-gate history | PR head系列の failed gate/test をflagまたは件数化する。stale/superseded failure と current failureを分ける。 | current/stale counts を分けて表示する。 |
| `blocked_to_merge_eligible_mttr` | blocked から merge eligible に戻るまでの時間。 | PR state timeline, `policy-gate-summary`, automation observability reports | 最初の blocked / failed required check 観測から `mergeStateStatus=CLEAN` 相当までを測る。 | trend metric。単独ではblockしない。 |
| `false_block_rate` | 後で不要と判断されたblockの割合。 | manual annotation, automation observability reports, PR comments, policy-decision notes | 初期はmanual annotationで `false_blocks / total_blocks` を観測期間ごとに計算する。 | annotation taxonomy が安定するまで report-only。 |

Semantic validation は、丸め済み ratio に `0.0001` の許容差を使います。count-based ratio では numerator が denominator 以下でなければなりません。`claim_coverage.denominator` または `evidence_completeness.required` が `0` の場合、対応する numerator も `0` とし、未充足項目が存在しないことを `ratio=1` で表します。`required_lane_compliance` はより厳密な not-applicable 表現を使い、`required=0`、`satisfied=0`、`ratio=null`、`notApplicable=true` とします。`false_block_rate.totalBlocks=0` は有意な割合を持たないため `ratio=null` とし、`annotatedFalseBlocks` が `null` の場合は manual classification が未実施であることを `annotationRequired=true` で記録します。

`required_lane_compliance.notApplicable` は metric-level の denominator state です。claim-level assurance status ではありません。claim-level schema と migration policy が明示的に許可するまで、producer は primary claim state として `not-applicable` を emit してはいけません。

`agent_regression_signal.regressed` は `currentFailures` と `staleOrSupersededFailures` だけから導出する値ではなく、producer-supplied な要約flagです。producer は2つのcount fieldに表れないtrend historyや外部check分類を含められるため、contractはshapeとcountを検証し、flagを過度に制約しません。

### 3. 既存artifactとの接続

`quality-scorecard/v1` は、既存dimensionに自然に表現できるmetricの推奨集約面です。

- `assuranceCoverage`: `claim_coverage`、`unresolved_claim_count`、`waiver_count`、`waiver_expiry_risk`、`required_lane_compliance`。
- `artifactIntegrity`: `evidence_completeness`。
- `executionHealth`: `agent_regression_signal`。
- `policyReadiness`: waiver validity と policy-decision readiness。
- `performanceRegression`: PR evidence に含まれる heavy-test / benchmark regression。

`agentic-metrics` は軽量なagent observability envelopeです。optional な report-only extension key は `agentPrAssurance` とし、`schema/agentic-metrics.schema.json` で検証します。`quality-scorecard/v1`、全PRでの `artifacts/agents/agent-pr-assurance-metrics.json` 生成要件、CI block条件を変えずにmetric値を保持できます。

### 4. Metrics collector

`pnpm run metrics:agent-pr-assurance` は `scripts/metrics/collect-agent-pr-assurance-metrics.mjs` を実行します。既定出力は report-only の JSON / Markdown です。

- `artifacts/metrics/agent-pr-assurance-metrics.json`
- `artifacts/metrics/agent-pr-assurance-metrics.md`

collector は2つのmodeを持ちます。

1. **Offline fixture mode**: `--fixture <path>` で deterministic な PR / check data と任意の local artifact path を読みます。GitHub API は呼びません。test、docs、pilot dry run に使います。
2. **Live GitHub mode**: `--repo <owner/repo> --pr <number>` で read-only の `gh pr view` を使い、PR timestamp と check rollup を収集します。`--review-completeness-json`、`--producer-summary`、`--boundary-map-summary`、`--assurance-profile`、`--claim-evidence-manifest`、`--policy-gate-summary` を指定すると report を補強できます。`time_to_merge_minutes` は、fixture の `pullRequest.reviewReadyAt` または `--review-ready-at` で review-ready timestamp が明示されている場合だけ、review-ready state から merge までを測ります。live mode では PR 作成時刻から推定しません。

collector は `docs/product/EFFECTIVENESS-METRICS.md` の product-effectiveness vocabulary に対応する `agentPrAssurance.productMetrics` を追加します。

- `review_threads_total`
- `review_threads_unresolved_final`
- `required_checks`
- `scope_drift_finding_count`
- `missing_evidence_finding_count`
- `selected_high_risk_claim_count`
- `ci_rerun_count`
- `time_to_merge_minutes`
- `policy_gate_false_positive_count`
- `policy_gate_false_negative_count`

live mode で任意fieldを収集できない場合、`0` と見せかけず `not_collected` として出力します。evidence artifact がない場合、低レベルの `metrics.unresolved_claim_count.count` も同様に `not_collected` とします。source が曖昧な場合は `unknown` を使います。後続rerunで green になっただけでは policy false positive とは分類しません。false positive / false negative count には manual annotation が必要です。Required check は check name と最新timestamp/orderで collapse するため、古い cancelled run は最新 required check が通過している限り current failure ではなく `stale_or_superseded_failure_count` として扱えます。

Privacy boundary: 外部pilotでは PR title、URL、review-thread count、check status、local artifact path が sensitive になり得ます。公開前に redaction または omit を行い、公開例には offline fixture mode を優先します。collector は外部LLM APIを呼ばず、agent vendor ranking を行わず、policy-gate blocking rule を追加しません。

### 5. PR comment 形状

PR comment は短く保ちます。raw log ではなく summary artifact へのリンクと要約行を優先します。

```text
Agent PR assurance metrics (report-only):
- claim coverage: 4/5 (80%)
- unresolved claims: 1
- waivers: active=1, expiry risk=0
- required lane compliance: 3/4 (75%)
- evidence completeness: 5/6 (83%)
- agent regression signal: current=0, stale/superseded=1
- blocked -> merge eligible MTTR: 18 min
- false block rate: n/a (manual annotation not available)
```

### 6. 昇格ルール

- Baseline: report-only metrics。新しいblocking条件は追加しない。
- Structured assurance: human review 前に不足evidenceとtraceabilityを説明するために使う。
- High-assurance critical core: missing required lane、expired waiver、unresolved high-risk claim を block または manual approval へ昇格できる。
- 昇格には明示的なpolicy変更が必要です。metric定義だけではenforcementになりません。

### 7. Validation

既存の検証コマンドを使います。

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
pnpm run metrics:agent-pr-assurance -- --fixture fixtures/metrics/agent-pr-assurance/offline-input.json
pnpm -s run quality:scorecard:v1
pnpm -s run quality:scorecard:validate
```

`quality:scorecard:v1` は通常運用では current verify-lite summary と report envelope input を要求します。ローカルdocs-only変更でartifactが無い場合は、`pnpm -s run check:schemas` でcontract fixtureを検証し、scorecard生成を実行しなかった理由を記録します。
