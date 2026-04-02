---
docRole: derived
canonicalSource:
- docs/quality/pr-summary-tool.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-04-02'
---
# PR Summary Aggregation (One Page)

> 🌍 Language / 言語: English | 日本語

---

## English

### Overview
- This document defines the current one-page PR summary policy for the renderer and workflow append pipeline.
- Baseline sections include the verify-lite summary, Discovery Pack status, assurance, failing GWT references, adapter summaries, formal status, and trace IDs.
- Current direct inputs are `artifacts/summary/combined.json`, `artifacts/verify-lite/verify-lite-run-summary.json`, `coverage/coverage-summary.json` or `artifacts/coverage/coverage-summary.json`, `artifacts/domain/replay.summary.json`, `artifacts/bdd/scenarios.json`, `artifacts/properties/summary.json`, `artifacts/properties/ltl-suggestions.json`, `artifacts/formal/gwt.summary.json`, and optional `artifacts/assurance/assurance-summary.json`, `artifacts/quality/quality-scorecard.json`, `artifacts/formal/formal-aggregate.json`, legacy `formal/summary.json`, or `artifacts/hermetic-reports/formal/summary.json`.
- The renderer writes the baseline Markdown to `artifacts/summary/PR_SUMMARY.md` and may append report-only detection lines such as `Detected coverage`, `Detected adapters`, and `Adapter shape warnings` when `artifacts/ae/context.json` or related adapter validation artifacts exist. After that, `pr-ci-status-comment.yml` appends `harness-health`, `change-package`, `change-package-validation`, `plan-artifact`, `plan-artifact-validation`, `hook-feedback`, and `quality-scorecard` Markdown artifacts.

Minimal one-line summary example:
```
• CI: ✅ tests 124/124, coverage 84% (≥80), typecov 66% (baseline 65); a11y 96 (≥95), perf 78 (≥75)
```

### Goal
- Provide a concise, machine-and-human friendly one-page PR summary for the current renderer and workflow append pipeline.

### Direct Inputs
- `artifacts/summary/combined.json`
  - Primary normalized sidecar for `adapters`, `formal`, `properties`, and `bdd`.
  - Current renderer does not read `propertyDesign` from this sidecar.
- `artifacts/bdd/scenarios.json`
- `artifacts/properties/summary.json`
- `artifacts/properties/ltl-suggestions.json`
- `artifacts/formal/gwt.summary.json`
- `artifacts/verify-lite/verify-lite-run-summary.json`
  - Baseline execution summary.
  - The Discovery Pack line reads only the top-level `discoveryPack` object from this file.
- `coverage/coverage-summary.json` or `artifacts/coverage/coverage-summary.json`
- `artifacts/domain/replay.summary.json`
- Optional direct inputs:
  - `artifacts/assurance/assurance-summary.json`
  - `artifacts/quality/quality-scorecard.json`
  - `artifacts/formal/formal-aggregate.json`
  - legacy `formal/summary.json`
  - `artifacts/hermetic-reports/formal/summary.json`

### Workflow Append Stage
- The renderer writes the baseline block to `artifacts/summary/PR_SUMMARY.md` and may append report-only detection lines such as `Detected coverage`, `Detected adapters`, and `Adapter shape warnings` when `artifacts/ae/context.json` or related adapter validation artifacts exist.
- After that, `pr-ci-status-comment.yml` appends the following Markdown artifacts:
  - `artifacts/ci/harness-health.md`
  - `artifacts/change-package/change-package.md`
  - `artifacts/change-package/change-package-validation.md`
  - `artifacts/plan/plan-artifact.md`
  - `artifacts/plan/plan-artifact-validation.md`
  - `artifacts/agents/hook-feedback.md`
  - `artifacts/downloaded/verify-lite-report/artifacts/quality/quality-scorecard.md`
- Those workflow-attached Markdown files are downstream workflow inputs, not renderer direct inputs.

### Summary Sections
- Coverage: current renderer prints overall percentage from coverage summary; threshold and delta are recommended follow-up enhancements
- Discovery Pack: mode, reason, orphan counts, compile counts from `verify-lite-run-summary.json.discoveryPack`
- Assurance: satisfied claims, warning claims, warning codes from `artifacts/assurance/assurance-summary.json`
- Failing GWT: short counterexamples derived from `artifacts/formal/gwt.summary.json.items`, using the count and the first `property` or GWT fragment (`traceId` is not currently rendered)
- Adapters: one-line summaries from `artifacts/summary/combined.json`
- Formal: prefer `artifacts/summary/combined.json.formal`, then fallback to legacy `formal/summary.json`, then `artifacts/hermetic-reports/formal/summary.json`
- Trace IDs: filterable trace references for replay / property / failure paths

### Current Renderer Notes
- The renderer currently prints `Coverage: <pct>%` without threshold or delta.
- It treats unreadable or malformed optional JSON as missing input and continues with the remaining artifacts.
- It does not perform JSON schema validation on its own; validation is expected to happen upstream.

### Recommended Output Examples
The examples below describe the recommended human-facing format. They are not a byte-for-byte snapshot of the current renderer output.

Short digest:
```
Quality: 82% (>=80) ✅ [+1%] | Formal: pass | Adapters: lighthouse(warn), playwright(ok) | GWT: 0 | Trace: inv-001, inv-002
```

Detailed block:
```
## Quality Summary
- Coverage: 82% (>= 80%) ✅  [+1%]
- Assurance: satisfied=1/1, warningClaims=0, warnings=0
- Failing GWT (1): allocated <= onHand
- Adapters:
  - lighthouse: Perf 78, A11y 96, PWA 55 (warn)
  - playwright: 12/12 passed (ok)
- Formal: fail — see `formal/summary.json`
- Trace IDs: inv-001, inv-002
```

Failure-oriented example:
```
- Coverage: 78% (< 80%) ❌  [-2%]
- Failing GWT (2): allocated <= onHand; nonNegative(onHand)
- Adapters:
  - lighthouse: Perf 72, A11y 93, PWA 50 (warn)
  - playwright: 10/12 passed (error)
- Formal: fail — see `formal/summary.json`
- Trace IDs: inv-001, inv-007
```

Replay line example:
```
Replay: 12 events (ItemReceived:7, ItemAllocated:5), 0 violations
```

### Implementation Notes
- Keep the renderer core thin and push enrichment into CI append stages or release scripts.
- Prefer aggregating validated artifacts.
- Discovery Pack execution records under `steps.discoveryPackValidation` and `steps.discoveryPackCompile` are operational traces in `verify-lite-run-summary.json`; they are not direct renderer inputs.
- Formal Summary v1/v2 remain upstream producer / validator contracts. They are not direct renderer inputs.
- `artifacts/formal/formal-aggregate.json` is supplementary aggregate detail, not the primary formal status source.

### Current Validation and Error Behavior
- `scripts/summary/render-pr-summary.mjs` does not enforce JSON schema validation.
- When optional JSON cannot be parsed or read, the renderer usually treats that input as missing and continues.
- Operationally, JSON validation is an upstream CI / producer responsibility, not a renderer responsibility.

### Recommended Validation and Error Policy
- Validate input JSON against the relevant schemas before rendering.
- Exclude invalid payloads from the summary instead of degrading the output with partial data.
- Prefer fail-fast messages that include file path, key, and `traceId`.
- Representative command:
  ```bash
  npx ajv -s docs/schemas/artifacts-adapter-summary.schema.json \
    -d artifacts/*/summary.json --strict=false
  ```
- `artifacts/ci/policy-gate-summary.json`, `artifacts/agents/hook-feedback.md`, and `artifacts/ci/harness-health.md` are not direct renderer inputs.

### PR Comment Structure
- One-line digest for Coverage / Formal / Adapters / GWT / Trace
- Detailed block headed by `## Quality Summary`
- Optional append sections for Replay and short error details

Short error template:
```
❌ adapter: invalid data at artifacts/lighthouse/summary.json (key=status, traceId=inv-001)
```

### Formatting Guidelines
The items below are recommended output guidelines. They are not yet fully enforced by the current renderer.
- Prefer rounding percentages to integers.
- Keep threshold comparisons explicit with `>=`.
- Prefer visual markers `✅`, `❌`, and `⚠️`.
- Limit noisy decimals to at most one decimal place.
- Prefer concise adapter formatting such as `name(status: short)`.
- Keep links sparse and point to one or two artifact paths when needed.

Before / after:
```
# Before
Coverage: 82.374% (>= 80.000%) | Perf: 78.443 | A11y: 96.221

# After
Coverage: 82% (>=80) | Perf: 78 | A11y: 96
```

Formal / adapters one-line example:
```
Formal: pass | Adapters: lighthouse(warn: Perf 78, A11y 96), playwright(ok)
```

---

## 日本語

### 概要
- 本ドキュメントは、renderer と workflow append pipeline における current one-page PR summary policy を定義します。
- baseline section には、verify-lite summary、Discovery Pack status、assurance、failing GWT references、adapter summaries、formal status、trace IDs が含まれます。
- 現在の direct input は `artifacts/summary/combined.json`、`artifacts/verify-lite/verify-lite-run-summary.json`、`coverage/coverage-summary.json` または `artifacts/coverage/coverage-summary.json`、`artifacts/domain/replay.summary.json`、`artifacts/bdd/scenarios.json`、`artifacts/properties/summary.json`、`artifacts/properties/ltl-suggestions.json`、`artifacts/formal/gwt.summary.json`、および optional の `artifacts/assurance/assurance-summary.json`、`artifacts/quality/quality-scorecard.json`、`artifacts/formal/formal-aggregate.json`、legacy `formal/summary.json`、`artifacts/hermetic-reports/formal/summary.json` です。
- renderer は baseline Markdown を `artifacts/summary/PR_SUMMARY.md` に書き出し、`artifacts/ae/context.json` や adapter validation artifact が存在する場合は `Detected coverage`、`Detected adapters`、`Adapter shape warnings` のような report-only 検出行を自ら追記します。その後 `pr-ci-status-comment.yml` が `harness-health`、`change-package`、`change-package-validation`、`plan-artifact`、`plan-artifact-validation`、`hook-feedback`、`quality-scorecard` の Markdown artifact を追記します。

最小 1 行サマリ（例）:
```
• CI: ✅ tests 124/124, coverage 84% (≥80), typecov 66% (baseline 65); a11y 96 (≥95), perf 78 (≥75)
```

### 目的
- current renderer と workflow append pipeline に対して、機械にも人にも読みやすい 1 ページの PR summary を提供します。

### 直接入力
- `artifacts/summary/combined.json`
  - `adapters`、`formal`、`properties`、`bdd` の primary normalized sidecar です。
  - current renderer はこの sidecar の `propertyDesign` を直接は読みません。
- `artifacts/bdd/scenarios.json`
- `artifacts/properties/summary.json`
- `artifacts/properties/ltl-suggestions.json`
- `artifacts/formal/gwt.summary.json`
- `artifacts/verify-lite/verify-lite-run-summary.json`
  - baseline execution summary です。
  - Discovery Pack 行は、この file の top-level `discoveryPack` object だけを参照します。
- `coverage/coverage-summary.json` または `artifacts/coverage/coverage-summary.json`
- `artifacts/domain/replay.summary.json`
- optional direct input:
  - `artifacts/assurance/assurance-summary.json`
  - `artifacts/quality/quality-scorecard.json`
  - `artifacts/formal/formal-aggregate.json`
  - legacy `formal/summary.json`
  - `artifacts/hermetic-reports/formal/summary.json`

### Workflow 追記段階
- renderer は baseline block を `artifacts/summary/PR_SUMMARY.md` に書き出し、`artifacts/ae/context.json` や adapter validation artifact が存在する場合は `Detected coverage`、`Detected adapters`、`Adapter shape warnings` のような report-only 検出行を追記します。
- その後 `pr-ci-status-comment.yml` が、以下の Markdown artifact を追記します。
  - `artifacts/ci/harness-health.md`
  - `artifacts/change-package/change-package.md`
  - `artifacts/change-package/change-package-validation.md`
  - `artifacts/plan/plan-artifact.md`
  - `artifacts/plan/plan-artifact-validation.md`
  - `artifacts/agents/hook-feedback.md`
  - `artifacts/downloaded/verify-lite-report/artifacts/quality/quality-scorecard.md`
- これら workflow 側で追記される Markdown artifact は renderer の direct input ではなく、downstream workflow input です。

### サマリセクション
- Coverage: current renderer は coverage summary から overall percentage を出力します。threshold や delta は推奨 follow-up enhancement です。
- Discovery Pack: `verify-lite-run-summary.json.discoveryPack` から mode / reason / orphan counts / compile counts を出力します。
- Assurance: `artifacts/assurance/assurance-summary.json` から satisfied claims / warning claims / warning codes を出力します。
- Failing GWT: `artifacts/formal/gwt.summary.json.items` から件数と先頭の `property` または GWT 断片を使った短い counterexample を出力します（現状 `traceId` は出力しません）。
- Adapters: `artifacts/summary/combined.json` から 1 行 summary を生成します。
- Formal: `artifacts/summary/combined.json.formal` を優先し、fallback として legacy `formal/summary.json`、さらに `artifacts/hermetic-reports/formal/summary.json` を見ます。
- Trace IDs: replay / property / failure path の filter 可能な trace reference を出力します。

### Current renderer の注意点
- current renderer は `Coverage: <pct>%` を出力するだけで、threshold や delta は出しません。
- unreadable または malformed な optional JSON は missing input として扱い、残りの artifact で継続します。
- renderer 自体は JSON schema validation を実行しません。validation は upstream で行う前提です。

### 推奨出力例
以下の例は、推奨される human-facing format を示します。current renderer の byte-for-byte な出力ではありません。

短いダイジェスト:
```
Quality: 82% (>=80) ✅ [+1%] | Formal: pass | Adapters: lighthouse(warn), playwright(ok) | GWT: 0 | Trace: inv-001, inv-002
```

詳細ブロック:
```
## Quality Summary
- Coverage: 82% (>= 80%) ✅  [+1%]
- Assurance: satisfied=1/1, warningClaims=0, warnings=0
- Failing GWT (1): allocated <= onHand
- Adapters:
  - lighthouse: Perf 78, A11y 96, PWA 55 (warn)
  - playwright: 12/12 passed (ok)
- Formal: fail — see `formal/summary.json`
- Trace IDs: inv-001, inv-002
```

失敗寄りの例:
```
- Coverage: 78% (< 80%) ❌  [-2%]
- Failing GWT (2): allocated <= onHand; nonNegative(onHand)
- Adapters:
  - lighthouse: Perf 72, A11y 93, PWA 50 (warn)
  - playwright: 10/12 passed (error)
- Formal: fail — see `formal/summary.json`
- Trace IDs: inv-001, inv-007
```

Replay 行の例:
```
Replay: 12 events (ItemReceived:7, ItemAllocated:5), 0 violations
```

### 実装ノート
- renderer の core は薄く保ち、enrichment は CI append stage または release script 側へ寄せます。
- validated artifact の集約を優先します。
- `steps.discoveryPackValidation` と `steps.discoveryPackCompile` にある Discovery Pack execution record は、`verify-lite-run-summary.json` の operational trace であり、renderer の direct input ではありません。
- Formal Summary v1/v2 は upstream producer / validator contract であり、renderer の direct input ではありません。
- `artifacts/formal/formal-aggregate.json` は補助的な aggregate detail であり、primary formal status source ではありません。

### 現行の validation と error behavior
- `scripts/summary/render-pr-summary.mjs` は JSON schema validation を強制しません。
- optional JSON が parse/read できない場合、renderer は通常その input を missing として扱い、残りの artifact で継続します。
- 運用上、JSON validation は upstream CI / producer の責務です。

### 推奨 validation / error policy
- rendering 前に、関連 schema で input JSON を validation してください。
- invalid payload は partial data として要約に混ぜず、summary から除外してください。
- fail-fast message には file path / key / `traceId` を含めてください。
- 代表コマンド:
  ```bash
  npx ajv -s docs/schemas/artifacts-adapter-summary.schema.json     -d artifacts/*/summary.json --strict=false
  ```
- `artifacts/ci/policy-gate-summary.json`、`artifacts/agents/hook-feedback.md`、`artifacts/ci/harness-health.md` は renderer の direct input ではありません。

### PR comment 構成
- Coverage / Formal / Adapters / GWT / Trace の 1 行ダイジェスト
- `## Quality Summary` を見出しにした詳細 block
- Replay 行や短い error detail の optional append section

短い error template:
```
❌ adapter: invalid data at artifacts/lighthouse/summary.json (key=status, traceId=inv-001)
```

### 出力整形ガイド
以下は推奨出力ガイドであり、current renderer が完全には強制していません。
- percentage は整数丸めを優先します。
- threshold comparison は `>=` を明示します。
- visual marker は `✅`、`❌`、`⚠️` を優先します。
- noisy な小数は 1 桁以内に抑えます。
- adapter 表記は `name(status: short)` のように短く保ちます。
- link は必要最小限にし、必要なら 1〜2 個の artifact path に絞ります。

Before / after:
```
# Before
Coverage: 82.374% (>= 80.000%) | Perf: 78.443 | A11y: 96.221

# After
Coverage: 82% (>=80) | Perf: 78 | A11y: 96
```

Formal / adapters 1 行例:
```
Formal: pass | Adapters: lighthouse(warn: Perf 78, A11y 96), playwright(ok)
```
