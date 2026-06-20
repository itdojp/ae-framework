---
docRole: derived
canonicalSource:
- docs/quality/pr-summary-tool.md
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/quality/coverage-required.md
- docs/quality/coverage-policy.md
lastVerified: '2026-05-09'
---
# PR Summary Aggregation (One Page)

> 🌍 Language / 言語: English | 日本語

---

## English

### Overview
- This document defines the current one-page PR summary policy for the renderer and workflow append pipeline.
- Baseline sections include the verify-lite summary, Discovery Pack status, assurance, failing GWT references, adapter summaries, formal status, and trace IDs.
- Current direct inputs are `artifacts/summary/combined.json`, `artifacts/verify-lite/verify-lite-run-summary.json`, `coverage/coverage-summary.json` or `artifacts/coverage/coverage-summary.json`, `artifacts/domain/replay.summary.json`, `artifacts/bdd/scenarios.json`, `artifacts/properties/summary.json`, `artifacts/properties/ltl-suggestions.json`, `artifacts/formal/gwt.summary.json`, and optional `artifacts/assurance/assurance-summary.json`, `artifacts/assurance/claim-evidence-manifest.json`, `artifacts/change-package/change-package-v2.json`, `artifacts/quality/quality-scorecard.json`, canonical formal inputs `artifacts/formal/formal-summary-v2.json` / `artifacts/formal/formal-summary-v1.json`, `artifacts/hermetic-reports/formal/summary.json`, `artifacts/formal/formal-aggregate.json`, or final legacy compatibility input `formal/summary.json`.
- The renderer writes the baseline Markdown to `artifacts/summary/PR_SUMMARY.md` and may append report-only detection lines such as `Detected coverage`, `Detected adapters`, and `Adapter shape warnings` when `artifacts/ae/context.json` or related adapter validation artifacts exist. After that, `pr-ci-status-comment.yml` appends `harness-health`, `change-package`, `change-package-validation`, `plan-artifact`, `plan-artifact-validation`, `hook-feedback`, `quality-scorecard`, and `claim-evidence-manifest` Markdown artifacts.

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
  - `artifacts/assurance/claim-evidence-manifest.json`
  - `artifacts/change-package/change-package-v2.json`
  - `artifacts/quality/quality-scorecard.json`
  - `artifacts/formal/formal-summary-v2.json`
  - `artifacts/formal/formal-summary-v1.json`
  - `artifacts/hermetic-reports/formal/summary.json`
  - `artifacts/formal/formal-aggregate.json`
  - final legacy compatibility input `formal/summary.json`

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
  - `artifacts/downloaded/verify-lite-report/artifacts/assurance/claim-evidence-manifest.md`
- Those workflow-attached Markdown files are downstream workflow inputs, not renderer direct inputs.

### Summary Sections
- Coverage: the current renderer prints only `Coverage: <pct>%` from the coverage summary; `Threshold (effective)`, `Derived`, `Policy`, and `Policy source` belong to the workflow-level coverage comment contract rather than the renderer output contract
- Discovery Pack: mode, reason, orphan counts, compile counts from `verify-lite-run-summary.json.discoveryPack`
- Assurance: satisfied claims, warning claims, warning codes from `artifacts/assurance/assurance-summary.json`
- Claim evidence: per-claim satisfied / partial / waived / unresolved manifest-status counts, missing / waiver reference counts, and separate review-state counts (`behavior/tested`, `model/model-checked`, `proof/proved`, `runtime/runtime-mitigated`) from `artifacts/assurance/claim-evidence-manifest.json`
- Change Package v2: claim-state counts, policy/release-control digest, and optional `contractMigrationNotes[]`. Contract migration notes are displayed only when the v2 artifact provides them; ordinary PRs without assurance contract impact omit the section.
- Failing GWT: short counterexamples derived from `artifacts/formal/gwt.summary.json.items`, using the count and the first `property` or GWT fragment (`traceId` is not currently rendered)
- Adapters: one-line summaries from `artifacts/summary/combined.json`
- Formal: prefer `artifacts/summary/combined.json.formal`, then canonical `artifacts/formal/formal-summary-v2.json`, then `artifacts/formal/formal-summary-v1.json`, then `artifacts/hermetic-reports/formal/summary.json`, including the same paths under `artifacts/downloaded/verify-lite-report/` when the PR Maintenance workflow has downloaded verify-lite evidence before rendering. Legacy compatibility input `formal/summary.json` remains the final fallback. Formal Summary `ok` / `failed` is rendered as PR-summary `pass` / `fail`; hermetic aggregate presence is rendered as `present <n>/<total>` when no pass/fail status exists.
- Trace IDs: filterable trace references for replay / property / failure paths

### Current Renderer Notes
- The renderer currently prints `Coverage: <pct>%` without threshold or delta. `Threshold (effective)`, `Derived`, `Policy`, and `Policy source` are documented in `docs/quality/coverage-required.md` and `docs/quality/coverage-policy.md` as workflow-level coverage comment fields, not renderer direct output fields.
- It treats unreadable or malformed optional JSON as missing input and continues with the remaining artifacts.
- It does not perform JSON schema validation on its own; validation is expected to happen upstream.

### Recommended Output Examples
The examples below describe the recommended human-facing format. They are not a byte-for-byte snapshot of the current renderer output. For authoritative threshold / policy provenance wording, prefer the workflow-level coverage comment contract in `docs/quality/coverage-required.md` and `docs/quality/coverage-policy.md`.

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
- Formal: fail — from `artifacts/formal/formal-summary-v2.json` or `artifacts/hermetic-reports/formal/summary.json`; use `formal/summary.json` only as the final legacy compatibility fallback
- Trace IDs: inv-001, inv-002
```

Failure-oriented example:
```
- Coverage: 78% (< 80%) ❌  [-2%]
- Failing GWT (2): allocated <= onHand; nonNegative(onHand)
- Adapters:
  - lighthouse: Perf 72, A11y 93, PWA 50 (warn)
  - playwright: 10/12 passed (error)
- Formal: fail — from `artifacts/formal/formal-summary-v2.json` or `artifacts/hermetic-reports/formal/summary.json`; use `formal/summary.json` only as the final legacy compatibility fallback
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
- Formal Summary v2/v1 are now direct read-only renderer inputs after `combined.json.formal`; they remain upstream producer / validator contracts and are not schema-validated by the renderer itself.
- `artifacts/formal/formal-aggregate.json` is supplementary aggregate detail, not the primary formal status source.
- The current renderer and workflow inline fallback keep `formal/summary.json` as the final compatibility input after canonical formal-summary and hermetic aggregate paths.
- Contract migration notes come from validated `change-package/v2` data. They are required when a PR changes assurance-facing schemas, canonical routes, policy-gate behavior, or change-package contracts in a compatibility-impacting way; otherwise they should be omitted.

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
- 現在の direct input は `artifacts/summary/combined.json`、`artifacts/verify-lite/verify-lite-run-summary.json`、`coverage/coverage-summary.json` または `artifacts/coverage/coverage-summary.json`、`artifacts/domain/replay.summary.json`、`artifacts/bdd/scenarios.json`、`artifacts/properties/summary.json`、`artifacts/properties/ltl-suggestions.json`、`artifacts/formal/gwt.summary.json`、および optional の `artifacts/assurance/assurance-summary.json`、`artifacts/assurance/claim-evidence-manifest.json`、`artifacts/change-package/change-package-v2.json`、`artifacts/quality/quality-scorecard.json`、正準 formal input の `artifacts/formal/formal-summary-v2.json` / `artifacts/formal/formal-summary-v1.json`、`artifacts/hermetic-reports/formal/summary.json`、`artifacts/formal/formal-aggregate.json`、final legacy compatibility input `formal/summary.json` です。
- renderer は baseline Markdown を `artifacts/summary/PR_SUMMARY.md` に書き出し、`artifacts/ae/context.json` や adapter validation artifact が存在する場合は `Detected coverage`、`Detected adapters`、`Adapter shape warnings` のような report-only 検出行を自ら追記します。その後 `pr-ci-status-comment.yml` が `harness-health`、`change-package`、`change-package-validation`、`plan-artifact`、`plan-artifact-validation`、`hook-feedback`、`quality-scorecard`、`claim-evidence-manifest` の Markdown artifact を追記します。

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
  - `artifacts/assurance/claim-evidence-manifest.json`
  - `artifacts/change-package/change-package-v2.json`
  - `artifacts/quality/quality-scorecard.json`
  - `artifacts/formal/formal-summary-v2.json`
  - `artifacts/formal/formal-summary-v1.json`
  - `artifacts/hermetic-reports/formal/summary.json`
  - `artifacts/formal/formal-aggregate.json`
  - final legacy compatibility input `formal/summary.json`

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
  - `artifacts/downloaded/verify-lite-report/artifacts/assurance/claim-evidence-manifest.md`
- これら workflow 側で追記される Markdown artifact は renderer の direct input ではなく、downstream workflow input です。

### サマリセクション
- Coverage: current renderer は coverage summary から `Coverage: <pct>%` だけを出力します。`Threshold (effective)`、`Derived`、`Policy`、`Policy source` は renderer 出力契約ではなく、workflow 側の coverage comment 契約です。
- Discovery Pack: `verify-lite-run-summary.json.discoveryPack` から mode / reason / orphan counts / compile counts を出力します。
- Assurance: `artifacts/assurance/assurance-summary.json` から satisfied claims / warning claims / warning codes を出力します。
- Claim evidence: `artifacts/assurance/claim-evidence-manifest.json` から claim 単位の satisfied / partial / waived / unresolved という manifest-status 件数、missing / waiver reference 件数、および `behavior/tested`、`model/model-checked`、`proof/proved`、`runtime/runtime-mitigated` の review-state 件数を分離して出力します。
- Change Package v2: claim-state counts、policy / release-control digest、および任意の `contractMigrationNotes[]` を出力します。契約移行注記は v2 artifact が提供する場合だけ表示し、assurance contract 影響のない通常 PR では省略します。
- Failing GWT: `artifacts/formal/gwt.summary.json.items` から件数と先頭の `property` または GWT 断片を使った短い counterexample を出力します（現状 `traceId` は出力しません）。
- Adapters: `artifacts/summary/combined.json` から 1 行 summary を生成します。
- Formal: `artifacts/summary/combined.json.formal` を優先し、次に正準 `artifacts/formal/formal-summary-v2.json`、`artifacts/formal/formal-summary-v1.json`、`artifacts/hermetic-reports/formal/summary.json` を見ます。PR Maintenance workflow が rendering 前に verify-lite evidence を download した場合は、同じ path の `artifacts/downloaded/verify-lite-report/` mirror も参照します。legacy compatibility input の `formal/summary.json` は final fallback です。Formal Summary の `ok` / `failed` は PR summary 上では `pass` / `fail` として表示し、pass/fail status が無い hermetic aggregate は `present <n>/<total>` として表示します。
- Trace IDs: replay / property / failure path の filter 可能な trace reference を出力します。

### Current renderer の注意点
- current renderer は `Coverage: <pct>%` を出力するだけで、threshold や delta は出しません。`Threshold (effective)`、`Derived`、`Policy`、`Policy source` は `docs/quality/coverage-required.md` と `docs/quality/coverage-policy.md` に定義された workflow 側の coverage comment field です。
- unreadable または malformed な optional JSON は missing input として扱い、残りの artifact で継続します。
- renderer 自体は JSON schema validation を実行しません。validation は upstream で行う前提です。

### 推奨出力例
以下の例は、推奨される human-facing format を示します。current renderer の byte-for-byte な出力ではありません。threshold / policy provenance の正準表現は、`docs/quality/coverage-required.md` と `docs/quality/coverage-policy.md` にある workflow 側の coverage comment 契約を優先してください。

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
- Formal: fail — `artifacts/formal/formal-summary-v2.json` または `artifacts/hermetic-reports/formal/summary.json` から表示します。`formal/summary.json` は final legacy compatibility fallback としてのみ使います
- Trace IDs: inv-001, inv-002
```

失敗寄りの例:
```
- Coverage: 78% (< 80%) ❌  [-2%]
- Failing GWT (2): allocated <= onHand; nonNegative(onHand)
- Adapters:
  - lighthouse: Perf 72, A11y 93, PWA 50 (warn)
  - playwright: 10/12 passed (error)
- Formal: fail — `artifacts/formal/formal-summary-v2.json` または `artifacts/hermetic-reports/formal/summary.json` から表示します。`formal/summary.json` は final legacy compatibility fallback としてのみ使います
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
- Formal Summary v2/v1 は `combined.json.formal` の次に参照される renderer の read-only direct input です。upstream producer / validator contract である点は維持し、renderer 自体は schema validation を実行しません。
- `artifacts/formal/formal-aggregate.json` は補助的な aggregate detail であり、primary formal status source ではありません。
- 現行 renderer と workflow inline fallback は、正準 formal-summary と hermetic aggregate の後に `formal/summary.json` を final compatibility input として維持します。
- contract migration note は validation 済みの `change-package/v2` data から取得します。assurance-facing schema、canonical route、policy-gate behavior、change-package contract に互換性影響のある変更を加える PR では必要で、それ以外の通常 PR では省略します。

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
