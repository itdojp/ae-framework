---
docRole: derived
canonicalSource:
- docs/quality/pr-summary-tool.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-03-21'
---
# PR Summary Aggregation (One Page)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

PR に 1 ページの品質サマリを集約して表示するための方針です。
- セクション: verify-lite baseline、Discovery Pack、assurance、失敗 GWT、アダプター要約、フォーマル結果、トレース ID
- current main の direct input: `artifacts/summary/combined.json`、`artifacts/verify-lite/verify-lite-run-summary.json`、`coverage/coverage-summary.json` または `artifacts/coverage/coverage-summary.json`、`artifacts/domain/replay.summary.json`、`artifacts/bdd/scenarios.json`、`artifacts/properties/summary.json`、`artifacts/properties/ltl-suggestions.json`、`artifacts/formal/gwt.summary.json`、optional `artifacts/assurance/assurance-summary.json` / `artifacts/quality/quality-scorecard.json` / `artifacts/formal/formal-aggregate.json` / `formal/summary.json` / `artifacts/hermetic-reports/formal/summary.json`
- 出力: `artifacts/summary/PR_SUMMARY.md` を baseline とし、`pr-ci-status-comment.yml` が `harness-health` / `change-package` / `change-package-validation` / `plan-artifact` / `plan-artifact-validation` / `hook-feedback` / `quality-scorecard` を追記

例やフォーマットは以下の英語セクションを参照してください。

最小1行サマリ（例）
```
• CI: ✅ tests 124/124, coverage 84% (≥80), typecov 66% (baseline 65); a11y 96 (≥95), perf 78 (≥75)
```

## English (Detailed)

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
- The renderer writes the baseline block to `artifacts/summary/PR_SUMMARY.md`.
- After that, `pr-ci-status-comment.yml` appends the following Markdown artifacts:
  - `artifacts/ci/harness-health.md`
  - `artifacts/change-package/change-package.md`
  - `artifacts/change-package/change-package-validation.md`
  - `artifacts/plan/plan-artifact.md`
  - `artifacts/plan/plan-artifact-validation.md`
  - `artifacts/agents/hook-feedback.md`
  - `artifacts/downloaded/verify-lite-report/artifacts/quality/quality-scorecard.md`
- These files are downstream workflow inputs, not renderer direct inputs.

### Summary Sections
- Coverage: current renderer prints overall percentage from coverage summary; threshold and delta are recommended follow-up enhancements
- Discovery Pack: mode, reason, orphan counts, compile counts from `verify-lite-run-summary.json.discoveryPack`
- Assurance: satisfied claims, warning claims, warning codes from `artifacts/assurance/assurance-summary.json`
- Failing GWT: short counterexamples with `traceId` references
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
- Failing GWT (1): inv-001 — allocated <= onHand
- Adapters:
  - lighthouse: Perf 78, A11y 96, PWA 55 (warn)
  - playwright: 12/12 passed (ok)
- Formal: fail — see `formal/summary.json`
- Trace IDs: inv-001, inv-002
```

Failure-oriented example:
```
- Coverage: 78% (< 80%) ❌  [-2%]
- Failing GWT (2): inv-001 — allocated <= onHand; inv-007 — nonNegative(onHand)
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

## 日本語（詳細）

### 目的
PR に 1 ページの品質サマリを生成し、機械/人間双方が読みやすい形で可視化します。

### 入力（正規化アーティファクト）
- `artifacts/summary/combined.json`（current renderer は adapters / formal / properties / bdd を primary に参照。`propertyDesign` は直接は使わず、LTL は別ファイルを参照）
- `artifacts/verify-lite/verify-lite-run-summary.json`（baseline）
- `coverage/coverage-summary.json`
- `artifacts/domain/replay.summary.json`
- `artifacts/bdd/scenarios.json`
- `artifacts/properties/summary.json`
- `artifacts/properties/ltl-suggestions.json`
- `artifacts/formal/gwt.summary.json`
- `artifacts/assurance/assurance-summary.json`（存在する場合）
- `artifacts/quality/quality-scorecard.json`（存在する場合）
- `artifacts/formal/formal-aggregate.json`（存在する場合。aggregate detail 用）
- legacy `formal/summary.json` または `artifacts/hermetic-reports/formal/summary.json`（存在する場合）
- workflow append stage:
  - `artifacts/ci/harness-health.md`
  - `artifacts/change-package/change-package.md`
  - `artifacts/change-package/change-package-validation.md`
  - `artifacts/plan/plan-artifact.md`
  - `artifacts/plan/plan-artifact-validation.md`
  - `artifacts/agents/hook-feedback.md`
  - `artifacts/downloaded/verify-lite-report/artifacts/quality/quality-scorecard.md`

### 出力（例）
短いダイジェスト:
```
Quality: 82% (>=80) ✅ [+1%] | Formal: pass | Adapters: lighthouse(warn), playwright(ok) | GWT: 0 | Trace: inv-001, inv-002
```

詳細:
```
## 品質サマリ
- カバレッジ: 82% (>= 80%) ✅ [+1%]
- 保証: 適合=1/1, 警告claim=0, 警告=0
- 失敗 GWT: なし
- アダプター:
  - lighthouse: Perf 78, A11y 96, PWA 55 (warn)
  - playwright: 12/12 passed (ok)
- フォーマル: pass
- Trace IDs: inv-001, inv-002
```

### 実装ノート
- 中核は薄く保ち、CI もしくはリリーススクリプト側で集約。
- current renderer 自体はスキーマ検証を実行しません。JSON 検証は upstream CI / producer 側で担保する前提です。
- Discovery Pack 行は top-level `discoveryPack` から生成します。`steps.discoveryPackValidation` / `steps.discoveryPackCompile` は verify-lite summary 側の実行記録であり、renderer の直接入力ではありません。
- current renderer の formal fallback order は `combined.json.formal` → legacy `formal/summary.json` → `artifacts/hermetic-reports/formal/summary.json` です。`artifacts/formal/formal-aggregate.json` は aggregate detail の補助入力です。
- Formal Summary v1/v2 は renderer の直接入力ではなく、上流 producer / validator 契約として別管理します。

### 検証とエラー方針
- current renderer は unreadable な optional JSON を欠損入力として扱い、残りの入力で継続します
- upstream CI / producer 側では入力アーティファクトをスキーマ検証（ajv など）に通す
- 推奨ポリシーとして、エラーは「ファイル/キー/traceId」を含めて短く出力し、不正データは要約に含めない
- 代表コマンド:
  ```bash
  npx ajv -s docs/schemas/artifacts-adapter-summary.schema.json \
    -d artifacts/*/summary.json --strict=false
  ```
- `artifacts/ci/policy-gate-summary.json`、`artifacts/agents/hook-feedback.md`、`artifacts/ci/harness-health.md` は renderer の direct input ではなく、workflow append stage または下流 consumer 用の artifact です。

### PR コメント構成（推奨）
- 1行ダイジェスト（Coverage/Formal/Adapters/GWT/Trace）
- 詳細ブロック（見出し `## Quality Summary`、各セクションの箇条書き）
- 追記（ある場合）: Replay 行、エラー明細（短く・リンク付き）

#### エラー出力テンプレ（短文）
```
❌ adapter: invalid data at artifacts/lighthouse/summary.json (key=status, traceId=inv-001)
```

### 出力整形ルール（推奨）
- 以下は推奨整形であり、current renderer が完全に強制しているわけではありません
- パーセントは整数に丸め（四捨五入）
- しきい値比較は `>=` を明記（記号と色分けは最小限）
- アイコンは ✅/❌/⚠️ を優先（読みやすさ優先）
- 数値は固定小数点 1 桁以内に制限（騒がしさ低減）

#### サンプル（整形適用後）
```
Quality: 83% (>=80) ✅ [+1%] | Formal: pass | Adapters: lighthouse(warn), playwright(ok) | GWT: 0 | Trace: inv-001, inv-002
```

#### 整形 Before/After
```
# Before（冗長・小数多用）
Coverage: 82.374% (>= 80.000%) | Perf: 78.443 | A11y: 96.221

# After（丸め・最小記号）
Coverage: 82% (>=80) | Perf: 78 | A11y: 96
```

#### Formal/Adapters の短文化（例）
```
Formal: pass | Adapters: lighthouse(warn: Perf 78, A11y 96), playwright(ok)
```

#### 表示ポリシー（Formal/Adapters）
- 閾値比較は `>=` のみ明示し、色・アイコンは最小（✅/❌/⚠️）
- 長文は避け、`name(status: short)` 形式で簡潔に（必要ならリンクを併記）

#### リンク方針（簡潔）
- 必要に応じて artifacts への相対パスを 1〜2 件だけ添付（多過ぎる列挙は避ける）
- 例: `formal/summary.json` / `artifacts/summary/combined.json`

#### リンク例（Short）
```
Formal: pass — formal/summary.json
Integration: see artifacts/integration/summary.json
```

#### 閾値表示の例
```
Coverage: 83% (>=80) ✅ | Perf: 78 (>=75) ✅ | A11y: 94 (>=95) ❌
```

#### Formal/Adapters の例（1行）
```
Formal: pass | Adapters: lighthouse(warn: Perf 78, A11y 96), playwright(ok)
```
