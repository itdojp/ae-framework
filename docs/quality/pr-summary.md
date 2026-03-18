---
docRole: derived
canonicalSource:
- docs/quality/pr-summary-tool.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-03-18'
---
# PR Summary Aggregation (One Page)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

PR に 1 ページの品質サマリを集約して表示するための方針です。
- セクション: verify-lite baseline、Discovery Pack、assurance、失敗 GWT、アダプター要約、フォーマル結果、トレース ID
- current main の direct input: `artifacts/summary/combined.json`、`artifacts/verify-lite/verify-lite-run-summary.json`、`coverage/coverage-summary.json` または `artifacts/coverage/coverage-summary.json`、`artifacts/domain/replay.summary.json`、optional `artifacts/assurance/assurance-summary.json` / `artifacts/quality/quality-scorecard.json` / `artifacts/formal/formal-aggregate.json` / `formal/summary.json` / `artifacts/hermetic-reports/formal/summary.json`
- 出力: `artifacts/summary/PR_SUMMARY.md` を baseline とし、`pr-ci-status-comment.yml` が `harness-health` / `change-package` / `plan-artifact` / `hook-feedback` / `quality-scorecard` を追記

例やフォーマットは以下の英語セクションを参照してください。

最小1行サマリ（例）
```
• CI: ✅ tests 124/124, coverage 84% (≥80), typecov 66% (baseline 65); a11y 96 (≥95), perf 78 (≥75)
```

Goal
- Provide a concise, machine-and-human friendly one-page PR summary.

Sections
- Coverage: overall %, threshold, delta
- Discovery Pack: `verify-lite-run-summary.json.discoveryPack` 由来の mode / reason / orphan counts / compile counts
- Assurance: satisfied claims / warning claims / warning codes from `artifacts/assurance/assurance-summary.json`
- Failing GWT: short counterexamples with `traceId` (see `docs/quality/counterexample-gwt.md`)
- Adapters: one-line summaries from `artifacts/summary/combined.json`
- Formal: `artifacts/summary/combined.json.formal` を優先し、fallback として `formal/summary.json` / `artifacts/hermetic-reports/formal/summary.json` / `artifacts/formal/formal-aggregate.json` を表示
- Trace IDs: quick links to filterable runs/tests

Format (example)
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

Artifacts
- Read from normalized JSON artifacts:
  - `artifacts/summary/combined.json` (`adapters`, `formal`, `properties`, `propertyDesign`, `bdd`, `ltlSuggestions`)
  - `artifacts/verify-lite/verify-lite-run-summary.json`
  - `coverage/coverage-summary.json`
  - `artifacts/domain/replay.summary.json`
  - `artifacts/assurance/assurance-summary.json` (optional)
  - `artifacts/quality/quality-scorecard.json` (optional)
  - `artifacts/formal/formal-aggregate.json` (optional)
  - `formal/summary.json` or `artifacts/hermetic-reports/formal/summary.json` (optional fallback)
- Appended after renderer output by workflow:
  - `artifacts/agents/hook-feedback.md`
  - `artifacts/ci/harness-health.md`
  - `artifacts/change-package/change-package.md`
  - `artifacts/plan/plan-artifact.md`

Implementation Notes
- Keep core thin; aggregation can be implemented in CI or release scripts.
- Output single comment body suitable for PR description or bot comment.

## Failure Case Example
- Coverage: 78% (< 80%) ❌  [-2%]
- Failing GWT (2): inv-001 — allocated <= onHand; inv-007 — nonNegative(onHand)
- Adapters:
  - lighthouse: Perf 72, A11y 93, PWA 50 (warn)
  - playwright: 10/12 passed (error)
- Formal: fail — see `formal/summary.json`
- Trace IDs: inv-001, inv-007

### Aggregator Pseudo
```text
type Summary = { coverage:number; failingGwt:string[]; adapters: {name:string; status:string; summary:string}[]; formal:string; traceIds:string[] };
function aggregate(a:Artifacts): Summary { /* read combined.json + verify-lite summary + coverage/replay and optional assurance/quality/hook-feedback/formal fallback inputs */ return {} as any }
```
## Validation Flow
- Validate JSON artifacts against schemas in `docs/schemas/`.
- Aggregate only validated data for PR summary to avoid noise.
- Prefer fail-fast with clear error messages and `traceId` context.

```mermaid
flowchart TD
  A[Collect artifacts] --> B[Validate with schemas]
  B -->|ok| C[Aggregate summary]
  B -->|fail| D[Report errors with traceId]
```
## Summary Output Variants
### Short Digest
```
Quality: 82% (>=80) ✅  [+1%] | Formal: pass | Adapters: lighthouse(warn), playwright(ok) | GWT: 0 | Trace: inv-001, inv-002
```

### Detailed
```
## Quality Summary
- Coverage: 82% (>= 80%) ✅  [+1%]
- Failing GWT: none
- Adapters:
  - lighthouse: Perf 78, A11y 96, PWA 55 (warn)
  - playwright: 12/12 passed (ok)
- Formal: pass
- Trace IDs: inv-001, inv-002
```

## Replay Line (optional)
- Example: `Replay: 12 events (ItemReceived:7, ItemAllocated:5), 0 violations`

---

## 日本語（詳細）

### 目的
PR に 1 ページの品質サマリを生成し、機械/人間双方が読みやすい形で可視化します。

### 入力（正規化アーティファクト）
- `artifacts/summary/combined.json`（adapters / formal / properties / propertyDesign / bdd / ltlSuggestions の集約 sidecar）
- `artifacts/verify-lite/verify-lite-run-summary.json`（baseline）
- `coverage/coverage-summary.json`
- `artifacts/domain/replay.summary.json`
- `artifacts/assurance/assurance-summary.json`（存在する場合）
- `artifacts/quality/quality-scorecard.json`（存在する場合）
- `artifacts/formal/formal-aggregate.json`（存在する場合）
- `formal/summary.json` または `artifacts/hermetic-reports/formal/summary.json`（存在する場合）
- workflow append stage:
  - `artifacts/agents/hook-feedback.md`
  - `artifacts/ci/harness-health.md`
  - `artifacts/change-package/change-package.md`
  - `artifacts/plan/plan-artifact.md`

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
- スキーマ検証（`docs/schemas/`）で不正データを早期に除外。
- Discovery Pack 行は top-level `discoveryPack` から生成します。`steps.discoveryPackValidation` / `steps.discoveryPackCompile` は verify-lite summary 側の実行記録であり、renderer の直接入力ではありません。
- Formal Summary v1/v2 は renderer の直接入力ではなく、上流 producer / validator 契約として別管理します。

### 検証とエラー方針
- 入力アーティファクトは必ずスキーマ検証（ajv など）を通す
- エラーは「ファイル/キー/traceId」を含めて短く出力（過剰ログ回避）
- 不正データは要約に含めない（fail-fast）
- 代表コマンド:
  ```bash
  npx ajv -s docs/schemas/artifacts-adapter-summary.schema.json \
    -d artifacts/*/summary.json --strict=false
  ```

### PR コメント構成（推奨）
- 1行ダイジェスト（Coverage/Formal/Adapters/GWT/Trace）
- 詳細ブロック（見出し `## Quality Summary`、各セクションの箇条書き）
- 追記（ある場合）: Replay 行、エラー明細（短く・リンク付き）

#### エラー出力テンプレ（短文）
```
❌ adapter: invalid data at artifacts/lighthouse/summary.json (key=status, traceId=inv-001)
```

### 出力整形ルール（推奨）
- パーセントは整数に丸め（四捨五入）
- しきい値比較は `>=` を明記（記号と色分けは最小限）
- アイコンは ✅/❌/⚠️ のみに限定（読みやすさ優先）
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
