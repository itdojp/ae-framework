---
docRole: narrative
lastVerified: '2026-03-31'
---
# Progress Summary (`artifacts/progress/summary.json`)

> 🌍 Language / 言語: English | 日本語

---

## English

### Purpose
`artifacts/progress/summary.json` aggregates the latest progress, quality, and traceability signals into a single JSON document. Use it as a compact status sidecar for downstream reporting and status inspection.

### Generate
```bash
node scripts/progress/aggregate-progress.mjs
# or
pnpm run progress:summary
```

### Default inputs
- `metrics/project-metrics.json`
- `reports/quality-gates/quality-report-*-latest.json` (preferred; if none exist, the generator falls back to the most recent `quality-report-*.json` under `reports/quality-gates/`)
- `traceability.json`
- `.ae/phase-state.json`

### Output
- `artifacts/progress/summary.json`

### Environment overrides
- `PROGRESS_METRICS`
- `PROGRESS_QUALITY`
- `PROGRESS_TRACEABILITY`
- `PROGRESS_PHASE_STATE`
- `PROGRESS_SUMMARY_OUTPUT`

### Phase state resolution order
Phase state resolution checks the following sources in order:
1. `PROGRESS_PHASE_STATE`
2. `AE_PHASE_STATE_FILE`
3. `AE_PHASE_STATE_ROOT` with `<root>/.ae/phase-state.json`
4. `.ae/phase-state.json` in the current working directory

### Output shape
High-level keys:
- `generatedAt`
- `sources` map of logical input keys to resolved file paths or `null` when the source is missing or unreadable
- `progress` phase state summary
- `metrics` TDD and coverage totals
- `quality` gate summary
- `traceability` link coverage summary
- `missing` array of keys from `sources` whose value is `null`

### Operational notes
- Missing or unreadable inputs are represented as `null` in `sources` and surfaced as the corresponding keys in `missing` instead of failing the whole aggregation path.
- Use the `sources` object to confirm which resolved files were actually consumed, and do not assume that every `sources.<key>` value is a non-null string.
- When phase state resolution looks inconsistent, verify the override precedence before debugging the generator itself.

## 日本語

### 目的
`artifacts/progress/summary.json` は、最新の progress、quality、traceability の signal を単一の JSON 文書に集約するための summary artifact です。下流の reporting や status inspection 向けの compact な sidecar として扱います。

### 生成
```bash
node scripts/progress/aggregate-progress.mjs
# または
pnpm run progress:summary
```

### 既定の入力
- `metrics/project-metrics.json`
- `reports/quality-gates/quality-report-*-latest.json`（優先。存在しない場合は、generator が `reports/quality-gates/` 配下の最新 `quality-report-*.json` に fallback します）
- `traceability.json`
- `.ae/phase-state.json`

### 出力
- `artifacts/progress/summary.json`

### 環境変数による上書き
- `PROGRESS_METRICS`
- `PROGRESS_QUALITY`
- `PROGRESS_TRACEABILITY`
- `PROGRESS_PHASE_STATE`
- `PROGRESS_SUMMARY_OUTPUT`

### Phase state の解決順序
Phase state は次の順序で解決されます。
1. `PROGRESS_PHASE_STATE`
2. `AE_PHASE_STATE_FILE`
3. `AE_PHASE_STATE_ROOT` を使った `<root>/.ae/phase-state.json`
4. current working directory の `.ae/phase-state.json`

### 出力 shape
上位 key は次のとおりです。
- `generatedAt`
- logical input key ごとの resolved file path、または source が missing / unreadable の場合は `null` を持つ `sources`
- phase state summary を持つ `progress`
- TDD と coverage の合計値を持つ `metrics`
- gate summary を持つ `quality`
- link coverage summary を持つ `traceability`
- `sources` の値が `null` だった key を持つ `missing`

### 運用メモ
- 入力不足や unreadable な source があっても集約全体は失敗せず、`sources` には `null`、`missing` には対応する key を記録します。
- 実際に消費された file を確認するときは `sources` を参照し、すべての `sources.<key>` が non-null string だと仮定しないでください。
- phase state の解決結果が想定と異なる場合は、generator 自体を疑う前に override precedence を確認してください。
