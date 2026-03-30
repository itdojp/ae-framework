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
- `reports/quality-gates/quality-report-*-latest.json`
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
- `sources` resolved file paths
- `progress` phase state summary
- `metrics` TDD and coverage totals
- `quality` gate summary
- `traceability` link coverage summary
- `missing` unavailable sources

### Operational notes
- Missing inputs are reflected in `missing` instead of failing the whole aggregation path.
- Use the `sources` object to confirm which resolved files were actually consumed.
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
- `reports/quality-gates/quality-report-*-latest.json`
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
- resolved file path を持つ `sources`
- phase state summary を持つ `progress`
- TDD と coverage の合計値を持つ `metrics`
- gate summary を持つ `quality`
- link coverage summary を持つ `traceability`
- 利用できなかった source を持つ `missing`

### 運用メモ
- 入力不足があっても集約全体を失敗させず、`missing` に記録します。
- 実際に消費された file を確認するときは `sources` を参照します。
- phase state の解決結果が想定と異なる場合は、generator 自体を疑う前に override precedence を確認してください。
