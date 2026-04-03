---
docRole: narrative
lastVerified: '2026-04-03'
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
`artifacts/progress/summary.json` は、最新の進捗・品質・トレーサビリティのシグナルを単一の JSON 文書に集約したサマリーアーティファクトです。下流のレポート生成やステータス確認向けのコンパクトなサイドカーとして扱います。

### 生成
```bash
node scripts/progress/aggregate-progress.mjs
# または
pnpm run progress:summary
```

### 既定の入力
- `metrics/project-metrics.json`
- `reports/quality-gates/quality-report-*-latest.json`（優先。存在しない場合は、生成スクリプトが `reports/quality-gates/` 配下の最新 `quality-report-*.json` にフォールバックします）
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

### フェーズ状態の解決順序
フェーズ状態は次の順序で解決されます。
1. `PROGRESS_PHASE_STATE`
2. `AE_PHASE_STATE_FILE`
3. `AE_PHASE_STATE_ROOT` を使った `<root>/.ae/phase-state.json`
4. カレントディレクトリの `.ae/phase-state.json`

### 出力スキーマ
主なキーは次のとおりです。
- `generatedAt`
- `sources` 論理入力キーごとの解決済みファイルパス。ソースが欠損または読み取り不能な場合は `null`
- `progress` フェーズ状態サマリー
- `metrics` TDD とカバレッジの合計値
- `quality` ゲートサマリー
- `traceability` リンクカバレッジサマリー
- `missing` `sources` の値が `null` だったキーの配列

### 運用メモ
- 入力不足や読み取り不能なソースがあっても集約全体は失敗せず、`sources` には `null`、`missing` には対応するキーを記録します。
- 実際に消費されたファイルを確認するときは `sources` を参照し、すべての `sources.<key>` が非 null 文字列だと仮定しないでください。
- フェーズ状態の解決結果が想定と異なる場合は、生成スクリプト自体を疑う前に上書き優先度を確認してください。
