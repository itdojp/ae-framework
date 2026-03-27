---
docRole: ssot
lastVerified: '2026-03-27'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Heavy Test Trend Visualization PoC

This document collects initial ideas for visualizing archived heavy-test trend history. / このドキュメントは、アーカイブ済みの heavy-test trend 履歴を可視化するための初期案を整理します。

Primary sources / 一次情報:
- history summary: `reports/heavy-test-trends-history/summary.md`
- export script: `scripts/pipelines/export-heavy-trend-history.mjs`
- threshold helper: `scripts/pipelines/recommend-heavy-trend-thresholds.mjs`

> Language / 言語: English | 日本語

---

## English

### 1. Goal

Organize ideas for turning archived heavy-test history (`reports/heavy-test-trends-history/*.json`) into analyst-friendly views for operational review, threshold tuning, and trend investigation.

### 2. CSV / Markdown export script

```bash
pnpm node scripts/pipelines/export-heavy-trend-history.mjs \
  --history-dir reports/heavy-test-trends-history \
  --csv-output reports/heavy-test-trends-history/history.csv \
  --markdown-output reports/heavy-test-trends-history/history.md \
  --markdown-limit 20
```

- `history.csv`: contains `snapshot,label,metric,baseline,current,delta` for every snapshot, intended for Observable or spreadsheet analysis.
- `reports/heavy-test-trends-history/history.md`: emits the latest N entries as a Markdown table that can be pasted into PRs or operational docs.

### 3. Threshold review report generation

```bash
pnpm node scripts/pipelines/recommend-heavy-trend-thresholds.mjs \
  --history-dir reports/heavy-test-trends-history \
  --markdown-output reports/heavy-test-trends-history/threshold-recommendation.md \
  --json-output reports/heavy-test-trends-history/threshold-recommendation.json \
  --min-snapshots 14
```

- `reports/heavy-test-trends-history/threshold-recommendation.md`: compares current thresholds against recommended Warning / Critical values.
- `reports/heavy-test-trends-history/threshold-recommendation.json`: machine-readable threshold recommendations, including sample count and quantile settings.
- Treat workflow threshold updates as blocked until the report reaches `Status: ready`.

### 4. Markdown preview example

| Snapshot | Label | Metric | Baseline | Current | Δ |
| --- | --- | --- | --- | --- | --- |
| ... | ... | ... | ... | ... | ... |

### 5. Observable Notebook example

1. Upload `history.csv` as a `FileAttachment` in the notebook.
2. Use the following example to draw the Mutation score trend.

```text
viewof metric = Inputs.select([...new Set(data.map(d => d.metric))], {value: "mutationScore"})
filtered = data.filter(d => d.metric === metric && d.label === "Mutation quick")
Plot.plot({
  marginLeft: 80,
  x: {label: "Snapshot", tickRotate: -45},
  y: {label: "Current"},
  marks: [
    Plot.ruleY([98], {stroke: "orange", strokeDash: "4,2"}),
    Plot.ruleY([96], {stroke: "red", strokeDash: "4,2"}),
    Plot.line(filtered, {x: "snapshot", y: "current", stroke: "steelblue", marker: true})
  ]
})
```

3. If you need a heatmap for `delta`, use `Plot.rectY` and color critical thresholds separately.

### 6. Candidate next steps

- Link Slack notifications or issue alerts directly to the corresponding snapshot location in the notebook.
- Import `history.csv` into Grafana or a similar BI tool and build a dashboard.
- Connect the visualization result with automated comments when deltas keep degrading across consecutive snapshots.

## 日本語

### 1. 目的

heavy-test トレンドの履歴 (`reports/heavy-test-trends-history/*.json`) を整形して可視化し、運用レビュー、しきい値調整、傾向調査に使うための初期案をまとめる。

### 2. CSV / Markdown 生成スクリプト
```bash
pnpm node scripts/pipelines/export-heavy-trend-history.mjs \
  --history-dir reports/heavy-test-trends-history \
  --csv-output reports/heavy-test-trends-history/history.csv \
  --markdown-output reports/heavy-test-trends-history/history.md \
  --markdown-limit 20
```
- `history.csv`: 全スナップショットの `snapshot,label,metric,baseline,current,delta` を含む。Observable や Excel での分析に利用する。
- `reports/heavy-test-trends-history/history.md`: 直近 N 件を Markdown テーブルで出力し、PR や運用ドキュメントに貼り付けられる。

### 3. 閾値見直しレポート生成
```bash
pnpm node scripts/pipelines/recommend-heavy-trend-thresholds.mjs \
  --history-dir reports/heavy-test-trends-history \
  --markdown-output reports/heavy-test-trends-history/threshold-recommendation.md \
  --json-output reports/heavy-test-trends-history/threshold-recommendation.json \
  --min-snapshots 14
```
- `reports/heavy-test-trends-history/threshold-recommendation.md`: 現在の閾値と提案値（Warning / Critical）を比較するレポート。
- `reports/heavy-test-trends-history/threshold-recommendation.json`: 閾値提案の機械可読データ（サンプル数・quantile 設定含む）。
- `Status: ready` になるまでは、workflow 閾値の更新を保留する。

### 4. Markdown プレビュー例
| Snapshot | Label | Metric | Baseline | Current | Δ |
| --- | --- | --- | --- | --- | --- |
| ... | ... | ... | ... | ... | ... |

### 5. Observable Notebook での活用例
1. `history.csv` を `FileAttachment` として Notebook にアップロードする。
2. 以下のコードで Mutation score のトレンドを描画する。

```text
viewof metric = Inputs.select([...new Set(data.map(d => d.metric))], {value: "mutationScore"})
filtered = data.filter(d => d.metric === metric && d.label === "Mutation quick")
Plot.plot({
  marginLeft: 80,
  x: {label: "Snapshot", tickRotate: -45},
  y: {label: "Current"},
  marks: [
    Plot.ruleY([98], {stroke: "orange", strokeDash: "4,2"}),
    Plot.ruleY([96], {stroke: "red", strokeDash: "4,2"}),
    Plot.line(filtered, {x: "snapshot", y: "current", stroke: "steelblue", marker: true})
  ]
})
```

3. `delta` をヒートマップ表示する場合は `Plot.rectY` を使い、critical しきい値を別色で塗り分ける。

### 6. 次ステップ候補
- Slack 通知や Issue アラートから Notebook の該当 snapshot へ直接リンクさせる。
- `history.csv` を Grafana 等の BI ツールへ取り込み、ダッシュボード化する。
- delta の連続悪化を自動コメントと連動させる。
