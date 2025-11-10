# Heavy Test Trend Visualization PoC

heavy-test トレンドの履歴 (`reports/heavy-test-trends-history/*.json`) を整形して可視化するためのアイデアをまとめます。

## CSV / Markdown 生成スクリプト
```bash
pnpm node scripts/pipelines/export-heavy-trend-history.mjs   --history-dir reports/heavy-test-trends-history   --csv-output reports/heavy-test-trends-history/history.csv   --markdown-output reports/heavy-test-trends-history/history.md   --markdown-limit 20
```
- `history.csv`: 全スナップショットの `snapshot,label,metric,baseline,current,delta` を含む。Observable や Excel での分析に利用。  
- `history.md`: 直近 N 件を Markdown テーブルで出力し、PR やドキュメントに貼り付け可能。

## Markdown プレビュー例
| Snapshot | Label | Metric | Baseline | Current | Δ |
| --- | --- | --- | --- | --- | --- |
| ... | ... | ... | ... | ... | ... |

## Observable Notebook での活用例
1. `history.csv` を `FileAttachment` として Notebook にアップロード。  
2. 以下のコードで CSV を読み込み、Mutation score のトレンドを描画。
```js
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
3. `delta` をヒートマップ表示する場合は `Plot.rectY` を利用し、critical しきい値を別色で塗り分ける。

## 今後のステップ
- Slack 通知／Issue 起票で共有された snapshot ラベルから直接 Notebook の該当位置へリンクさせる。  
- Grafana 等の BI ツールへ `history.csv` を取り込み、ダッシュボード化する。  
- delta が連続で悪化した場合の自動コメントなど、可視化結果とアラートを結びつける。
