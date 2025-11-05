# Heavy Test Trend Visualization PoC

heavy-test トレンドの履歴 (`reports/heavy-test-trends-history/*.json`) を整形して可視化するためのアイデアをまとめます。

## CSV / Markdown 生成スクリプト
```
node scripts/pipelines/export-heavy-trend-history.mjs   --history-dir reports/heavy-test-trends-history   --csv-output reports/heavy-test-trends-history/history.csv   --markdown-output reports/heavy-test-trends-history/history.md   --markdown-limit 20
```
- `history.csv`: 全スナップショットの `snapshot,label,metric,baseline,current,delta` を含む。Observable/Excel での分析に利用。
- `history.md`: 直近 N 件を Markdown テーブルで出力し、PR やドキュメントに貼り付け可能。

## Markdown プレビュー例
| Snapshot | Label | Metric | Baseline | Current | Δ |
| --- | --- | --- | --- | --- | --- |
| ... | ... | ... | ... | ... | ... |

## 可視化の方向性
- Observable Notebook で `history.csv` を読み込み、Mutation score のヒートマップや property failure rate のトレンドグラフを作成。
- Critical アラート発生時は対象スナップショットを強調表示し、Issue リンクを添付。
- 長期的には Slack 通知に同テーブルを添付、または Grafana ログ取り込みを検討。
