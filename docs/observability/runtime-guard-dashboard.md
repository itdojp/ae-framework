# Runtime Guard ダッシュボード連携メモ

## 目的
Verify Lite で生成される `artifacts/runtime-guard/runtime-guard-stats.json` を時系列データとして可視化するための手順です。Grafana など任意のダッシュボードに取り込める CSV を生成します。

## エクスポート手順
```bash
node scripts/telemetry/export-runtime-guard-timeseries.mjs artifacts/runtime-guard/runtime-guard-stats.json runtime-guard-last24h.csv
```

上記コマンドは 24 時間分の hourly bucket を `hour,count` 形式の CSV に変換します。出力例:

```csv
hour,count
2025-10-07T08:00:00.000Z,3
```

## 可視化のアイディア
- Grafana Loki / Prometheus 経由で `hour,count` を取り込み、違反件数の推移グラフを表示する。
- 上記 CSV を GitHub Pages / Observable 等で読み込み、簡易的な折れ線グラフを描画する。
- `byEndpoint` 集計と組み合わせて、エンドポイント別のヒートマップを作成し、ランタイムガードのホットスポットを即時に把握する。

## フォローアップ
- Verify Lite ワークフローで `export-runtime-guard-timeseries.mjs` を実行し、CSV をアーティファクトとして保存するタスクを追加予定。
