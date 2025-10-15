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

## データソース
- API: `/api/runtime-guard/stats` が最新違反状況を返却。Verify Lite pipeline ではこのエンドポイントを呼び出して `artifacts/runtime-guard/runtime-guard-stats.json` を生成する。
- Step Summary: `scripts/telemetry/render-runtime-guard-summary.mjs` で Markdown を生成し、Gate から参照できるようにする。
- 時系列変換: `scripts/telemetry/export-runtime-guard-timeseries.mjs` で 24h の hourly bucket を CSV 化し、Grafana や Observable notebook から参照可能にする。

## 収集フロー案
1. Verify Lite の post-processing で `/api/runtime-guard/stats` をフェッチし `artifacts/runtime-guard/runtime-guard-stats.json` を保存。
2. 上記ファイルを `render-runtime-guard-summary.mjs` に渡して Step Summary へ埋め込み。
3. 同じ run 内で `export-runtime-guard-timeseries.mjs` を実行し、`artifacts/runtime-guard/runtime-guard-timeseries.csv` を生成。
4. 生成した CSV を GitHub Actions の artifact として公開し、ダッシュボードツールに取り込む。

## ダッシュボード構成案
| パネル | 指標 | データソース | 備考 |
| --- | --- | --- | --- |
| Violations per hour | `hour,count` | timeseries CSV | 直近 24 時間の推移を棒グラフ表示。
| Violations by type | `stats.byType` | JSON | Pie/ドーナツでホットスポットを可視化。
| Top endpoints | `stats.byEndpoint` (今後拡張) | JSON | 主要エンドポイントごとの件数。
| Severity split | `stats.bySeverity` | JSON | Critical/High をウォッチ。
| Recent violations | `stats.recent` | JSON | 最新 5 件を Table で列挙。

## CI 連携計画
- `scripts/ci/run-verify-lite-local.sh` に runtime guard fetch + summary + timeseries export をフックし、Step Summary と artifact を常に更新する。
- `pnpm pipelines:full` 実行時にも同じ処理を走らせ、フルパイプラインで生成される `hermetic-reports` に CSV/JSON を配置。
- 将来的には timeseries CSV を Tempo/Grafana に push するジョブ、もしくは S3 へ転送するスクリプトを整備する。

## TODO / 次のアクション
- [ ] `/api/runtime-guard/stats` に `byEndpoint` や `hourlyBuckets` などダッシュボード向けメタデータを拡張する。
- [ ] Verify Lite ワークフローで `render-runtime-guard-summary.mjs` / `export-runtime-guard-timeseries.mjs` を実行し、出力を Step Summary + artifact に組み込む。
- [ ] Grafana/Observable テンプレートを作成し、CSV を取り込むサンプルを共有。
