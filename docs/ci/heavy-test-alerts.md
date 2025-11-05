# Heavy Test Trend Alerting Plan

## 対象メトリクス
- **Mutation quick**
  - `mutationScore` の絶対値と直近比較 (`Δ`).
  - レポート件数（`survived`, `timedOut`, `ignored`）の急増を補足指標とする。
- **Property harness**
  - `failed` 件数、`runs` に対する失敗率。
  - `traceId` 単位での連続失敗を検知対象にする。
- **MBT harness**
  - `violations` 件数、および `runs` / `depth` の極端な変化。

`scripts/pipelines/render-heavy-trend-summary.mjs` で ``--warn-*`` / ``--critical-*`` オプションを指定し、`summary.md` / `summary.json` から自動判定できるようになりました。

## 初期閾値案
| メトリクス | Warning | Critical | 備考 |
|------------|---------|----------|------|
| Mutation score | `current < 98` または `Δ <= -1.0` | `current < 96` または `Δ <= -2.5` | Δ は baseline との差。Warning で Slack 通知、Critical で Issue 起票を検討。|
| Property failed count | `failed >= 1` | `failed >= 3` | 失敗率が 10% を超えた場合も Warning。|
| MBT violations | `violations >= 1` | `violations >= 3` | violations が 0 でない場合は詳細ログ確認を必須にする。|

## 通知フロー案
1. `render-heavy-trend-summary.mjs` に閾値判定オプションを追加し、Markdown 出力内に :warning:/:rotating_light: を埋め込む。
2. Warning 以上の項目が存在する場合は Slack Webhook（`nightly-monitoring` 既存通知を再利用）でメッセージ送信。
3. Critical 判定時は GitHub Issue（`flaky-test` ラベル）を自動作成し、関連ログ／アーティファクトへのリンクを添付。
4. PR 上で手動 rerun を行う際も同スクリプトを実行し、Step Summary に判定結果を表示する。

## 実装ステップ
1. `render-heavy-trend-summary.mjs` を拡張し、`--warn-mutation-score`, `--critical-mutation-score` 等の CLI オプションで閾値を受け取り、Markdown 内にバッジを表示する。
2. CLI から JSON 形式の判定結果を吐き出す (`--json-output`)、Slack ワークフローで利用できるようにする。
3. `ci-extended` のスケジュール実行後に判定スクリプトを実行し、Warning 以上の場合は Slack 通知ステップを追加する。
4. Critical の場合は `gh issue create` を用いた自動起票か、既存 `nightly-monitoring` に統合する。

## 運用上の注意
- 閾値は初期案。実データに基づき 2〜3 週間運用した後に見直す。
- false positive を避けるため、`Δ` 判定は 2 回連続で閾値を下回った場合にエスカレーションするモードも検討する。
- Slack 通知は深夜帯（JST）に偏るため、通知チャンネルのサイレンス設定を確認する。
- Issue 起票時には関連する `heavy-test-trends-history/<timestamp>.json` と `summary.md`、該当 run の URL を必ず添付する。

## TODO
- [x] `render-heavy-trend-summary.mjs` への閾値オプション追加
- [x] Slack Webhook 通知ステップの実装（`ci-extended.yml` スケジュール実行に追加済み）
- [ ] 自動 Issue 起票フローの設計（Critical 判定時）
- [ ] 閾値リファインのためのメトリクス実測データ収集
