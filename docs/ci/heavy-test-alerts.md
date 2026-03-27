---
docRole: ssot
lastVerified: '2026-03-27'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Heavy Test Trend Alerting Plan

This document defines threshold proposals and operating rules for heavy-test trend alerting. / このドキュメントは、heavy-test trend alerting のしきい値案と運用ルールを定義します。

Primary sources / 一次情報:
- workflow: `.github/workflows/ci-extended.yml`
- summary script: `scripts/pipelines/render-heavy-trend-summary.mjs`
- threshold helper: `scripts/pipelines/recommend-heavy-trend-thresholds.mjs`

> Language / 言語: English | 日本語

---

## English

### 1. Target metrics

- **Mutation quick**
  - absolute `mutationScore` and the delta (`Δ`) from the previous baseline
  - rapid increases in report counts (`survived`, `timedOut`, `ignored`) as supporting indicators
- **Property harness**
  - `failed` count and failure rate against `runs`
  - repeated failures grouped by `traceId`
- **MBT harness**
  - `violations` count
  - extreme changes in `runs` or `depth`

`render-heavy-trend-summary.mjs` already accepts `--warn-*` and `--critical-*` options and can evaluate `reports/heavy-test-trends-history/summary.md` and `reports/heavy-test-trends-history/summary.json` directly.

### 2. Initial threshold proposal

| Metric | Warning | Critical | Notes |
| --- | --- | --- | --- |
| Mutation score | `current < 98` or `Δ <= -1.0` | `current < 96` or `Δ <= -2.5` | `Δ` is measured against the baseline. Warning should notify Slack. Critical should consider auto-opening an issue. |
| Property failed count | `failed >= 1` | `failed >= 3` | Treat failure rate above 10% as Warning as well. |
| MBT violations | `violations >= 1` | `violations >= 3` | Any non-zero violation requires detailed log inspection. |

### 3. Notification flow (current implementation)

1. Add threshold options to `render-heavy-trend-summary.mjs` and embed `:warning:` / `:rotating_light:` markers into the Markdown output.
2. When at least one metric is Warning or worse, send a Slack webhook message from the scheduled path in `ci-extended.yml`.
3. Create a GitHub issue only when `steps.harness-health.outputs.severity == 'critical'`. When a heavy-trend snapshot is also critical, the issue body includes the critical heavy-trend entries as supporting detail.
4. Run the same summary script in scheduled execution, or in `workflow_dispatch` with `trigger=schedule`, and publish the decision in the GitHub Step Summary. Normal PR reruns do not execute this path.

#### Critical issue creation (current implementation)

- Repository: `itdojp/ae-framework`
- Labels: `flaky-test`, `ci-stability`, `needs-investigation`
- Title example: `[CI Extended] Harness health critical alert - <snapshotLabel>`
- Body template:
  ```md
  ## Alert
  - Workflow: ${{ github.workflow }} (run: ${{ github.server_url }}/${{ github.repository }}/actions/runs/${{ github.run_id }})
  - Severity: critical
  - Snapshot: <timestamp>
  - Summary: reports/heavy-test-trends-history/summary.md
  - JSON: reports/heavy-test-trends-history/summary.json

  ## Next Steps
  - [ ] Download artifacts and inspect mutation/property/MBT outputs
  - [ ] Update issue with root cause and resolution plan
  ```
- Implementation note: the `Create harness health critical issue` step in `ci-extended.yml` opens the issue through `actions/github-script` when `steps.harness-health.outputs.severity == 'critical'`.

### 4. Implementation status

- [x] Threshold options added to `render-heavy-trend-summary.mjs`
- [x] JSON output for machine-readable decisions (`--json-output`)
- [x] Slack notification step added to scheduled `ci-extended`
- [x] Auto issue creation for harness-health Critical results (`ci-extended.yml`)
- [x] History archive for `reports/heavy-test-trends-history/*.json` plus periodic generation of `reports/heavy-test-trends-history/summary.md` / `reports/heavy-test-trends-history/summary.json`
- [x] Artifact retention extended to 30 days for 2-3 week trend analysis
- [x] Threshold recommendation helper added (`scripts/pipelines/recommend-heavy-trend-thresholds.mjs`)
- [ ] Threshold refinement based on measured data (`min-snapshots=14` or more)

### 5. Operating notes

- The thresholds are initial proposals. Revisit them after 2-3 weeks of real data.
- To reduce false positives, consider a mode that escalates only after the `Δ` threshold is crossed twice in a row.
- Slack delivery will often occur during JST late-night windows. Confirm channel silence rules before enabling broad notifications.
- When an issue is created, always attach the corresponding `reports/heavy-test-trends-history/<timestamp>.json`, `reports/heavy-test-trends-history/summary.md`, and the run URL.
- Before applying revised thresholds to the workflow, run the recommendation helper and confirm `Status: ready`.
  - `node scripts/pipelines/recommend-heavy-trend-thresholds.mjs --history-dir reports/heavy-test-trends-history --min-snapshots 14`

### 6. Backlog

- [x] Threshold options in `render-heavy-trend-summary.mjs`
- [x] Slack webhook notification step in scheduled `ci-extended`
- [x] Auto issue creation flow for Critical results
- [x] History archive for threshold refinement
- [x] Automatic threshold recommendation report (`threshold-recommendation.md/json`)
- [ ] Apply threshold refinement using `threshold-recommendation`

## 日本語

### 1. 対象メトリクス
- **Mutation quick**
  - `mutationScore` の絶対値と直近比較 (`Δ`).
  - レポート件数（`survived`, `timedOut`, `ignored`）の急増を補足指標とする。
- **Property harness**
  - `failed` 件数、`runs` に対する失敗率。
  - `traceId` 単位での連続失敗を検知対象にする。
- **MBT harness**
  - `violations` 件数、および `runs` / `depth` の極端な変化。

`scripts/pipelines/render-heavy-trend-summary.mjs` で ``--warn-*`` / ``--critical-*`` オプションを指定し、`reports/heavy-test-trends-history/summary.md` / `reports/heavy-test-trends-history/summary.json` から自動判定できるようになりました。

### 2. 初期閾値案
| メトリクス | Warning | Critical | 備考 |
|------------|---------|----------|------|
| Mutation score | `current < 98` または `Δ <= -1.0` | `current < 96` または `Δ <= -2.5` | Δ は baseline との差。Warning で Slack 通知、Critical で Issue 起票を検討。|
| Property failed count | `failed >= 1` | `failed >= 3` | 失敗率が 10% を超えた場合も Warning。|
| MBT violations | `violations >= 1` | `violations >= 3` | violations が 0 でない場合は詳細ログ確認を必須にする。|

### 3. 通知フロー（現行実装）
1. `render-heavy-trend-summary.mjs` に閾値判定オプションを追加し、Markdown 出力内に :warning:/:rotating_light: を埋め込む。
2. Warning 以上の項目が存在する場合は Slack Webhook（`ci-extended.yml` スケジュール実行に追加済み）でメッセージ送信。
3. GitHub Issue の自動起票は `steps.harness-health.outputs.severity == 'critical'` の場合のみ実行する。heavy trend 側にも critical snapshot がある場合は、その詳細を補足情報として Issue 本文に含める。
4. スケジュール実行（または `workflow_dispatch` で `trigger=schedule` 指定時）に同スクリプトを実行し、Step Summary に判定結果を表示する（通常の PR rerun では実行されない）。

#### Critical 判定時の Issue 起票（現行実装）
- 作成先: `itdojp/ae-framework` / labels: `flaky-test`, `ci-stability`, `needs-investigation`
- タイトル例: `[CI Extended] Harness health critical alert - <snapshotLabel>`
- 本文テンプレート:
  ```md
  ## Alert
  - Workflow: ${{ github.workflow }} (run: ${{ github.server_url }}/${{ github.repository }}/actions/runs/${{ github.run_id }})
  - Severity: critical
  - Snapshot: <timestamp>
  - Summary: reports/heavy-test-trends-history/summary.md
  - JSON: reports/heavy-test-trends-history/summary.json

  ## Next Steps
  - [ ] Download artifacts and inspect mutation/property/MBT outputs
  - [ ] Update issue with root cause and resolution plan
  ```
- 実装: `ci-extended.yml` の `Create harness health critical issue` ステップで `steps.harness-health.outputs.severity == 'critical'` 時に `actions/github-script` から Issue を自動起票。

### 4. 実装状況
- [x] `render-heavy-trend-summary.mjs` への閾値オプション追加
- [x] JSON 形式の判定結果出力（`--json-output`）
- [x] `ci-extended` スケジュール実行への Slack 通知ステップ追加
- [x] harness-health の Critical 判定時の自動 Issue 起票（`ci-extended.yml`）
- [x] `reports/heavy-test-trends-history/*.json` の履歴アーカイブと `reports/heavy-test-trends-history/summary.md` / `reports/heavy-test-trends-history/summary.json` の定期生成
- [x] 履歴アーティファクト保持期間を 30 日に拡張（2〜3週間分の分析前提を満たす）
- [x] 閾値見直し補助スクリプトを追加（`scripts/pipelines/recommend-heavy-trend-thresholds.mjs`）
- [ ] 実測データに基づく閾値リファイン（`min-snapshots=14` 以上で実施）

### 5. 運用上の注意
- 閾値は初期案。実データに基づき 2〜3 週間運用した後に見直す。
- false positive を避けるため、`Δ` 判定は 2 回連続で閾値を下回った場合にエスカレーションするモードも検討する。
- Slack 通知は深夜帯（JST）に偏るため、通知チャンネルのサイレンス設定を確認する。
- Issue 起票時には関連する `reports/heavy-test-trends-history/<timestamp>.json` と `reports/heavy-test-trends-history/summary.md`、該当 run の URL を必ず添付する。
- 閾値見直し時は次を実行し、`Status: ready` を確認してから workflow 閾値へ反映する。
  - `node scripts/pipelines/recommend-heavy-trend-thresholds.mjs --history-dir reports/heavy-test-trends-history --min-snapshots 14`

### 6. Backlog
- [x] `render-heavy-trend-summary.mjs` への閾値オプション追加
- [x] Slack Webhook 通知ステップの実装（`ci-extended.yml` スケジュール実行に追加済み）
- [x] 自動 Issue 起票フローの実装（Critical 判定時）
- [x] 閾値リファイン向けの実測データ収集基盤（履歴アーカイブ）整備
- [x] 閾値見直し補助レポートの自動生成（`threshold-recommendation.md/json`）
- [ ] 閾値リファイン実施（`threshold-recommendation` を根拠に workflow へ反映）
