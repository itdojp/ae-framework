# Automation Alerting

`automation-observability-weekly` の集計結果から、重大な運用異常を通知するための仕様。

一次情報:
- workflow: `.github/workflows/automation-observability-weekly.yml`
- summary script: `scripts/ci/automation-observability-weekly.mjs`
- alert script: `scripts/ci/automation-observability-alert.mjs`

## 1. 最小構成

- 通知チャネル: `issue_comment`
- 通知先: `AE_AUTOMATION_ALERT_ISSUE_NUMBER`（既定 `1963`）
- 通知の重複抑止:
  - 同一 fingerprint（同一期間・同一条件）を再投稿しない
  - 最終通知から `AE_AUTOMATION_ALERT_COOLDOWN_HOURS` 内は新規通知を抑止

Slack 等の外部チャネルは未対応。必要時は別 workflow/job で `weekly-alert-summary.json` を取り込み拡張する。

## 2. 通知条件

`weekly-failure-summary.json` の `summary` を入力に判定する。

| Code | 条件 | 既定しきい値 |
| --- | --- | --- |
| `blocked_spike` | `summary.byStatus.blocked` が上限超過 | `AE_AUTOMATION_ALERT_MAX_BLOCKED=2` |
| `consecutive_failures` | `summary.maxConsecutiveFailures` が上限超過 | `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES=3` |
| `slo_breach` | `summary.slo.successRatePercent < target` | target は summary or env |
| `mttr_breach` | `summary.mttr.meanMinutes > target` | target は summary or env |

`slo_breach` / `mttr_breach` は SLO/MTTR 値が存在する場合のみ判定。

## 3. 通知テンプレート

Issue comment の本文は次の要素で構成する。

- marker: `<!-- AE-AUTOMATION-ALERT v1 -->`
- Triggered conditions（code/severity/value/threshold）
- Cause (initial): top failure reason
- Impact: 運用影響の共通文言
- Primary actions: code別の一次対応
- References: sample run URL / runbook / observability docs
- fingerprint marker: `<!-- AE-AUTOMATION-ALERT-FP <hex16> -->`

## 4. 主要環境変数

- `AE_AUTOMATION_OBSERVABILITY_ALERT_INPUT`（既定: `artifacts/automation/weekly-failure-summary.json`）
- `AE_AUTOMATION_OBSERVABILITY_ALERT_OUTPUT`（既定: `artifacts/automation/weekly-alert-summary.json`）
- `AE_AUTOMATION_ALERT_CHANNEL`（`issue_comment` / `dry_run`）
- `AE_AUTOMATION_ALERT_ISSUE_NUMBER`
- `AE_AUTOMATION_ALERT_MAX_BLOCKED`
- `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES`
- `AE_AUTOMATION_ALERT_COOLDOWN_HOURS`
- `AE_AUTOMATION_ALERT_DRY_RUN`（`true` で通知投稿を抑止）

補足:
- `AE_AUTOMATION_ALERT_CHANNEL=dry_run` または `AE_AUTOMATION_ALERT_DRY_RUN=true` の場合も、`issue_number` が設定されていれば suppression 判定自体は実行し、`weekly-alert-summary.json` に反映する。

## 5. 運用

1. 週次 workflow が summary を生成
2. alert script が条件判定と抑止判定を実施
3. 条件一致かつ抑止なしの場合のみ Issue comment を投稿
4. 判定結果は `weekly-alert-summary.json` と Step Summary に保存

## 6. トラブルシュート

- 通知が出ない:
  - `AE_AUTOMATION_ALERT_DRY_RUN` が `true` になっていないか
  - `AE_AUTOMATION_ALERT_ISSUE_NUMBER` が 0 / 未設定になっていないか
  - `suppressed=true` / `suppressedReason` を `weekly-alert-summary.json` で確認
- 通知が過剰:
  - `AE_AUTOMATION_ALERT_COOLDOWN_HOURS` を延長
  - `AE_AUTOMATION_ALERT_MAX_BLOCKED` / `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES` を調整
