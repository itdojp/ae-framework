---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Automation Alerting

This document defines how weekly automation observability results are converted into operator alerts. / このドキュメントは、週次の自動化 observability 集計結果を運用アラートへ変換するルールを定義します。

Primary sources / 一次情報:
- workflow: `.github/workflows/automation-observability-weekly.yml`
- summary script: `scripts/ci/automation-observability-weekly.mjs`
- alert script: `scripts/ci/automation-observability-alert.mjs`

> Language / 言語: English | 日本語

---

## English

### 1. Minimum setup

- Notification channel: `issue_comment`
- Notification destination: `AE_AUTOMATION_ALERT_ISSUE_NUMBER`
  - default: `1963`
  - normal operation: configure the long-lived operations issue as a Repository Variable
  - temporary override: pass a different issue number through `workflow_dispatch`
- Duplicate suppression:
  - suppress the same fingerprint unconditionally as `duplicate_fingerprint`
  - for different fingerprints, suppress new posts while the latest alert comment is still within `AE_AUTOMATION_ALERT_COOLDOWN_HOURS`

Slack or other external channels are not implemented in the current workflow. If an external sink is required, consume `weekly-alert-summary.json` from a separate workflow or job.

### 2. Alert conditions

The alert script evaluates `summary` from `weekly-failure-summary.json`.

| Code | Condition | Default threshold |
| --- | --- | --- |
| `blocked_spike` | `summary.byStatus.blocked` exceeds the limit | `AE_AUTOMATION_ALERT_MAX_BLOCKED=2` |
| `consecutive_failures` | `summary.maxConsecutiveFailures` exceeds the limit | `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES=3` |
| `slo_breach` | `summary.slo.successRatePercent < target` | `AE_AUTOMATION_ALERT_SLO_TARGET_PERCENT` -> `AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT` -> summary |
| `mttr_breach` | `summary.mttr.meanMinutes > target` | `AE_AUTOMATION_ALERT_MTTR_TARGET_MINUTES` -> `AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES` -> summary |

`slo_breach` and `mttr_breach` are evaluated only when the corresponding SLO / MTTR values exist in the summary.

### 3. Comment template

The issue-comment body is built from these elements.

- marker: `<!-- AE-AUTOMATION-ALERT v1 -->`
- Triggered conditions (`code`, `severity`, `value`, `threshold`)
- Cause (initial): top failure reason
- Cause (initial): top failure `reasonCode`
- Impact: shared operational impact text
- Primary actions: first-response actions mapped by alert code
- References: sample run URL, runbook, observability docs
- fingerprint marker: `<!-- AE-AUTOMATION-ALERT-FP <hex16> -->`

The fingerprint marker is the stable suppression key. The same fingerprint is always suppressed as `duplicate_fingerprint`, regardless of cooldown. For different fingerprints, the workflow suppresses a new comment only when the latest alert comment is still within `AE_AUTOMATION_ALERT_COOLDOWN_HOURS`, and records that result in `weekly-alert-summary.json`.

### 4. Key environment variables

- `AE_AUTOMATION_OBSERVABILITY_ALERT_INPUT` (default: `artifacts/automation/weekly-failure-summary.json`)
- `AE_AUTOMATION_OBSERVABILITY_ALERT_OUTPUT` (default: `artifacts/automation/weekly-alert-summary.json`)
- `AE_AUTOMATION_ALERT_CHANNEL` (`issue_comment` / `dry_run`)
- `AE_AUTOMATION_ALERT_ISSUE_NUMBER`
- `AE_AUTOMATION_ALERT_MAX_BLOCKED`
- `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES`
- `AE_AUTOMATION_ALERT_SLO_TARGET_PERCENT` (`slo_breach` threshold)
- `AE_AUTOMATION_ALERT_MTTR_TARGET_MINUTES` (`mttr_breach` threshold)
- `AE_AUTOMATION_ALERT_COOLDOWN_HOURS`
- `AE_AUTOMATION_ALERT_DRY_RUN` (suppresses the actual issue comment when `true`)

Operational note:
- When `AE_AUTOMATION_ALERT_CHANNEL=dry_run` or `AE_AUTOMATION_ALERT_DRY_RUN=true`, the script still performs suppression evaluation if `issue_number` is available and writes the result to `weekly-alert-summary.json`.

### 5. Operating flow

1. The weekly workflow generates `weekly-failure-summary.json`.
2. The alert script evaluates thresholds and suppression state.
3. It posts an issue comment only when at least one alert condition matches and suppression does not apply.
4. The decision is persisted to `weekly-alert-summary.json` and the GitHub Step Summary.

Use `weekly-alert-summary.json` as the first evidence source during triage. It records whether the alert was emitted, suppressed, or skipped, plus the reason.

### 6. Troubleshooting

- No alert is posted:
  - verify that `AE_AUTOMATION_ALERT_DRY_RUN` is not `true`
  - verify that `AE_AUTOMATION_ALERT_ISSUE_NUMBER` is neither `0` nor unset
  - inspect `suppressed=true` and `suppressedReason` in `weekly-alert-summary.json`
- Too many alerts are posted:
  - increase `AE_AUTOMATION_ALERT_COOLDOWN_HOURS`
  - tune `AE_AUTOMATION_ALERT_MAX_BLOCKED` or `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES`
- `slo_breach` or `mttr_breach` never triggers:
  - confirm that `summary.slo.*` and `summary.mttr.*` are present in `weekly-failure-summary.json`
  - confirm whether override variables are masking the summary defaults

## 日本語

### 1. 最小構成

- 通知チャネル: `issue_comment`
- 通知先: `AE_AUTOMATION_ALERT_ISSUE_NUMBER`
  - 既定: `1963`
  - 通常運用: Repository Variable で固定の運用 Issue を定義
  - 一時上書き: `workflow_dispatch` 入力で別 Issue 番号を指定可能
- 通知の重複抑止:
  - 同一 fingerprint は cooldown に関係なく `duplicate_fingerprint` として常に抑止
  - 別 fingerprint については、直近の alert comment から `AE_AUTOMATION_ALERT_COOLDOWN_HOURS` 内であれば新規通知を抑止

Slack 等の外部チャネルは current workflow では未対応です。必要な場合は別 workflow / job で `weekly-alert-summary.json` を取り込んで拡張します。

### 2. 通知条件

`weekly-failure-summary.json` の `summary` を入力に判定します。

| Code | 条件 | 既定しきい値 |
| --- | --- | --- |
| `blocked_spike` | `summary.byStatus.blocked` が上限超過 | `AE_AUTOMATION_ALERT_MAX_BLOCKED=2` |
| `consecutive_failures` | `summary.maxConsecutiveFailures` が上限超過 | `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES=3` |
| `slo_breach` | `summary.slo.successRatePercent < target` | `AE_AUTOMATION_ALERT_SLO_TARGET_PERCENT` -> `AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT` -> summary |
| `mttr_breach` | `summary.mttr.meanMinutes > target` | `AE_AUTOMATION_ALERT_MTTR_TARGET_MINUTES` -> `AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES` -> summary |

`slo_breach` / `mttr_breach` は、対応する SLO / MTTR 値が summary に存在する場合のみ判定します。

### 3. 通知テンプレート

Issue comment の本文は次の要素で構成します。

- marker: `<!-- AE-AUTOMATION-ALERT v1 -->`
- Triggered conditions（`code`, `severity`, `value`, `threshold`）
- Cause (initial): top failure reason
- Cause (initial): top failure `reasonCode`
- Impact: 共通の運用影響文言
- Primary actions: code 別の一次対応
- References: sample run URL / runbook / observability docs
- fingerprint marker: `<!-- AE-AUTOMATION-ALERT-FP <hex16> -->`

fingerprint marker は抑止判定の安定キーです。同一 fingerprint は cooldown に関係なく常に `duplicate_fingerprint` として抑止し、`weekly-alert-summary.json` に suppression 結果を書き込みます。別 fingerprint については、直近の alert comment から `AE_AUTOMATION_ALERT_COOLDOWN_HOURS` 内であれば新規 comment を投稿せず抑止し、同様に `weekly-alert-summary.json` へ記録します。

### 4. 主要環境変数

- `AE_AUTOMATION_OBSERVABILITY_ALERT_INPUT`（既定: `artifacts/automation/weekly-failure-summary.json`）
- `AE_AUTOMATION_OBSERVABILITY_ALERT_OUTPUT`（既定: `artifacts/automation/weekly-alert-summary.json`）
- `AE_AUTOMATION_ALERT_CHANNEL`（`issue_comment` / `dry_run`）
- `AE_AUTOMATION_ALERT_ISSUE_NUMBER`
- `AE_AUTOMATION_ALERT_MAX_BLOCKED`
- `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES`
- `AE_AUTOMATION_ALERT_SLO_TARGET_PERCENT`（`slo_breach` 判定しきい値）
- `AE_AUTOMATION_ALERT_MTTR_TARGET_MINUTES`（`mttr_breach` 判定しきい値）
- `AE_AUTOMATION_ALERT_COOLDOWN_HOURS`
- `AE_AUTOMATION_ALERT_DRY_RUN`（`true` の場合は issue comment 投稿を抑止）

運用補足:
- `AE_AUTOMATION_ALERT_CHANNEL=dry_run` または `AE_AUTOMATION_ALERT_DRY_RUN=true` の場合も、`issue_number` が設定されていれば suppression 判定は実行し、結果を `weekly-alert-summary.json` に反映します。

### 5. 運用フロー

1. 週次 workflow が `weekly-failure-summary.json` を生成
2. alert script が条件判定と suppression 判定を実施
3. 条件一致かつ suppression なしの場合のみ Issue comment を投稿
4. 判定結果を `weekly-alert-summary.json` と GitHub Step Summary に保存

トリアージでは最初に `weekly-alert-summary.json` を確認します。通知の投稿・抑止・skip の別と、その理由をここで確認できます。

### 6. トラブルシュート

- 通知が出ない:
  - `AE_AUTOMATION_ALERT_DRY_RUN` が `true` になっていないか
  - `AE_AUTOMATION_ALERT_ISSUE_NUMBER` が `0` / 未設定になっていないか
  - `weekly-alert-summary.json` の `suppressed=true` / `suppressedReason` を確認
- 通知が過剰:
  - `AE_AUTOMATION_ALERT_COOLDOWN_HOURS` を延長
  - `AE_AUTOMATION_ALERT_MAX_BLOCKED` / `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES` を調整
- `slo_breach` / `mttr_breach` が発火しない:
  - `weekly-failure-summary.json` に `summary.slo.*` / `summary.mttr.*` が存在するか確認
  - override 変数が summary の既定値を上書きしていないか確認
