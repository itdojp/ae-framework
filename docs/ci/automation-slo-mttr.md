# Automation SLO / MTTR Definitions

PR 自動化運用で使用する SLO / MTTR の定義をまとめる。

一次情報:
- `scripts/ci/automation-observability-weekly.mjs`
- `.github/workflows/automation-observability-weekly.yml`

## 1. 対象

- `PR Self-Heal`
- `Codex Autopilot Lane`
- `PR Maintenance`
- `Copilot Auto Fix`

`ae-automation-report/v1` の集計対象レポートを分母として扱う。

## 2. SLO（成功率）

- 指標: `successRatePercent`
- 算式:
  - `successfulReports = totalReports - totalFailures`
  - `successRatePercent = successfulReports / totalReports * 100`
- `totalFailures` は `status in ['error', 'blocked']`
- 目標値:
  - `AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT`（既定: `95`）
- 達成判定:
  - `summary.slo.achieved = successRatePercent >= targetPercent`

## 3. MTTR（復旧時間）

- 指標:
  - `summary.mttr.meanMinutes`
  - `summary.mttr.p95Minutes`
  - `summary.mttr.unresolvedOpenIncidents`
- 計測ロジック（最小定義）:
  1. `status in ['error','blocked']` を失敗イベントとして起点化
  2. 同一 `tool` の次の `status='resolved'` を復旧イベントとして対応付け
  3. 差分時間を復旧時間（分）として集計
- 目標値:
  - `AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES`（既定: `120`）
- 達成判定:
  - `summary.mttr.achieved = meanMinutes <= targetMinutes`

## 4. インシデント分類

`summary.mttr.byIncidentType` の分類キー:
- `rate_limit_429`: reason に `429` / `Too Many Requests` / `rate limit`
- `review_gate`: reason に `gate` または `review`
- `behind_loop`: reason に `behind`
- `blocked`: status=`blocked` または reason に `blocked` / `conflict`
- `other`: 上記以外

## 5. 運用時の基準

- SLO未達 (`summary.slo.achieved=false`):
  - Top failure reasons を確認し、対象 workflow の再発要因を優先対処
- MTTR未達 (`summary.mttr.achieved=false`):
  - `summary.mttr.byIncidentType` の高頻度・長時間カテゴリを優先改善
- 未解消インシデントあり (`unresolvedOpenIncidents>0`):
  - `docs/ci/automation-rollback-runbook.md` に従って段階停止または手動復旧へ移行

## 6. 関連ドキュメント

- `docs/ci/automation-observability.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/automation-rollback-runbook.md`
