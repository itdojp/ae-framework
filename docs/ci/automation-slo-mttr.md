---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Automation SLO / MTTR Definitions

This document defines the SLO / MTTR metrics used for PR automation operations. / このドキュメントは、PR 自動化運用で使用する SLO / MTTR の定義をまとめます。

Primary sources / 一次情報:
- `scripts/ci/automation-observability-weekly.mjs`
- `.github/workflows/automation-observability-weekly.yml`

> Language / 言語: English | 日本語

---

## English

### 1. Scope

The denominator for these metrics is the set of `ae-automation-report/v1` reports aggregated by the weekly observability workflow.

Covered workflows:
- `PR Self-Heal`
- `Codex Autopilot Lane`
- `PR Maintenance`
- `Copilot Auto Fix`

This document only defines the weekly SLO / MTTR semantics. Threshold evaluation and alert emission are handled by `scripts/ci/automation-observability-weekly.mjs` and the downstream alert workflow.

### 2. SLO (success rate)

- Metric: `summary.slo.successRatePercent`
- Formula:
  - `successfulReports = totalReports - totalFailures`
  - if `totalReports > 0`: `successRatePercent = successfulReports / totalReports * 100`
  - if `totalReports == 0`: `successRatePercent = null`
- `totalFailures` counts reports where `status in ['error', 'blocked']`
- Target value:
  - `AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT`
  - default: `95`
- Achievement rule:
  - if `successRatePercent != null`: `summary.slo.achieved = successRatePercent >= targetPercent`
  - if `successRatePercent == null`: `summary.slo.achieved = null`

Operational interpretation:
- `done` and `skip` reports remain outside the failure numerator
- the weekly summary treats blocked automation the same as explicit error for SLO purposes
- the SLO is intentionally coarse; drill-down uses `reasonCode`, `reason`, and per-tool breakdowns

### 3. MTTR (mean time to recovery)

Primary fields:
- `summary.mttr.meanMinutes`
- `summary.mttr.p95Minutes`
- `summary.mttr.unresolvedOpenIncidents`

Minimum recovery pairing logic:
1. treat `status in ['error', 'blocked']` as a failure event
2. define the incident key as `tool + incidentScope` (`pr:<number>`, `pull:<ref>`, `sha:<sha>`, or `global`)
3. when a failure occurs for a key that does not already have an open incident, open a new incident and record its start time
4. additional failures for the same key while the incident is still open are aggregated into that incident and do not reset the start time
5. when `status='resolved'` appears for the same key, close the incident and measure the delta in minutes as the recovery duration

Target value:
- `AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES`
- default: `120`

Achievement rule:
- `summary.mttr.achieved = meanMinutes <= targetMinutes`

Operational interpretation:
- `meanMinutes` is the baseline service-level indicator
- `p95Minutes` exposes tail recovery time and is the better signal for repeated prolonged incidents
- `unresolvedOpenIncidents` is the immediate escalation trigger even when mean MTTR still satisfies the target

### 4. Incident classification

`summary.mttr.byIncidentType` uses these classification keys in deterministic order (first match wins):
- `rate_limit_429`: the reason contains `429`, `Too Many Requests`, or `rate limit`
- `behind_loop`: the reason contains `behind`
- `review_gate`: the reason contains `gate` or `review`
- `blocked`: `status='blocked'` or the reason contains `blocked` / `conflict`
- `other`: anything else

This taxonomy is intentionally lightweight. It is designed for weekly triage, not for full root-cause modeling.

### 5. Operating thresholds and triage

- When SLO is missed (`summary.slo.achieved=false`):
  - inspect `summary.topFailureReasonCodes` first because they are stable keys
  - use `summary.topFailureReasons` only as supporting free-text context
- When MTTR is missed (`summary.mttr.achieved=false`):
  - prioritize the highest-frequency and longest-duration buckets in `summary.mttr.byIncidentType`
- When unresolved incidents remain (`unresolvedOpenIncidents > 0`):
  - move to staged stop or manual recovery via `docs/ci/automation-rollback-runbook.md`

Recommended operator reading order:
1. `weekly-failure-summary.json`
2. `summary.topFailureReasonCodes`
3. `summary.mttr.byIncidentType`
4. related rollback / troubleshooting runbooks

### 6. Related documents

- `docs/ci/automation-observability.md`
- `docs/ci/reason-codes.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/automation-rollback-runbook.md`

## 日本語

### 1. 対象

- `PR Self-Heal`
- `Codex Autopilot Lane`
- `PR Maintenance`
- `Copilot Auto Fix`

`ae-automation-report/v1` の集計対象レポートを分母として扱います。ここで列挙しているのは report の `tool` 値ではなく、`DEFAULT_WORKFLOWS` に含まれる対象 workflow 名です。ここでは週次 observability 集計における SLO / MTTR の定義のみを扱い、しきい値評価や alert 発報は `scripts/ci/automation-observability-weekly.mjs` および downstream workflow 側の責務です。

### 2. SLO（成功率）

- 指標: `summary.slo.successRatePercent`
- 算式:
  - `successfulReports = totalReports - totalFailures`
  - `totalReports > 0` の場合: `successRatePercent = successfulReports / totalReports * 100`
  - `totalReports == 0` の場合: `successRatePercent = null`
- `totalFailures` は `status in ['error', 'blocked']`
- 目標値:
  - `AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT`（既定: `95`）
- 達成判定:
  - `successRatePercent != null` の場合: `summary.slo.achieved = successRatePercent >= targetPercent`
  - `successRatePercent == null` の場合: `summary.slo.achieved = null`

運用解釈:
- `done` / `skip` は failure 分子に含めません
- blocked は明示的な error と同様に SLO 失敗として扱います
- SLO は粗い週次指標であり、詳細分析は `reasonCode`、`reason`、tool 別内訳で行います

### 3. MTTR（復旧時間）

- 指標:
  - `summary.mttr.meanMinutes`
  - `summary.mttr.p95Minutes`
  - `summary.mttr.unresolvedOpenIncidents`
- 計測ロジック（最小定義）:
  1. `status in ['error','blocked']` を失敗イベントとして起点化
  2. incident key を `tool + incidentScope`（`pr:<number>` / `pull:<ref>` / `sha:<sha>` / `global`）として定義
  3. その key に未解消インシデントがない場合のみ新規 open し、開始時刻を記録
  4. 未解消の間に同じ key で追加 failure が発生しても、同一インシデントへ集約し、開始時刻は更新しない
  5. 同じ key で `status='resolved'` が来た時点で close し、開始時刻との差分を復旧時間（分）として集計
- 目標値:
  - `AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES`（既定: `120`）
- 達成判定:
  - `summary.mttr.achieved = meanMinutes <= targetMinutes`

運用解釈:
- `meanMinutes` は基本のサービスレベル指標です
- `p95Minutes` は長時間化した復旧の tail を可視化するため、継続的な長期障害の把握に有効です
- `unresolvedOpenIncidents` は mean MTTR が閾値内でも即時エスカレーション対象です

### 4. インシデント分類

`summary.mttr.byIncidentType` の分類キー（first match wins）:
- `rate_limit_429`: reason に `429` / `Too Many Requests` / `rate limit`
- `behind_loop`: reason に `behind`
- `review_gate`: reason に `gate` または `review`
- `blocked`: status=`blocked` または reason に `blocked` / `conflict`
- `other`: 上記以外

この分類は週次トリアージ用の軽量 taxonomy です。完全な root cause modeling ではなく、優先度付けに必要な粒度へ絞っています。

### 5. 運用時の基準

- SLO未達 (`summary.slo.achieved=false`):
  - `summary.topFailureReasonCodes`（安定キー）を先に確認し、再発要因を優先対処
  - `summary.topFailureReasons` は補足の自由記述として扱う
- MTTR未達 (`summary.mttr.achieved=false`):
  - `summary.mttr.byIncidentType` の高頻度・長時間カテゴリを優先改善
- 未解消インシデントあり (`unresolvedOpenIncidents>0`):
  - `docs/ci/automation-rollback-runbook.md` に従って段階停止または手動復旧へ移行

推奨するオペレータの確認順:
1. `weekly-failure-summary.json`
2. `summary.topFailureReasonCodes`
3. `summary.mttr.byIncidentType`
4. rollback / troubleshooting runbook

### 6. 関連ドキュメント

- `docs/ci/automation-observability.md`
- `docs/ci/reason-codes.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/automation-rollback-runbook.md`
