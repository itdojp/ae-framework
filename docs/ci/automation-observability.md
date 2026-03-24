---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Automation Observability

This document defines the shared `ae-automation-report/v1` output contract and weekly observability aggregation used by PR automation workflows. / このドキュメントは、PR 自動化 workflow が出力する共通契約 `ae-automation-report/v1` と、その週次 observability 集計を定義します。

Primary sources / 一次情報:
- `scripts/ci/lib/automation-report.mjs`
- `scripts/ci/pr-self-heal.mjs`
- `scripts/ci/codex-autopilot-lane.mjs`
- `scripts/ci/auto-merge-enabler.mjs`
- `scripts/ci/copilot-auto-fix.mjs`
- `.github/workflows/spec-generate-model.yml` (`kvonce-trace-validation` report-emitting step)

> Language / 言語: English | 日本語

---

## English

### 1. Output destinations

Automation scripts emit `ae-automation-report/v1` through these channels:
- **stdout**: single-line JSON with prefix `[ae-automation-report]`
- **GitHub Step Summary**: appended automatically when `GITHUB_STEP_SUMMARY` is available
- **optional JSON file**: written when `AE_AUTOMATION_REPORT_FILE` is set

Operational note:
- stdout is the canonical extraction source for weekly aggregation
- the optional JSON file is primarily for artifact preservation and local debugging
- Step Summary is an operator convenience view, not the system-of-record input

### 2. Shared schema (overview)

Representative payload:

```json
{
  "schemaVersion": "ae-automation-report/v1",
  "generatedAt": "2026-02-13T00:00:00.000Z",
  "tool": "codex-autopilot-lane",
  "mode": "active",
  "status": "blocked",
  "reasonCode": "policy.required_labels_missing",
  "reason": "missing policy labels: run-security, run-ci-extended",
  "prNumber": 123,
  "metrics": {},
  "data": {},
  "run": {
    "workflow": "PR Self-Heal",
    "event": "workflow_dispatch",
    "runId": 21966754908,
    "attempt": 1,
    "url": "https://github.com/itdojp/ae-framework/actions/runs/21966754908",
    "repository": "itdojp/ae-framework",
    "ref": "refs/heads/main",
    "sha": "..."
  }
}
```

Key field roles:
- `tool`: stable producer identifier used for tool-level aggregation
- `status`: normalized operational outcome
- `reasonCode`: stable machine-readable failure/skip key
- `reason`: human-readable detail
- `metrics` / `data`: producer-specific extensions
- `run`: workflow/run provenance used for weekly correlation and evidence links

### 3. `status` semantics

- `resolved`: completed successfully
- `blocked`: stopped because prerequisites were missing or convergence was not achieved
- `skip`: intentionally skipped because nothing was actionable or configuration disabled execution
- `error`: runtime failure during execution

Supporting semantics:
- `reasonCode` is the stable dictionary key; see `policy/reason-codes.yml` and `docs/ci/reason-codes.md`
- `reason` is free text for operators and may change more often than `reasonCode`
- weekly SLO / MTTR calculations treat `blocked` and `error` as failures, while `resolved` / `skip` remain outside the failure numerator

### 4. Primary operating metrics (`#2374`)

#### 4.1 Blocked rate
- Definition: `summary.byStatus.blocked / summary.totalReports * 100`
- JSON output: `weekly-failure-summary.json` -> `summary.blockedRatePercent`
- Goal: detect rising automation stop frequency early

#### 4.2 Rounds to convergence
- Source data: `metrics.rounds` in `ae-automation-report/v1`
- Aggregate outputs:
  - `summary.convergenceRounds.overall` (`count`, `meanRounds`, `p95Rounds`, `maxRounds`)
  - `summary.convergenceRounds.byTool.<tool>`
- Goal: track whether automated convergence is requiring more retries over time

Example extraction:

```bash
jq '.summary | {blockedRatePercent, convergenceRounds}' artifacts/automation/weekly-failure-summary.json
```

### 5. Log extraction examples

`rg` variant (bash/zsh):

```bash
gh run view <run_id> --repo itdojp/ae-framework --log \
  | rg '^\[ae-automation-report\]' \
  | sed 's/^\[ae-automation-report\] //'
```

`grep` variant (POSIX shell compatible):

```bash
gh run view <run_id> --repo itdojp/ae-framework --log \
  | grep '^\[ae-automation-report\]' \
  | sed 's/^\[ae-automation-report\] //'
```

### 6. Representative operating uses

- Monitoring integration: extract rows where `status in {blocked,error}`
- Failure analysis: classify by `reasonCode`, then use `reason` and `metrics` as supporting context
- Evidence retention: write JSON with `AE_AUTOMATION_REPORT_FILE` and upload as an artifact

Recommended triage order:
1. confirm the workflow/run from `run.workflow`, `run.runId`, and `run.url`
2. inspect `status`, `reasonCode`, `reason`
3. inspect producer-specific `metrics` / `data`
4. move to weekly aggregation if the issue appears recurrent

### 7. Weekly aggregation (Top N failure reasons)

The weekly batch `Automation Observability Weekly` extracts `ae-automation-report/v1` rows from major automation workflow logs and aggregates `error` / `blocked` reasons.

- workflow: `.github/workflows/automation-observability-weekly.yml`
- summary script: `scripts/ci/automation-observability-weekly.mjs`
- alert script: `scripts/ci/automation-observability-alert.mjs`
- artifact: `automation-observability-weekly`
  - `weekly-failure-summary.json`
  - `weekly-alert-summary.json`

Primary inputs:
- `AE_AUTOMATION_REPOSITORY`: target repository; required unless `GITHUB_REPOSITORY` is already available
- `AE_AUTOMATION_OBSERVABILITY_WORKFLOWS`: target workflow names (CSV)
- `AE_AUTOMATION_OBSERVABILITY_SINCE_DAYS`: aggregation window
- `AE_AUTOMATION_OBSERVABILITY_MAX_RUNS_PER_WORKFLOW`: max referenced runs per workflow
- `AE_AUTOMATION_OBSERVABILITY_TOP_N`: Top N count
- `AE_AUTOMATION_OBSERVABILITY_OUTPUT`: summary JSON output path
- `AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT`: success-rate SLO target (%)
- `AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES`: MTTR target (minutes)
- `AE_AUTOMATION_ALERT_SLO_TARGET_PERCENT`: alert threshold override for `slo_breach`
- `AE_AUTOMATION_ALERT_MTTR_TARGET_MINUTES`: alert threshold override for `mttr_breach`
- `AE_AUTOMATION_ALERT_MAX_BLOCKED`: blocked count threshold
- `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES`: consecutive-failure threshold
- `AE_AUTOMATION_ALERT_COOLDOWN_HOURS`: alert cooldown window
- `AE_AUTOMATION_ALERT_ISSUE_NUMBER`: target issue for `issue_comment` alerts
- `AE_AUTOMATION_ALERT_CHANNEL`: `issue_comment` / `dry_run`
- `AE_AUTOMATION_ALERT_DRY_RUN`: evaluate without posting alerts when `true`

Key derived outputs:
- `summary.topFailureReasonCodes`
- `summary.reasonCodeCoveragePercent`
- `summary.slo.successRatePercent`
- `summary.slo.achieved`
- `summary.mttr.meanMinutes`
- `summary.mttr.p95Minutes`
- `summary.mttr.byIncidentType`

Detailed SLO / MTTR semantics are defined in `docs/ci/automation-slo-mttr.md`. Alert conditions, template rules, and suppression semantics are defined in `docs/ci/automation-alerting.md`.

Manual dispatch example:

```bash
gh workflow run "Automation Observability Weekly" \
  --repo itdojp/ae-framework \
  -f since_days=7 \
  -f max_runs_per_workflow=30 \
  -f top_n=5 \
  -f slo_target_percent=95 \
  -f mttr_target_minutes=120 \
  -f alert_issue_number=1963 \
  -f alert_max_blocked=2 \
  -f alert_max_consecutive_failures=3 \
  -f alert_cooldown_hours=24 \
  -f alert_channel=issue_comment
```

### 8. Trace-required aggregation (`#2394`)

For `KvOnce Trace Validation` required-check analysis, narrow the workflow set to `Spec Generate & Model Tests`.

```bash
AE_AUTOMATION_REPOSITORY=itdojp/ae-framework \
AE_AUTOMATION_OBSERVABILITY_WORKFLOWS='Spec Generate & Model Tests' \
AE_AUTOMATION_OBSERVABILITY_SINCE_DAYS=28 \
AE_AUTOMATION_OBSERVABILITY_MAX_RUNS_PER_WORKFLOW=120 \
AE_AUTOMATION_OBSERVABILITY_OUTPUT=artifacts/automation/trace-required-summary.json \
node scripts/ci/automation-observability-weekly.mjs
```

The Go/No-Go threshold and time-window criteria are defined in `docs/ci/trace-required-criteria.md`.

## 日本語

PR自動化系スクリプトの実行結果は、共通フォーマット `ae-automation-report/v1` で出力されます。

### 1. 出力先

- **標準出力**: 1行JSON（prefix: `[ae-automation-report]`）
- **Step Summary**: `GITHUB_STEP_SUMMARY` がある場合に自動追記
- **JSONファイル（任意）**: `AE_AUTOMATION_REPORT_FILE` を設定した場合に保存

運用補足:
- 週次集計の canonical input は標準出力ログです
- 任意の JSON ファイル出力は artifact 保存やローカルデバッグ向けです
- Step Summary は運用者向けの可視化であり、system-of-record ではありません

### 2. 共通スキーマ（概要）

```json
{
  "schemaVersion": "ae-automation-report/v1",
  "generatedAt": "2026-02-13T00:00:00.000Z",
  "tool": "codex-autopilot-lane",
  "mode": "active",
  "status": "blocked",
  "reasonCode": "policy.required_labels_missing",
  "reason": "missing policy labels: run-security, run-ci-extended",
  "prNumber": 123,
  "metrics": {},
  "data": {},
  "run": {
    "workflow": "PR Self-Heal",
    "event": "workflow_dispatch",
    "runId": 21966754908,
    "attempt": 1,
    "url": "https://github.com/itdojp/ae-framework/actions/runs/21966754908",
    "repository": "itdojp/ae-framework",
    "ref": "refs/heads/main",
    "sha": "..."
  }
}
```

主要 field の役割:
- `tool`: tool 単位集計に使う安定 identifier
- `status`: 正規化された運用結果
- `reasonCode`: 機械可読な安定キー
- `reason`: 人手向けの補足説明
- `metrics` / `data`: producer 固有の拡張領域
- `run`: workflow / run provenance。週次相関や証跡リンクで使用

### 3. `status` の目安

- `resolved`: 正常に処理完了
- `blocked`: 条件不一致や未収束で停止
- `skip`: 実行対象なし、または設定によりスキップ
- `error`: 実行時エラー

補足:
- `reasonCode`: 失敗/スキップ理由の分類キー（辞書: `policy/reason-codes.yml`、解説: `docs/ci/reason-codes.md`）
- `reason`: 人間向けの補足（自由記述）
- 週次 SLO / MTTR 集計では `blocked` / `error` を failure、`resolved` / `skip` は failure 分子外として扱います

### 4. 主要運用指標（#2374）

#### 4.1 blocked率
- 定義: `summary.byStatus.blocked / summary.totalReports * 100`
- JSON出力: `weekly-failure-summary.json` の `summary.blockedRatePercent`
- 目的: 自動化停止（blocked）の増加を早期検知する

#### 4.2 収束までのラウンド数
- 元データ: `ae-automation-report/v1` の `metrics.rounds`
- 集計出力:
  - `summary.convergenceRounds.overall`（count / meanRounds / p95Rounds / maxRounds）
  - `summary.convergenceRounds.byTool.<tool>`（同指標）
- 目的: 自動収束に必要な試行回数の増減を追跡する

取得例:

```bash
jq '.summary | {blockedRatePercent, convergenceRounds}' artifacts/automation/weekly-failure-summary.json
```

### 5. ログからの抽出例

`rg` 版（bash/zsh前提）:

```bash
gh run view <run_id> --repo itdojp/ae-framework --log \
  | rg '^\[ae-automation-report\]' \
  | sed 's/^\[ae-automation-report\] //'
```

`grep` 版（POSIX系シェル互換）:

```bash
gh run view <run_id> --repo itdojp/ae-framework --log \
  | grep '^\[ae-automation-report\]' \
  | sed 's/^\[ae-automation-report\] //'
```

### 6. 代表的な運用

- 監視連携: `status in {blocked,error}` を抽出して通知
- 失敗分析: `reasonCode` を先に確認し、その後 `reason` と `metrics` で要因を分類
- 証跡保存: `AE_AUTOMATION_REPORT_FILE` でJSONを生成し artifact 化

推奨するトリアージ順:
1. `run.workflow` / `run.runId` / `run.url` で対象 run を特定
2. `status` / `reasonCode` / `reason` を確認
3. producer 固有の `metrics` / `data` を確認
4. 再発傾向がある場合のみ週次集計へ進む

### 7. 週次集計（失敗理由 Top N）

週次バッチ `Automation Observability Weekly` が、主要自動化WFの実行ログから `ae-automation-report/v1` を抽出し、`error` / `blocked` の理由を集計します。

- workflow: `.github/workflows/automation-observability-weekly.yml`
- script: `scripts/ci/automation-observability-weekly.mjs`
- alert script: `scripts/ci/automation-observability-alert.mjs`
- artifact: `automation-observability-weekly`
  - `weekly-failure-summary.json`（週次集計）
  - `weekly-alert-summary.json`（通知判定結果）

主な入力:
- `AE_AUTOMATION_OBSERVABILITY_WORKFLOWS`: 対象WF名（CSV）
- `AE_AUTOMATION_OBSERVABILITY_SINCE_DAYS`: 集計対象期間（日数）
- `AE_AUTOMATION_OBSERVABILITY_MAX_RUNS_PER_WORKFLOW`: WFごとの参照run上限
- `AE_AUTOMATION_OBSERVABILITY_TOP_N`: Top N件数
- `AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT`: 成功率SLO目標（%）
- `AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES`: MTTR目標（分）
- `AE_AUTOMATION_ALERT_SLO_TARGET_PERCENT`: `slo_breach` 判定しきい値（未設定時は `AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT` を利用）
- `AE_AUTOMATION_ALERT_MTTR_TARGET_MINUTES`: `mttr_breach` 判定しきい値（未設定時は `AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES` を利用）
- `AE_AUTOMATION_ALERT_MAX_BLOCKED`: blocked 件数しきい値
- `AE_AUTOMATION_ALERT_MAX_CONSECUTIVE_FAILURES`: 連続失敗しきい値
- `AE_AUTOMATION_ALERT_COOLDOWN_HOURS`: 通知クールダウン
- `AE_AUTOMATION_ALERT_ISSUE_NUMBER`: Issue comment 通知先（通知運用Issueを Repository Variable として固定）
- `AE_AUTOMATION_ALERT_CHANNEL`: `issue_comment` / `dry_run`
- `AE_AUTOMATION_ALERT_DRY_RUN`: `true` の場合は通知を投稿せず判定のみ

出力に追加される主要指標:
- `summary.topFailureReasonCodes`: 失敗（`error`/`blocked`）の reasonCode Top N（安定キー、辞書: `policy/reason-codes.yml`）
- `summary.reasonCodeCoveragePercent`: 失敗のうち reasonCode が付与されている割合（%）
- `summary.slo.successRatePercent`: 期間内成功率
- `summary.slo.achieved`: SLO達成可否
- `summary.mttr.meanMinutes` / `summary.mttr.p95Minutes`: 復旧時間の平均/P95
- `summary.mttr.byIncidentType`: インシデント種別別の復旧統計

定義の詳細:
- `docs/ci/automation-slo-mttr.md`

手動実行例:

```bash
gh workflow run "Automation Observability Weekly" \
  --repo itdojp/ae-framework \
  -f since_days=7 \
  -f max_runs_per_workflow=30 \
  -f top_n=5 \
  -f slo_target_percent=95 \
  -f mttr_target_minutes=120 \
  -f alert_issue_number=1963 \
  -f alert_max_blocked=2 \
  -f alert_max_consecutive_failures=3 \
  -f alert_cooldown_hours=24 \
  -f alert_channel=issue_comment
```

通知条件・テンプレート・抑止ルールの詳細は `docs/ci/automation-alerting.md` を参照してください。

### 8. trace Required化向け集計（#2394）

`KvOnce Trace Validation` の Required 化判定に使う場合は、対象 workflow を `Spec Generate & Model Tests` に絞って集計します。

```bash
AE_AUTOMATION_REPOSITORY=itdojp/ae-framework \
AE_AUTOMATION_OBSERVABILITY_WORKFLOWS='Spec Generate & Model Tests' \
AE_AUTOMATION_OBSERVABILITY_SINCE_DAYS=28 \
AE_AUTOMATION_OBSERVABILITY_MAX_RUNS_PER_WORKFLOW=120 \
AE_AUTOMATION_OBSERVABILITY_OUTPUT=artifacts/automation/trace-required-summary.json \
node scripts/ci/automation-observability-weekly.mjs
```

判定基準（期間/しきい値/Go-NoGo）は `docs/ci/trace-required-criteria.md` を参照。
