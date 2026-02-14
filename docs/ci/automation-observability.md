# Automation Observability

PR自動化系スクリプトの実行結果は、共通フォーマット `ae-automation-report/v1` で出力されます。

一次情報:
- `scripts/ci/lib/automation-report.mjs`
- `scripts/ci/pr-self-heal.mjs`
- `scripts/ci/codex-autopilot-lane.mjs`
- `scripts/ci/auto-merge-enabler.mjs`
- `scripts/ci/copilot-auto-fix.mjs`

## 1. 出力先

- **標準出力**: 1行JSON（prefix: `[ae-automation-report]`）
- **Step Summary**: `GITHUB_STEP_SUMMARY` がある場合に自動追記
- **JSONファイル（任意）**: `AE_AUTOMATION_REPORT_FILE` を設定した場合に保存

## 2. 共通スキーマ（概要）

```json
{
  "schemaVersion": "ae-automation-report/v1",
  "generatedAt": "2026-02-13T00:00:00.000Z",
  "tool": "pr-self-heal",
  "mode": "dry-run",
  "status": "resolved",
  "reason": "completed",
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

## 3. `status` の目安

- `resolved`: 正常に処理完了
- `blocked`: 条件不一致や未収束で停止
- `skip`: 実行対象なし、または設定によりスキップ
- `error`: 実行時エラー

## 4. ログからの抽出例

`rg` 版（bash/zsh前提）:

```bash
gh run view <run_id> --repo itdojp/ae-framework --log \
  | rg '^\\[ae-automation-report\\]' \
  | sed 's/^\\[ae-automation-report\\] //'
```

`grep` 版（POSIX系シェル互換）:

```bash
gh run view <run_id> --repo itdojp/ae-framework --log \
  | grep '^\[ae-automation-report\]' \
  | sed 's/^\[ae-automation-report\] //'
```

## 5. 代表的な運用

- 監視連携: `status != resolved` を抽出して通知
- 失敗分析: `reason` と `metrics` で要因を分類
- 証跡保存: `AE_AUTOMATION_REPORT_FILE` でJSONを生成し artifact 化

## 6. 週次集計（失敗理由 Top N）

週次バッチ `Automation Observability Weekly` が、主要自動化WFの実行ログから `ae-automation-report/v1` を抽出し、`error` / `blocked` の理由を集計します。

- workflow: `.github/workflows/automation-observability-weekly.yml`
- script: `scripts/ci/automation-observability-weekly.mjs`
- artifact: `automation-observability-weekly`（`weekly-failure-summary.json`）

主な入力:
- `AE_AUTOMATION_OBSERVABILITY_WORKFLOWS`: 対象WF名（CSV）
- `AE_AUTOMATION_OBSERVABILITY_SINCE_DAYS`: 集計対象期間（日数）
- `AE_AUTOMATION_OBSERVABILITY_MAX_RUNS_PER_WORKFLOW`: WFごとの参照run上限
- `AE_AUTOMATION_OBSERVABILITY_TOP_N`: Top N件数
- `AE_AUTOMATION_OBSERVABILITY_SLO_TARGET_PERCENT`: 成功率SLO目標（%）
- `AE_AUTOMATION_OBSERVABILITY_MTTR_TARGET_MINUTES`: MTTR目標（分）

出力に追加される主要指標:
- `summary.slo.successRatePercent`: 期間内成功率（`1 - failures/totalReports`）
- `summary.slo.achieved`: SLO達成可否
- `summary.mttr.meanMinutes` / `summary.mttr.p95Minutes`: 復旧時間の平均/P95
- `summary.mttr.byIncidentType`: インシデント種別（`rate_limit_429` / `review_gate` / `behind_loop` / `blocked` / `other`）別の復旧統計

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
  -f mttr_target_minutes=120
```
