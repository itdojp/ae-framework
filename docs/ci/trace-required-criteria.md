---
docRole: ssot
lastVerified: '2026-03-11'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Trace Validation Required化 判定基準（#2394）

目的:
- OTel/trace 検証（`KvOnce Trace Validation`）を branch protection の Required check に昇格する Go/No-Go 判定を、再現可能な指標で運用する。

一次情報:
- `.github/workflows/spec-generate-model.yml`
- `scripts/ci/automation-observability-weekly.mjs`
- `.github/branch-protection.main.verify-lite-trace-noreview.json`
- `docs/ci/automation-rollback-runbook.md`

## 1. 判定対象

- check context: `KvOnce Trace Validation`
- 観測単位: `ae-automation-report/v1`（`tool=kvonce-trace-validation`）
- 観測期間: 直近 28 日（固定）

## 2. Go/No-Go 基準

全条件を同時に満たした場合のみ **Go** とする。

| 区分 | 指標 | 取得元 | しきい値（Go） |
| --- | --- | --- | --- |
| 期間 | 観測期間 | `config.sinceDays` | `28` 日 |
| サンプル数 | `totalReports` | `summary.totalReports` | `>= 20` |
| 失敗率 | `failureRatePercent = totalFailures / totalReports * 100` | `summary.totalFailures`, `summary.totalReports` | `<= 5%` |
| 復旧時間 | `mttr.meanMinutes` | `summary.mttr.meanMinutes` | `<= 120` 分 |
| 未復旧件数 | `mttr.unresolvedOpenIncidents` | `summary.mttr.unresolvedOpenIncidents` | `= 0` |
| 再現性（連続失敗） | `maxConsecutiveFailures` | `summary.maxConsecutiveFailures` | `<= 2` |

補足:
- 失敗は `status in ['error','blocked']` を採用する（`automation-observability-weekly` の既定）。
- 失敗率は小数第2位まで丸めて評価する。

## 3. automation-observability からの集計手順

### 3.1 事前確認（trace report の存在確認）

```bash
gh run view <run_id> --repo itdojp/ae-framework --log \
  | rg '^\[ae-automation-report\].*"tool":"kvonce-trace-validation"'
```

### 3.2 28日集計の生成

```bash
AE_AUTOMATION_REPOSITORY=itdojp/ae-framework \
AE_AUTOMATION_OBSERVABILITY_WORKFLOWS='Spec Generate & Model Tests' \
AE_AUTOMATION_OBSERVABILITY_SINCE_DAYS=28 \
AE_AUTOMATION_OBSERVABILITY_MAX_RUNS_PER_WORKFLOW=120 \
AE_AUTOMATION_OBSERVABILITY_OUTPUT=artifacts/automation/trace-required-summary.json \
node scripts/ci/automation-observability-weekly.mjs
```

### 3.3 判定用メトリクス抽出

```bash
jq '{
  sinceDays: .config.sinceDays,
  totalReports: .summary.totalReports,
  totalFailures: .summary.totalFailures,
  failureRatePercent: (
    if .summary.totalReports == 0 then null
    else ((.summary.totalFailures / .summary.totalReports) * 100 * 100 | round) / 100
    end
  ),
  mttrMeanMinutes: .summary.mttr.meanMinutes,
  unresolvedOpenIncidents: .summary.mttr.unresolvedOpenIncidents,
  maxConsecutiveFailures: .summary.maxConsecutiveFailures
}' artifacts/automation/trace-required-summary.json
```

### 3.4 Go/No-Go の機械判定

```bash
jq 'def failure_rate:
      if .summary.totalReports == 0 then 999
      else ((.summary.totalFailures / .summary.totalReports) * 100 * 100 | round) / 100
      end;
    {
      go:
        (.config.sinceDays == 28) and
        (.summary.totalReports >= 20) and
        (failure_rate <= 5) and
        ((.summary.mttr.meanMinutes // 999999) <= 120) and
        ((.summary.mttr.unresolvedOpenIncidents // 999999) == 0) and
        ((.summary.maxConsecutiveFailures // 999999) <= 2),
      failureRatePercent: failure_rate
    }' artifacts/automation/trace-required-summary.json
```

## 4. Branch protection preset 更新案

- 追加 preset: `.github/branch-protection.main.verify-lite-trace-noreview.json`
- Required contexts:
  - `verify-lite`
  - `policy-gate`
  - `gate`
  - `KvOnce Trace Validation`

適用は Go 判定後に `branch-protection-apply` workflow または `scripts/admin/apply-branch-protection.mjs` で実施する。  
No-Go の間は既存 preset（`branch-protection.main.verify-lite-noreview.json`）を維持する。

## 5. ロールバック条件

以下のいずれかに該当した時点で、Required からの切り戻し（rollback）を実施する。

- 失敗率が `> 5%` を 2 週連続で超過
- `mttr.meanMinutes > 120` を 2 週連続で超過
- `unresolvedOpenIncidents > 0` が 24 時間以上継続
- `maxConsecutiveFailures > 2` が同一週内で発生

手順は `docs/ci/automation-rollback-runbook.md` の「4.5 trace required rollback」を参照。
