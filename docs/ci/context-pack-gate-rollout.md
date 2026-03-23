---
docRole: ssot
lastVerified: '2026-03-23'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Context Pack Gate Rollout（non-blocking -> blocking）

Issue: #2258

## 1. 目的
圏論的メタモデル検証（Context Pack validator群）の CI 運用を、non-blocking から blocking へ段階導入する。

## 2. 現状棚卸し（non-blocking 対象と依存ジョブ）

一次情報:
- `.github/workflows/context-pack-quality-gate.yml`
- `scripts/context-pack/run-e2e-fixture.mjs`
- `scripts/ci/context-pack-gate-observability.mjs`

| ジョブ/ステップ | 依存 | 既定モード | blocking 化トリガー |
| --- | --- | --- | --- |
| `gate` | なし | report-only 判定 | `enforce-context-pack` ラベル / `CONTEXT_PACK_ENFORCE_MAIN=1` / dispatch strict |
| `Run Context Pack dependency boundary checks` | `gate` | report-only（違反は warn 出力） | `gate.strict == true` のとき違反で fail |
| `context-pack-e2e` | `gate` | non-blocking (`continue-on-error`) | `gate.strict == true` のとき blocking |
| `Observe rollout metrics` | `context-pack-e2e` 内 | non-blocking | なし（常に観測のみ） |

## 3. 観測指標（判定基準）

観測期間: 直近 14 日（初期値）

- 失敗率（`failureRatePercent`）
  - 式: `failedRuns / totalRuns * 100`
  - 合格基準: `<= 5%`
- 失敗再現率（`reproductionRatePercent`）
  - 式: 「同一 SHA の複数 run のうち、初回失敗後に再度失敗した割合」
  - 合格基準: `>= 80%`（失敗が再現できる = 診断容易）
- MTTR（`mttr.meanMinutes`）
  - 式: 同一ブランチで失敗開始から次の成功までの平均復旧時間
  - 合格基準: `<= 120 分`
- サンプル数
  - 合格基準: `totalRuns >= 20`

実測は次コマンドで生成する。

```bash
pnpm -s run ci:context-pack:observe -- \
  --repo itdojp/ae-framework \
  --workflow-id context-pack-quality-gate.yml \
  --days 14 \
  --output-json artifacts/context-pack/context-pack-gate-observability.json \
  --output-md artifacts/context-pack/context-pack-gate-observability.md
```

## 4. 段階導入手順

1. **Phase A（既定）**
   - PR/Push で `context-pack-e2e` を実行し、report-only で観測する。
2. **Phase B（PR限定 strict）**
   - 対象 PR に `enforce-context-pack` を付与し、blocking として運用する。
3. **Phase C（main strict）**
   - Repository Variable `CONTEXT_PACK_ENFORCE_MAIN=1` を設定し、main で常時 blocking 化する。
4. **Phase D（Branch Protection）**
   - Required checks に `context-pack-e2e` を追加して merge gate に組み込む。

## 5. ロールバック条件と手順

### ロールバック条件
- 失敗率が 5% を連続 3 日で超過
- MTTR 平均が 120 分を連続 3 日で超過
- `unresolvedFailureStreaks > 0` が 24 時間以上継続

### ロールバック手順
1. Branch protection で `context-pack-e2e` の Required を一時解除
2. `CONTEXT_PACK_ENFORCE_MAIN=0` に戻す
3. PR 側は `enforce-context-pack` ラベルを外す
4. 原因修正後、Phase B から再開

## 6. 運用メモ

- E2E fixture は `fixtures/context-pack/e2e` を SSOT とする。
- 実行レポートは `artifacts/context-pack/` 配下に保存される。
- 依存境界チェックのレポートは `artifacts/context-pack/deps-summary.json` / `artifacts/context-pack/deps-summary.md` として保存される。
- 観測レポート JSON/Markdown は同ディレクトリに出力され、PR Step Summary にも転記される。


## English

This document defines the staged rollout plan for promoting the Context Pack validator group from non-blocking observation to blocking CI enforcement.

### 1. Purpose
Promote the category-theory-oriented Context Pack validators from report-only execution to blocking CI checks without introducing unstable branch protection.

### 2. Current inventory (report-only targets and dependent jobs)
Primary implementation references:
- `.github/workflows/context-pack-quality-gate.yml`
- `scripts/context-pack/run-e2e-fixture.mjs`
- `scripts/ci/context-pack-gate-observability.mjs`

| Job / step | Depends on | Default mode | Becomes blocking when |
| --- | --- | --- | --- |
| `gate` | none | report-only judgement | `enforce-context-pack` label, `CONTEXT_PACK_ENFORCE_MAIN=1`, or strict workflow dispatch |
| `Run Context Pack dependency boundary checks` | `gate` | report-only (`warn` on violations) | fails when `gate.strict == true` |
| `context-pack-e2e` | `gate` | non-blocking (`continue-on-error`) | blocking when `gate.strict == true` |
| `Observe rollout metrics` | inside `context-pack-e2e` | non-blocking | never; observation only |

### 3. Observability metrics and acceptance thresholds
Recommended observation window: the latest 14 days.

- Failure rate (`failureRatePercent`)
  - Formula: `failedRuns / totalRuns * 100`
  - Pass threshold: `<= 5%`
- Reproduction rate (`reproductionRatePercent`)
  - Formula: percentage of SHAs that fail again after the first failure within repeated runs
  - Pass threshold: `>= 80%`
- MTTR (`mttr.meanMinutes`)
  - Formula: average time from the first failure to the next success on the same branch
  - Pass threshold: `<= 120` minutes
- Sample size
  - Pass threshold: `totalRuns >= 20`

Generate the observation report with:

```bash
pnpm -s run ci:context-pack:observe -- \
  --repo itdojp/ae-framework \
  --workflow-id context-pack-quality-gate.yml \
  --days 14 \
  --output-json artifacts/context-pack/context-pack-gate-observability.json \
  --output-md artifacts/context-pack/context-pack-gate-observability.md
```

### 4. Phased rollout procedure
1. **Phase A (default)**
   - Run `context-pack-e2e` on PRs and pushes, and observe it in report-only mode.
2. **Phase B (strict on selected PRs)**
   - Add the `enforce-context-pack` label to target PRs and run the validators as blocking checks.
3. **Phase C (strict on `main`)**
   - Set repository variable `CONTEXT_PACK_ENFORCE_MAIN=1` to enforce blocking behavior on `main`.
4. **Phase D (branch protection)**
   - Add `context-pack-e2e` to required checks after the signal remains stable.

### 5. Rollback conditions and procedure
#### Rollback conditions
- Failure rate exceeds `5%` for three consecutive days
- Mean MTTR exceeds `120` minutes for three consecutive days
- `unresolvedFailureStreaks > 0` continues for more than 24 hours

#### Rollback procedure
1. Temporarily remove `context-pack-e2e` from branch protection required checks.
2. Reset `CONTEXT_PACK_ENFORCE_MAIN=0`.
3. Remove the `enforce-context-pack` label from PRs.
4. Re-enter at Phase B after the root cause is fixed.

### 6. Operational notes
- Use `fixtures/context-pack/e2e` as the SSOT for the E2E fixture set.
- Runtime reports are stored under `artifacts/context-pack/`.
- Dependency boundary reports are written to `artifacts/context-pack/deps-summary.json` and `artifacts/context-pack/deps-summary.md`.
- Observation JSON/Markdown reports are written to the same directory and appended to the PR step summary.
