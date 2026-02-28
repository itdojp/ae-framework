# Release Engineering (Policy v1 / Post-deploy Verify)

Issue: `#2288`

本ドキュメントは、`policy/release-policy.yml` を SSOT としてリリース判定を標準化する運用手順を定義します。

## 1. 目的

- デプロイ実行とリリース判断を分離する。
- ロールアウト/ロールバック条件を機械可読に統一する。
- 判定結果を `artifacts/release/**` に証跡として保存する。

## 2. Source of Truth

- Policy: `policy/release-policy.yml`
- Schema: `schema/release-policy.schema.json`
- Schema fixture: `fixtures/release/sample.release-policy.json`
- Sample verify inputs（ローカル検証用。workflow_dispatch では利用不可）:
  - `fixtures/release/sample.metrics-snapshot.json`
  - `fixtures/release/sample.synthetic-checks.json`

## 3. Policy構造（`ae-release-policy/v1`）

- `rolloutStrategy`
  - `mode`: `canary | progressive | blue-green`
  - `percentSteps`, `pauseSeconds`, `maxDurationSeconds`
- `healthSignals`
  - メトリクスキー、warning/critical 閾値、比較方向（`lte` / `gte`）
  - `lte`: warning <= critical
  - `gte`: warning >= critical
- `rollbackPolicy`
  - `enabled`, `trigger`（`any-critical | all-critical | manual`）, `dryRun`, `hook`
- `requiredEvidence`
  - 例: `postDeployVerify`, `qualityGates`, `conformanceSummary`
- `environments`
  - 環境ごとの rollout/evidence 上書き

## 4. CLI運用

前提:
- Node.js `>=20.11 <23`
- pnpm `10.x`

### 4.1 Release Plan 生成

```bash
pnpm run ae-framework -- release plan \
  --policy policy/release-policy.yml \
  --environment staging \
  --feature checkout \
  --output-dir artifacts/release
```

出力:
- `artifacts/release/release-plan.json`
- `artifacts/release/release-plan.md`

### 4.2 Post-deploy Verify

```bash
pnpm run ae-framework -- release verify \
  --policy policy/release-policy.yml \
  --environment staging \
  --metrics fixtures/release/sample.metrics-snapshot.json \
  --synthetic-checks fixtures/release/sample.synthetic-checks.json \
  --output-dir artifacts/release
```

任意入力:
- `--trace-bundle <path>`: telemetry-as-context の trace bundle
- `--synthetic-checks <path>`: 合成監視/スモークテスト結果

出力:
- `artifacts/release/post-deploy-verify.json`
- `artifacts/release/post-deploy-verify.md`

判定:
- `status`: `pass | warn | fail`
- `rollbackRecommended`: `status=fail` かつ rollback trigger 条件一致時に `true`

## 5. GitHub Actions: `post-deploy-verify.yml`

Workflow:
- `.github/workflows/post-deploy-verify.yml`
- trigger: `workflow_dispatch`

主な inputs:
- `environment`: `staging | production`
- `metrics_snapshot_path`: 必須
- `trace_bundle_path`: 任意
- `synthetic_checks_path`: 任意
- `fail_on_verify_fail`: `true` の場合、`status=fail` でジョブ失敗
- `run_rollback_hook_dry_run`: `true` の場合、fail 時に rollback hook を dry-run 実行
- `rollback_hook_args`: dry-run 実行時の追加引数

CLI 実行例:

```bash
gh workflow run post-deploy-verify.yml \
  -f environment=staging \
  -f metrics_snapshot_path=artifacts/observability/metrics-snapshot.json \
  -f synthetic_checks_path=artifacts/observability/synthetic-checks.json \
  -f fail_on_verify_fail=true \
  -f run_rollback_hook_dry_run=false
```

Web UI 実行:
1. GitHub の `Actions` タブを開く
2. `post-deploy-verify` workflow を選択
3. `Run workflow` で input を指定して実行

成果物:
- `post-deploy-verify-artifacts` artifact（`artifacts/release/**`）
- Step Summary（status, fail/warn/unknown, missing evidence, 詳細 report）

## 6. ロールバック実行責務

- 本ワークフローは既定で「判定 + 証跡保存」を行う。
- rollback hook は `run_rollback_hook_dry_run=true` の場合のみ dry-run 実行。
- 実際のロールバック実行は各プロダクト側の deploy pipeline に委譲する。

## 7. Telemetry-as-Context との接続

推奨フロー:
1. `ae conformance ingest` で trace bundle 生成
2. `ae release verify --trace-bundle <bundle>` で evidence 評価
3. `post-deploy-verify.json` を release 判定証跡として保存

## 8. ガバナンス

- `policy/release-policy.yml` は `policy/risk-policy.yml` の high-risk path として扱う。
- 変更時は schema 検証（`scripts/ci/validate-json.mjs`）を通過させる。
