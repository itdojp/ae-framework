# Workflow Inventory (Issue #2031 / Phase 3)

最終更新: 2026-02-17

対象: `.github/workflows/*.yml`（51 files）

## 1. 調査方法

実行コマンド（ローカル再現用）:

- workflow 一覧/トリガー抽出: `node + yaml` で `name` と `on` を集計
- reusable 呼び出し関係抽出: `jobs.<job>.uses` が `./.github/workflows/*.yml` のものを抽出
- Branch protection 必須チェック抽出: `gh api repos/itdojp/ae-framework/branches/main/protection --jq '.required_status_checks.checks[].context'`

## 2. 必須/任意の現状（main branch protection 基準）

main の Required checks は次の 2 つのみ。

| Required check context | 対応 workflow | 判定 |
|---|---|---|
| `verify-lite` | `verify-lite.yml` | 必須 |
| `gate` | `copilot-review-gate.yml` | 必須 |

補足:

- 上記以外の workflow は、実行されても merge blocking の必須条件ではない（2026-02-17 時点）。
- ただし個別 workflow 内で failure を返す場合、運用上の判断で対応対象になる。

## 3. workflow_dispatch 入力棚卸し（主要運用フロー）

`workflow_dispatch` 対応 workflow の入力一覧:

| Workflow file | Inputs |
|---|---|
| `automation-observability-weekly.yml` | `since_days`, `max_runs_per_workflow`, `top_n`, `slo_target_percent`, `mttr_target_minutes`, `alert_issue_number`, `alert_max_blocked`, `alert_max_consecutive_failures`, `alert_cooldown_hours`, `alert_channel` |
| `branch-protection-apply.yml` | `preset`, `branch` |
| `codex-autopilot-lane.yml` | `pr_number`, `dry_run`, `max_rounds` |
| `copilot-review-gate.yml` | `pr_number` |
| `coverage-check.yml` | `strict` |
| `docker-tests.yml` | `target_sha`, `service_filter` |
| `flake-detect.yml` | `mode`, `workflow_file`, `eligibility_artifact`, `eligibility_path`, `dry_run` |
| `formal-aggregate.yml` | `source_run_id`, `pr_number`, `strict_formal_summary_v1` |
| `formal-verify.yml` | `target`, `tlaFile`, `engine`, `solver`, `alloyJar`, `tlaToolsJar` |
| `minimal-pipeline.yml` | `enforce_lint` |
| `mutation-quick.yml` | `mutate`, `time_limit`, `base_ref` |
| `nightly.yml` | `mode` |
| `parallel-test-execution.yml` | `mode`, `suites`, `exclude_suites`, `max_concurrency`, `use_container_unit` |
| `pr-ci-status-comment.yml` | `mode`, `pr_number`, `enable_auto_merge` |
| `pr-self-heal.yml` | `pr_number`, `dry_run`, `max_rounds` |
| `pr-verify.yml` | `trigger`, `pr_labels`, `pr_is_fork`, `pr_number` |
| `sbom-generation.yml` | `include_vulnerabilities` |
| `spec-generate-model.yml` | `kvonce_otlp_payload`, `kvonce_payload_artifact`, `kvonce_otlp_payload_url` |
| `validate-artifacts-ajv.yml` | `strict` |
| `verify.yml` | `trigger`, `pr_labels`, `pr_number`, `pr_head_sha` |

## 4. 重複/統合余地（呼び出し関係ベース）

主要な再利用・重複パターン:

1. `ci-core.yml` に job 実行定義が集中
   - 呼び出し元: `ci-fast.yml`, `quality-gates-centralized.yml`, `nightly.yml`
   - 影響: setup 差分や cache 方針の更新点が複数 workflow に波及
2. `ci.yml` が複数 reusable workflow をオーケストレーション
   - `spec-validation.yml`, `ci-extended.yml`, `hermetic-ci.yml`, `parallel-test-execution.yml`, `podman-smoke.yml`, `ci-fast.yml`, `pr-verify.yml`, `verify.yml`, `ae-ci.yml`
   - 影響: エントリポイントとして責務過多になりやすい
3. spec 系の段階呼び出し
   - `spec-validation.yml` → `fail-fast-spec-validation.yml` / `spec-check.yml` / `validate-artifacts-ajv.yml`
4. formal 集約の段階呼び出し
   - `formal-verify.yml` → `formal-aggregate.yml`
5. flake 系の段階呼び出し
   - `flake-detect.yml` → `flake-stability.yml`

## 5. 必須/任意/レポート分類（運用上の整理）

`core`（常時運用の中心）:

- `verify-lite.yml`（Required）
- `copilot-review-gate.yml`（Required）
- `ci.yml`（総合入口）
- `ci-fast.yml` / `pr-verify.yml` / `verify.yml`（主要検証）
- `workflow-lint.yml` / `coverage-check.yml` / `spec-validation.yml`（品質ガード）

`optional`（ラベル/dispatch/夜間で実行）:

- `ci-extended.yml`, `parallel-test-execution.yml`, `hermetic-ci.yml`
- `formal-verify.yml`, `formal-aggregate.yml`, `spec-check.yml`
- `security.yml`, `sbom-generation.yml`, `flake-detect.yml`, `flake-stability.yml`
- `podman-smoke.yml`, `docker-tests.yml`, `mutation-quick.yml`, `spec-generate-model.yml`

`report / operations`（監視・コメント・復旧）:

- `pr-ci-status-comment.yml`, `pr-self-heal.yml`, `ci-auto-rerun-failed.yml`
- `automation-observability-weekly.yml`, `adapter-thresholds.yml`
- `branch-protection-apply.yml`, `release-quality-artifacts.yml`, `triage.yml`

## 6. 全 workflow 一覧（イベント別）

### 6.1 `pull_request`（22）

`adapter-thresholds.yml`, `cedar-quality-gates.yml`, `ci.yml`, `codegen-drift-check.yml`, `codex-autopilot-lane.yml`, `copilot-review-gate.yml`, `coverage-check.yml`, `formal-verify.yml`, `grafana-dashboards.yml`, `lean-proof.yml`, `lockfile-reproducibility.yml`, `phase6-validation.yml`, `pr-ci-status-comment.yml`, `quality-gates-centralized.yml`, `sbom-generation.yml`, `security.yml`, `spec-generate-model.yml`, `spec-validation.yml`, `testing-ddd-scripts.yml`, `verify-lite.yml`, `verify.yml`, `workflow-lint.yml`

### 6.2 `push`（13）

`ci.yml`, `codegen-drift-check.yml`, `coverage-check.yml`, `lean-proof.yml`, `lockfile-reproducibility.yml`, `quality-gates-centralized.yml`, `release.yml`, `sbom-generation.yml`, `security.yml`, `spec-validation.yml`, `testing-ddd-scripts.yml`, `verify-lite.yml`, `workflow-lint.yml`

### 6.3 `schedule`（9）

`automation-observability-weekly.yml`, `ci.yml`, `docker-tests.yml`, `flake-detect.yml`, `grafana-dashboards.yml`, `nightly.yml`, `pr-ci-status-comment.yml`, `pr-self-heal.yml`, `security.yml`

### 6.4 `workflow_dispatch`（35）

`ae-ci.yml`, `automation-observability-weekly.yml`, `branch-protection-apply.yml`, `cedar-quality-gates.yml`, `ci-fast.yml`, `ci.yml`, `codex-autopilot-lane.yml`, `copilot-review-gate.yml`, `coverage-check.yml`, `docker-tests.yml`, `fail-fast-spec-validation.yml`, `flake-detect.yml`, `formal-aggregate.yml`, `formal-verify.yml`, `grafana-dashboards.yml`, `hermetic-ci.yml`, `lockfile-reproducibility.yml`, `minimal-pipeline.yml`, `mutation-quick.yml`, `nightly.yml`, `parallel-test-execution.yml`, `podman-smoke.yml`, `pr-ci-status-comment.yml`, `pr-self-heal.yml`, `pr-verify.yml`, `release-quality-artifacts.yml`, `sbom-generation.yml`, `security.yml`, `spec-check.yml`, `spec-generate-model.yml`, `spec-validation.yml`, `validate-artifacts-ajv.yml`, `verify-lite.yml`, `verify.yml`, `webapi-sample-ci.yml`

### 6.5 `workflow_call`（20）

`ae-ci.yml`, `ci-core.yml`, `ci-extended.yml`, `ci-fast.yml`, `ci.yml`, `codegen-drift-check.yml`, `fail-fast-spec-validation.yml`, `flake-stability.yml`, `formal-aggregate.yml`, `hermetic-ci.yml`, `parallel-test-execution.yml`, `podman-smoke.yml`, `pr-verify.yml`, `quality-gates-centralized.yml`, `release-quality-artifacts.yml`, `sbom-generation.yml`, `spec-check.yml`, `spec-validation.yml`, `validate-artifacts-ajv.yml`, `verify.yml`

### 6.6 `issue_comment`（4）

`agent-commands.yml`, `codex-autopilot-lane.yml`, `copilot-review-gate.yml`, `slash-commands.yml`

### 6.7 `workflow_run`（2）

`ci-auto-rerun-failed.yml`, `pr-self-heal.yml`

### 6.8 `pull_request_review`（2）

`copilot-auto-fix.yml`, `copilot-review-gate.yml`

### 6.9 `issues`（1）

`triage.yml`

## 7. 次アクション（Phase 3）

1. `core / optional / report` を前提に、`ci.yml` と周辺 reusable workflow の責務境界を明文化
2. Required 化候補（`workflow-lint`, `coverage-check`）の段階導入条件を定義
3. 429対策（retry/backoff/sleep）を `scripts/ci/lib` 共通化し、呼び出し workflow を統一

