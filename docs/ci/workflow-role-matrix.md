---
docRole: ssot
lastVerified: '2026-03-25'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Workflow Role Matrix (core / optional / report)

This document classifies `.github/workflows/*.yml` by operational role so required and non-required workflows are managed consistently. / 本ドキュメントは、`.github/workflows/*.yml` を運用ロールで分類し、Required / 非Required workflow を一貫して管理するための基準を定義します。

> Language / 言語: English | 日本語

---

## English

Update summary: 2026-03-14

Scope: operational role mapping for `.github/workflows/*.yml` (Issue #2031 / Phase 3).

Note (2026-03-04):
- for the proposed regrouping into `pr-core` / `pr-extended` / `maintenance` / `release-assurance`, see `docs/ci/workflow-topology-mapping-2026-03-04.md`

### 1. Purpose

- clarify workflow responsibilities as `core`, `optional`, or `report`
- keep the boundary between required checks and non-required workflows operationally consistent
- provide a stable decision baseline when workflows are consolidated or removed

### 2. Role definitions

- `core`: daily PR quality gates that require immediate response on failure
- `optional`: heavier validations that run through label / dispatch / schedule
- `report`: observability, notification, self-heal, or other supporting automation

Notes:

- as of 2026-03-14, the required checks on `main` are `verify-lite`, `policy-gate`, and `gate`
- `gate` is the status-check name emitted by `copilot-review-gate.yml`
- after Copilot Auto Fix, gate re-evaluation dispatch is handled by `agent-commands.yml`, not by `copilot-review-gate.yml`

### 3. Current mapping (major workflows)

#### 3.1 core

| Workflow | Primary purpose | Trigger |
|---|---|---|
| `verify-lite.yml` | lightweight required gate (types / build / baseline validation) | PR / push / dispatch |
| `policy-gate.yml` | required checks / risk policy / OPA shadow compare decisions | PR / review / workflow_run / dispatch |
| `copilot-review-gate.yml` | Copilot review presence / resolution confirmation | PR / review / dispatch |
| `ci.yml` | aggregate orchestration entrypoint | PR / push / schedule / dispatch |
| `ci-fast.yml` | fast validation batch | call / dispatch |
| `pr-verify.yml` | standard PR validation entrypoint | call / dispatch |
| `verify.yml` | integrated traceability / formal validation entrypoint | PR / call / dispatch |
| `workflow-lint.yml` | workflow quality rule validation | PR / push |
| `docs-doctest.yml` | lightweight doctest for README/docs index plus weekly full doctest | PR(path) / push(main,path) / schedule / dispatch |
| `coverage-check.yml` | coverage threshold gate | PR / push / dispatch |
| `spec-validation.yml` | spec fail-fast / schema validation | PR / push / call / dispatch |

#### 3.2 optional

| Workflow | Primary purpose | Trigger |
|---|---|---|
| `ci-extended.yml` | integration / property / MBT / mutation suites | call |
| `parallel-test-execution.yml` | parallel test execution optimization | call / dispatch |
| `hermetic-ci.yml` | hermetic reproducibility validation | call / dispatch |
| `formal-verify.yml` | opt-in formal tooling | PR(label) / dispatch |
| `formal-aggregate.yml` | aggregate formal results | call / dispatch |
| `security.yml` | heavier security validation | PR(label) / push / schedule / dispatch |
| `sbom-generation.yml` | SBOM generation and vulnerability collection | PR / push / call / dispatch |
| `context-pack-quality-gate.yml` | Context Pack E2E validation during staged rollout | PR(path) / push(main) / dispatch |
| `flake-detect.yml` / `flake-stability.yml` | flake detection / retry stability | schedule / dispatch / call |
| `podman-smoke.yml` / `docker-tests.yml` | container execution validation | call / dispatch / schedule |
| `mutation-quick.yml` | mutation quick validation | dispatch |

#### 3.3 report

| Workflow | Primary purpose | Trigger |
|---|---|---|
| `pr-ci-status-comment.yml` | PR-facing CI summary / auto-merge control | PR / schedule / dispatch |
| `pr-self-heal.yml` | automated recovery on failure | workflow_run / schedule / dispatch |
| `ci-auto-rerun-failed.yml` | automatic rerun of failed jobs | workflow_run |
| `automation-observability-weekly.yml` | weekly SLO / MTTR observation for automation | schedule / dispatch |
| `adapter-thresholds.yml` | threshold reporting (report-only) | PR |
| `branch-protection-apply.yml` | branch-protection apply operations | dispatch |

### 4. Operating rules

1. Whenever a new workflow is added, add its role to this document.
2. Promote a workflow to `core` only after confirming reproducibility, runtime, and false-positive rate.
3. Revisit high-frequency `optional` workflows quarterly as potential `core` integration candidates.
4. Do not include `report` workflows in PR merge-blocking conditions.

### 5. Related documents

- `docs/maintenance/workflow-inventory-2026-02-17.md`
- `docs/ci-policy.md`
- `docs/ci/docs-doctest-policy.md`
- `docs/ci/copilot-review-gate.md`
- `docs/ci/workflow-topology-mapping-2026-03-04.md`

## 日本語

最終更新: 2026-03-14

対象: `.github/workflows/*.yml` の運用責務整理（Issue #2031 / Phase 3）

補足（2026-03-04）:
- 4系統（`pr-core` / `pr-extended` / `maintenance` / `release-assurance`）への再配置案は
  `docs/ci/workflow-topology-mapping-2026-03-04.md` を参照。

## 1. 目的

- CI workflow の責務を `core / optional / report` に明確化する
- Required checks と非Required workflow の使い分けを運用で統一する
- workflow 統合・削減時の判断基準を固定する

## 2. ロール定義

- `core`: 日常PRの品質ゲート。失敗時は即対応対象
- `optional`: ラベル/dispatch/schedule で実行する重い検証
- `report`: 可視化・通知・自己修復など運用補助

補足:

- 2026-03-14 時点の main branch Required checks は `verify-lite`, `policy-gate`, `gate` の 3 つ
- `gate` は `copilot-review-gate.yml` が出す status check 名
- Copilot Auto Fix 後の gate 再評価 dispatch は `copilot-review-gate.yml` ではなく `agent-commands.yml` が担当

## 3. 現行マッピング（主要workflow）

### 3.1 core

| Workflow | 主目的 | 実行トリガ |
|---|---|---|
| `verify-lite.yml` | 軽量必須ゲート（型/ビルド/基本検証） | PR / push / dispatch |
| `policy-gate.yml` | Required checks / risk policy / OPA shadow compare の判定 | PR / review / workflow_run / dispatch |
| `copilot-review-gate.yml` | Copilotレビュー存在/解決確認 | PR / review / dispatch |
| `ci.yml` | 総合オーケストレーション入口 | PR / push / schedule / dispatch |
| `ci-fast.yml` | 高速検証バッチ | call / dispatch |
| `pr-verify.yml` | PR向け標準検証 | call / dispatch |
| `verify.yml` | traceability/formal系の統合検証入口 | PR / call / dispatch |
| `workflow-lint.yml` | workflow品質ルール検証 | PR / push |
| `docs-doctest.yml` | README/docs索引の軽量doctest + 週次全量doctest | PR(path) / push(main,path) / schedule / dispatch |
| `coverage-check.yml` | カバレッジ閾値ゲート | PR / push / dispatch |
| `spec-validation.yml` | spec fail-fast / schema検証 | PR / push / call / dispatch |

### 3.2 optional

| Workflow | 主目的 | 実行トリガ |
|---|---|---|
| `ci-extended.yml` | integration/property/mbt/mutation | call |
| `parallel-test-execution.yml` | 並列テスト実行最適化 | call / dispatch |
| `hermetic-ci.yml` | hermetic再現性検証 | call / dispatch |
| `formal-verify.yml` | formalツール実行（opt-in） | PR(label) / dispatch |
| `formal-aggregate.yml` | formal実行結果集約 | call / dispatch |
| `security.yml` | security系重検証 | PR(label) / push / schedule / dispatch |
| `sbom-generation.yml` | SBOM生成・脆弱性収集 | PR/push/call/dispatch |
| `context-pack-quality-gate.yml` | Context Pack E2E検証（段階導入ゲート） | PR(path) / push(main) / dispatch |
| `flake-detect.yml` / `flake-stability.yml` | flake検出/再試行 | schedule / dispatch / call |
| `podman-smoke.yml` / `docker-tests.yml` | コンテナ実行検証 | call/dispatch/schedule |
| `mutation-quick.yml` | mutation quick検証 | dispatch |

### 3.3 report

| Workflow | 主目的 | 実行トリガ |
|---|---|---|
| `pr-ci-status-comment.yml` | PR向けCIサマリ/auto-merge制御 | PR / schedule / dispatch |
| `pr-self-heal.yml` | 失敗時の自動復旧実行 | workflow_run / schedule / dispatch |
| `ci-auto-rerun-failed.yml` | 失敗jobの自動再実行 | workflow_run |
| `automation-observability-weekly.yml` | 週次の自動化SLO/MTTR観測 | schedule / dispatch |
| `adapter-thresholds.yml` | 閾値レポート（report-only） | PR |
| `branch-protection-apply.yml` | branch protection 適用運用 | dispatch |

## 4. 運用ルール

1. 新規 workflow 追加時は本ドキュメントにロールを追記する
2. `core` への昇格は、再現性・実行時間・誤検知率を確認してから行う
3. `optional` のうち高頻度運用になったものは `core` 統合候補として四半期見直しする
4. `report` は PR merge blocking 条件に含めない

## 5. 関連ドキュメント

- `docs/maintenance/workflow-inventory-2026-02-17.md`
- `docs/ci-policy.md`
- `docs/ci/docs-doctest-policy.md`
- `docs/ci/copilot-review-gate.md`
- `docs/ci/workflow-topology-mapping-2026-03-04.md`
