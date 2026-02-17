# Workflow Role Matrix (core / optional / report)

最終更新: 2026-02-17

対象: `.github/workflows/*.yml` の運用責務整理（Issue #2031 / Phase 3）

## 1. 目的

- CI workflow の責務を `core / optional / report` に明確化する
- Required checks と非Required workflow の使い分けを運用で統一する
- workflow 統合・削減時の判断基準を固定する

## 2. ロール定義

- `core`: 日常PRの品質ゲート。失敗時は即対応対象
- `optional`: ラベル/dispatch/schedule で実行する重い検証
- `report`: 可視化・通知・自己修復など運用補助

補足:

- 2026-02-17 時点の main branch Required checks は `verify-lite`, `gate` の 2 つ

## 3. 現行マッピング（主要workflow）

### 3.1 core

| Workflow | 主目的 | 実行トリガ |
|---|---|---|
| `verify-lite.yml` | 軽量必須ゲート（型/ビルド/基本検証） | PR / push / dispatch |
| `copilot-review-gate.yml` | Copilotレビュー存在/解決確認 | PR / review / dispatch |
| `ci.yml` | 総合オーケストレーション入口 | PR / push / schedule / dispatch |
| `ci-fast.yml` | 高速検証バッチ | call / dispatch |
| `pr-verify.yml` | PR向け標準検証 | call / dispatch |
| `verify.yml` | traceability/formal系の統合検証入口 | PR / call / dispatch |
| `workflow-lint.yml` | workflow品質ルール検証 | PR / push |
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
- `docs/ci/copilot-review-gate.md`
