# CI Workflow Topology Mapping (2026-03-04)

対象Issue: `#2404`  
目的: 現行の `.github/workflows/*.yml`（56本）を、理想設計の4系統へ再配置する。

## 1. 4系統の定義

- `pr-core`
  - PRの必須品質判定と自動化レーン。日常開発で常時利用する。
- `pr-extended`
  - ラベル/dispatch起動の重い検証。必要時のみ実行する。
- `maintenance`
  - 定期観測、再実行、運用保守。PRマージ可否には直接使わない。
- `release-assurance`
  - リリース検証・配布品質検証。

## 2. 現行56 workflow のマッピング

| Workflow | 目標トラック | 移行方針 |
|---|---|---|
| `ae-ci.yml` | `pr-core` | `ci.yml` 配下の reusable 呼び出しに寄せる |
| `agent-commands.yml` | `pr-core` | PRコメント起点の入口として維持 |
| `ci-core.yml` | `pr-core` | `pr-core` の reusable 本体として維持 |
| `ci-fast.yml` | `pr-core` | 高速検証バッチとして維持 |
| `ci.yml` | `pr-core` | `pr-core` 入口へ一本化（他入口の集約先） |
| `codegen-drift-check.yml` | `pr-core` | `pr-core` へ統合（stage化） |
| `codex-autopilot-lane.yml` | `pr-core` | 収束制御レーンとして維持（state機械へ接続） |
| `copilot-auto-fix.yml` | `pr-core` | `pr-core` 自動修正ステージとして維持 |
| `copilot-review-gate.yml` | `pr-core` | review解決ゲートとして維持（required候補） |
| `coverage-check.yml` | `pr-core` | required維持、結果契約を共通化 |
| `docs-doctest.yml` | `pr-core` | docs変更時の軽量ゲートとして維持 |
| `fail-fast-spec-validation.yml` | `pr-core` | `spec-validation.yml` へ段階統合 |
| `minimal-pipeline.yml` | `pr-core` | 非推奨化し `pr-core` へ統合 |
| `policy-gate.yml` | `pr-core` | required維持、判定順序の先頭に固定 |
| `pr-ci-status-comment.yml` | `pr-core` | auto-merge連携の報告レーンとして維持 |
| `pr-self-heal.yml` | `pr-core` | self-heal制御として維持（共通state参照） |
| `pr-verify.yml` | `pr-core` | `pr-core` の reusable 実体へ寄せる |
| `quality-gates-centralized.yml` | `pr-core` | 名称整理の上で `pr-core` 内へ統合 |
| `slash-commands.yml` | `pr-core` | dispatch入口として維持 |
| `spec-check.yml` | `pr-core` | `spec-validation.yml` へ段階統合 |
| `spec-generate-model.yml` | `pr-core` | trace系ゲートとして維持（policy連携） |
| `spec-validation.yml` | `pr-core` | spec検証の主入口として維持 |
| `testing-ddd-scripts.yml` | `pr-core` | `pr-core` の条件付きステップへ統合 |
| `validate-artifacts-ajv.yml` | `pr-core` | artifact契約検証として維持 |
| `verify-lite.yml` | `pr-core` | required維持（最終的な主ゲート） |
| `verify.yml` | `pr-core` | `pr-core`/`pr-extended` への分離再編 |
| `workflow-lint.yml` | `pr-core` | workflow品質ゲートとして維持 |
| `adapter-thresholds.yml` | `pr-extended` | `run-adapters` 条件の opt-in として維持 |
| `cedar-quality-gates.yml` | `pr-extended` | security群へ統合（mode化） |
| `ci-extended.yml` | `pr-extended` | extended検証の主入口として維持 |
| `context-pack-quality-gate.yml` | `pr-extended` | path/label駆動の opt-in 維持 |
| `docker-tests.yml` | `pr-extended` | heavy test として維持 |
| `formal-aggregate.yml` | `pr-extended` | formal群の集約として維持 |
| `formal-verify.yml` | `pr-extended` | formal実行の主入口として維持 |
| `hermetic-ci.yml` | `pr-extended` | 再現性検証として維持 |
| `lean-proof.yml` | `pr-extended` | formal拡張として維持 |
| `mutation-quick.yml` | `pr-extended` | heavy検証側へ移動 |
| `parallel-test-execution.yml` | `pr-extended` | extended reusable として維持 |
| `phase6-validation.yml` | `pr-extended` | UI/UX系の拡張検証として維持 |
| `podman-smoke.yml` | `pr-extended` | container smoke（opt-in）維持 |
| `runtime-conformance-self-heal.yml` | `pr-extended` | conformance拡張として維持 |
| `sbom-generation.yml` | `pr-extended` | security群へ統合（mode化） |
| `security.yml` | `pr-extended` | security拡張の主入口として維持 |
| `webapi-sample-ci.yml` | `pr-extended` | sample検証に限定し opt-in 維持 |
| `automation-observability-weekly.yml` | `maintenance` | 週次運用観測として維持 |
| `branch-protection-apply.yml` | `maintenance` | 管理者向け運用workflowとして維持 |
| `ci-auto-rerun-failed.yml` | `maintenance` | 再実行制御として維持 |
| `flake-detect.yml` | `maintenance` | flake管理の主入口として維持 |
| `flake-stability.yml` | `maintenance` | `flake-detect.yml` reusable へ寄せる |
| `grafana-dashboards.yml` | `maintenance` | 監視資産同期として維持 |
| `lockfile-reproducibility.yml` | `maintenance` | 再現性監視として維持 |
| `nightly.yml` | `maintenance` | 夜間バッチ入口として維持 |
| `triage.yml` | `maintenance` | トリアージ運用として維持 |
| `post-deploy-verify.yml` | `release-assurance` | release検証の主入口として維持 |
| `release-quality-artifacts.yml` | `release-assurance` | リリース証跡の品質検証として維持 |
| `release.yml` | `release-assurance` | リリース配布フローとして維持 |

## 3. 集約後の構成目標（数）

- 現在: 56 workflows
- 目標:
  - `pr-core`: 27（うち統合候補 6）
  - `pr-extended`: 17（うち mode 統合候補 3）
  - `maintenance`: 9（うち reusable 化候補 2）
  - `release-assurance`: 3

## 4. 実装順（手戻り最小化）

1. 判定順序共通化（`policy-gate`/`review-gate`/`verify-lite`）
2. `pr-core` の入口整理（`ci.yml` と `quality-gates-centralized.yml` の役割統一）
3. `fail-fast-spec-validation.yml` / `spec-check.yml` を `spec-validation.yml` へ統合
4. `pr-extended` の security/formal グルーピングを mode 化
5. `maintenance` の reusable 化（flake系）

## 5. 完了判定

- 全workflowが4系統のいずれかに一意に所属する
- required checks 名称を維持したまま統合できる
- `docs/ci` の運用手順と実装の参照先が一致する
