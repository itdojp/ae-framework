---
docRole: ssot
lastVerified: '2026-03-26'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# CI Workflow Topology Mapping (2026-03-04)

> 🌍 Language / 言語: English | 日本語

対象Issue / Target issue: `#2404`
目的 / Purpose: 現行の `.github/workflows/*.yml`（56本）を、理想設計の4系統へ再配置する。 / Re-map the current `.github/workflows/*.yml` set (56 workflows) into the four-track target topology.

## English

### 1. Four-track definitions

- `pr-core`
  - Required PR quality decisions and automation lanes used in day-to-day development.
- `pr-extended`
  - Heavy validation paths triggered by label or dispatch, used only when needed.
- `maintenance`
  - Scheduled observation, reruns, and operational maintenance. These do not directly decide whether a PR can merge.
- `release-assurance`
  - Release verification and distribution-quality validation.

### 2. Current 56-workflow mapping

| Workflow | Target track | Migration policy |
| --- | --- | --- |
| `ae-ci.yml` | `pr-core` | Move closer to reusable calls under `ci.yml` |
| `agent-commands.yml` | `pr-core` | Keep as the PR-comment entrypoint |
| `ci-core.yml` | `pr-core` | Keep as the reusable core for `pr-core` |
| `ci-fast.yml` | `pr-core` | Keep as the fast validation batch |
| `ci.yml` | `pr-core` | Consolidate as the main `pr-core` entrypoint |
| `codegen-drift-check.yml` | `pr-core` | Integrate into `pr-core` as a stage |
| `codex-autopilot-lane.yml` | `pr-core` | Keep as the convergence-control lane connected to the state machine |
| `copilot-auto-fix.yml` | `pr-core` | Keep as an auto-fix stage inside `pr-core` |
| `copilot-review-gate.yml` | `pr-core` | Keep as the review-resolution gate and required-check candidate |
| `coverage-check.yml` | `pr-core` | Keep as required and normalize the result contract |
| `docs-doctest.yml` | `pr-core` | Keep as the lightweight gate for doc changes |
| `fail-fast-spec-validation.yml` | `pr-core` | Gradually merge into `spec-validation.yml` |
| `minimal-pipeline.yml` | `pr-core` | Deprecate and fold into `pr-core` |
| `policy-gate.yml` | `pr-core` | Keep as required and pin it to the start of the decision order |
| `pr-ci-status-comment.yml` | `pr-core` | Keep as the reporting lane used by auto-merge coordination |
| `pr-self-heal.yml` | `pr-core` | Keep as the self-heal controller referencing shared state |
| `pr-verify.yml` | `pr-core` | Move toward the reusable implementation behind `pr-core` |
| `quality-gates-centralized.yml` | `pr-core` | Rename/restructure and absorb into `pr-core` |
| `slash-commands.yml` | `pr-core` | Keep as the dispatch entrypoint |
| `spec-check.yml` | `pr-core` | Gradually merge into `spec-validation.yml` |
| `spec-generate-model.yml` | `pr-core` | Keep as the trace-oriented gate with policy integration |
| `spec-validation.yml` | `pr-core` | Keep as the primary spec-validation entrypoint |
| `testing-ddd-scripts.yml` | `pr-core` | Integrate as conditional steps inside `pr-core` |
| `validate-artifacts-ajv.yml` | `pr-core` | Keep as the artifact-contract validator |
| `verify-lite.yml` | `pr-core` | Keep as required and preserve it as the primary gate |
| `verify.yml` | `pr-core` | Re-split between `pr-core` and `pr-extended` |
| `workflow-lint.yml` | `pr-core` | Keep as the workflow-quality gate |
| `adapter-thresholds.yml` | `pr-extended` | Keep as an opt-in lane under `run-adapters` |
| `cedar-quality-gates.yml` | `pr-extended` | Merge into the security group through mode-based control |
| `ci-extended.yml` | `pr-extended` | Keep as the primary entrypoint for extended validation |
| `context-pack-quality-gate.yml` | `pr-extended` | Keep as a path/label-driven opt-in gate |
| `docker-tests.yml` | `pr-extended` | Keep as a heavy test lane |
| `formal-aggregate.yml` | `pr-extended` | Keep as the formal aggregation lane |
| `formal-verify.yml` | `pr-extended` | Keep as the primary formal-execution entrypoint |
| `hermetic-ci.yml` | `pr-extended` | Keep as the reproducibility validation lane |
| `lean-proof.yml` | `pr-extended` | Keep as the formal-extension lane |
| `mutation-quick.yml` | `pr-extended` | Move to the heavy-validation side |
| `parallel-test-execution.yml` | `pr-extended` | Keep as reusable extended execution |
| `phase6-validation.yml` | `pr-extended` | Keep as the UI/UX extended validation lane |
| `podman-smoke.yml` | `pr-extended` | Keep as an opt-in container smoke lane |
| `runtime-conformance-self-heal.yml` | `pr-extended` | Keep as an extended conformance lane |
| `sbom-generation.yml` | `pr-extended` | Merge into the security group through mode-based control |
| `security.yml` | `pr-extended` | Keep as the primary security-extension entrypoint |
| `webapi-sample-ci.yml` | `pr-extended` | Limit it to sample validation and keep it opt-in |
| `automation-observability-weekly.yml` | `maintenance` | Keep as the weekly automation-observability lane |
| `branch-protection-apply.yml` | `maintenance` | Keep as the admin-facing operations workflow |
| `ci-auto-rerun-failed.yml` | `maintenance` | Keep as the rerun controller |
| `flake-detect.yml` | `maintenance` | Keep as the primary flake-management entrypoint |
| `flake-stability.yml` | `maintenance` | Move closer to a reusable helper for `flake-detect.yml` |
| `grafana-dashboards.yml` | `maintenance` | Keep as the observability-asset sync lane |
| `lockfile-reproducibility.yml` | `maintenance` | Keep as the reproducibility-monitoring lane |
| `nightly.yml` | `maintenance` | Keep as the nightly batch entrypoint |
| `triage.yml` | `maintenance` | Keep as the triage operations lane |
| `post-deploy-verify.yml` | `release-assurance` | Keep as the primary release-verification entrypoint |
| `release-quality-artifacts.yml` | `release-assurance` | Keep as the release-artifact quality validator |
| `release.yml` | `release-assurance` | Keep as the release distribution flow |

### 3. Target structure after consolidation

- Current: 56 workflows
- Target:
  - `pr-core`: 27 workflows (6 candidates for direct consolidation)
  - `pr-extended`: 17 workflows (3 candidates for mode-based consolidation)
  - `maintenance`: 9 workflows (2 candidates for reusable extraction)
  - `release-assurance`: 3 workflows

### 4. Recommended implementation order

1. Normalize the common decision order (`policy-gate` / review-gate / `verify-lite`).
2. Simplify `pr-core` entrypoints by clarifying the roles of `ci.yml` and `quality-gates-centralized.yml`.
3. Merge `fail-fast-spec-validation.yml` and `spec-check.yml` into `spec-validation.yml`.
4. Reorganize security/formal grouping inside `pr-extended` through mode-based control.
5. Extract reusable helpers from `maintenance`, starting with the flake-related workflows.

### 5. Completion criteria

- Every workflow belongs uniquely to one of the four tracks.
- Required check names remain stable while the implementation is consolidated.
- `docs/ci` operational guidance and implementation references point to the same current locations.

## 日本語

### 1. 4系統の定義

- `pr-core`
  - PRの必須品質判定と自動化レーン。日常開発で常時利用する。
- `pr-extended`
  - ラベル/dispatch起動の重い検証。必要時のみ実行する。
- `maintenance`
  - 定期観測、再実行、運用保守。PRマージ可否には直接使わない。
- `release-assurance`
  - リリース検証・配布品質検証。

### 2. 現行56 workflow のマッピング

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

### 3. 集約後の構成目標（数）

- 現在: 56 workflows
- 目標:
  - `pr-core`: 27（うち統合候補 6）
  - `pr-extended`: 17（うち mode 統合候補 3）
  - `maintenance`: 9（うち reusable 化候補 2）
  - `release-assurance`: 3

### 4. 実装順（手戻り最小化）

1. 判定順序共通化（`policy-gate`/`review-gate`/`verify-lite`）
2. `pr-core` の入口整理（`ci.yml` と `quality-gates-centralized.yml` の役割統一）
3. `fail-fast-spec-validation.yml` / `spec-check.yml` を `spec-validation.yml` へ統合
4. `pr-extended` の security/formal グルーピングを mode 化
5. `maintenance` の reusable 化（flake系）

### 5. 完了判定

- 全workflowが4系統のいずれかに一意に所属する
- required checks 名称を維持したまま統合できる
- `docs/ci` の運用手順と実装の参照先が一致する
