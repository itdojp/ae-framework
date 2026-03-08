# 📚 ae-framework Documentation / ドキュメント

> 🌍 Language / 言語: English | 日本語

---

## English

Comprehensive documentation for the agentic SDLC orchestrator and assurance control plane.

### Current implementation snapshot (recommended first read)
- System overview (implementation-aligned): `architecture/CURRENT-SYSTEM-OVERVIEW.md`
- Product summary: `product/OVERVIEW.md`, `product/DETAIL.md`, `product/USER-MANUAL.md`

### Getting Started
- Quick Start (15 minutes): `getting-started/QUICK-START-GUIDE.md`
- Phase 6 Quick Start (UI/UX): `getting-started/PHASE-6-GETTING-STARTED.md`
- Setup: `getting-started/SETUP.md`

### Product Docs
- Overview: `product/OVERVIEW.md`
- Detailed description: `product/DETAIL.md`
- User manual: `product/USER-MANUAL.md`
- Positioning / comparison: `product/POSITIONING.md`
- Assurance control plane: `product/ASSURANCE-CONTROL-PLANE.md`

### Strategy
- Codex boundary + Verify-first strategy: `strategy/CODEX-AE-BOUNDARY-VERIFY-FIRST.md`
- Plan -> Spec normalization template: `templates/plan-to-spec-normalization-template.md`
- Agent development policy (risk-based PR gating): `agent-dev-policy.md`

### Maintenance
- Repository layout policy: `maintenance/repo-layout-policy.md`
- Code improvement plan: `maintenance/code-improvement-plan.md`
- Branch cleanup runbook: `maintenance/branch-cleanup-runbook.md`
- Remote branch triage runbook: `maintenance/remote-branch-triage-runbook.md`
- Multi-agent safety policy: `agents/multi-agent-safety.md`
- Subagent worktree runbook: `maintenance/subagent-worktree-runbook.md`
- Worktree cleanup runbook: `maintenance/worktree-cleanup-runbook.md`
- Branch cleanup report (2026-02-28): `maintenance/branch-cleanup-report-2026-02-28.md`
- Public types sync runbook: `maintenance/public-types-sync-runbook.md`
- TODO triage runbook: `maintenance/todo-triage-runbook.md`
- TODO triage inventory summary (2026-03-01): `maintenance/todo-triage-inventory-2026-03-01.md`
- TODO triage inventory (triage CSV, 2026-03-01): `maintenance/todo-triage-inventory-2026-03-01.csv`
- TODO triage backlog (2026-03-01): `maintenance/todo-triage-backlog-2026-03-01.md`
- TODO triage inventory summary (2026-02-28): `maintenance/todo-triage-inventory-2026-02-28.md`
- TODO triage inventory (triage CSV, 2026-02-28): `maintenance/todo-triage-inventory-2026-02-28.csv`
- TODO triage backlog (2026-02-28): `maintenance/todo-triage-backlog-2026-02-28.md`
- Phase 0 inventory snapshot: `maintenance/phase0-inventory-2026-02-17.md`

### Positioning maps (concept / flow / use cases)
- Concept & system diagrams: `architecture/ARCHITECTURE.md`
- Reference flow (Web API + DB): `reference/REFERENCE-FLOW-WEB-API-DB.md`
- Minimal adoption flow: `quality/adoption-sample-flow.md`
- Formal mini flow: `quality/formal-mini-flow.md`

### Guides
- Development Instructions: `guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md`
- Claude Code Automation Guide: `guides/CLAUDE-CODE-AUTOMATION-GUIDE.md`
- Phase 2 Advanced Features (2.1–2.3): `guides/PHASE-2-ADVANCED-FEATURES-GUIDE.md`
- Advanced Troubleshooting: `guides/ADVANCED-TROUBLESHOOTING-GUIDE.md`
- Context Pack onboarding checklist: `guides/context-pack-onboarding-checklist.md`
- Context Pack Phase5+ cookbook: `guides/context-pack-phase5-cookbook.md`
- Context Pack troubleshooting runbook: `operations/context-pack-troubleshooting.md`
- Thread -> Repo -> CI flow: `guides/THREAD-REPO-CI-FLOW.md`
- General Usage: `guides/USAGE.md`
- CLI Entry Migration: `guides/CLI-MIGRATION.md`
- ExecPlan JSON schema: `guides/EXECPLAN-SCHEMA.md`

### Development
- Enhanced State Manager: [development/enhanced-state-manager.md](./development/enhanced-state-manager.md) - SSOT/versioning/transactions with EventBus-aware state management.
- Circuit Breaker Pattern: [development/circuit-breaker.md](./development/circuit-breaker.md) - CLOSED/OPEN/HALF_OPEN failover control with fallback and monitoring.

### Phases
- Natural Language Requirements: `phases/PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md`
- Runtime Conformance: `phases/PHASE-2-2-RUNTIME-CONFORMANCE.md`
- Telemetry-as-Context (Trace Bundle ingest): `operate/telemetry-as-context.md`
- Release engineering policy (rollout/rollback contract): `operate/release-engineering.md`
- Integration Testing / E2E: `phases/PHASE-2-3-INTEGRATION-TESTING.md`
- User Stories: `phases/PHASE-3-USER-STORIES-CREATION.md`
- Validation: `phases/PHASE-4-VALIDATION.md`
- Domain Modeling: `phases/PHASE-5-DOMAIN-MODELING.md`
- Phase 6 UI/UX: `phases/phase-6-uiux.md`
- Frontend foundation: `phases/frontend-foundation.md`
- Telemetry configuration: `phases/telemetry-configuration.md`

### Integrations
- Claude Code Task Tool Integration: `integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`
- Claude Code Workflow: `integrations/CLAUDECODE-WORKFLOW.md`
- CodeX Integration (PoC/MCP/Adapter): `integrations/CODEX-INTEGRATION.md`
- Codex boundary + vendor-neutral core: `integrations/CODEX-VENDOR-NEUTRAL-BOUNDARY.md`

### Reference
- CLI Commands: `reference/CLI-COMMANDS-REFERENCE.md`
- API Reference: `reference/API.md`
- Schema governance ($id canonical URI policy): [SCHEMA-GOVERNANCE.md](./reference/SCHEMA-GOVERNANCE.md)
- Contract catalog (input/decision/evidence/operation): [CONTRACT-CATALOG.md](./reference/CONTRACT-CATALOG.md)
- Change Package v2 reference: `reference/change-package-v2.md`
- Context Pack v1 validation guide: [context-pack.md](./spec/context-pack.md)
- Spec & Verification Kit (minimal activation guide): `reference/SPEC-VERIFICATION-KIT-MIN.md`
- Legacy ExecPlan (6-phase, deprecated): `../plans/archive/legacy-6-phase.md`

### Architecture
- TDD Framework Architecture: `architecture/TDD-FRAMEWORK-ARCHITECTURE.md`
- CEGIS Design: `architecture/CEGIS-DESIGN.md`
- Runtime Conformance Design: `architecture/RUNTIME-CONFORMANCE-DESIGN.md`
- Zero-based ideal redesign: `architecture/ZERO-BASED-IDEAL-DESIGN.md`
- PR state / execution plan v1 draft: `architecture/PR-STATE-EXECUTION-PLAN-V1-DRAFT.md`

### Quality / Verification
- Assurance model: `quality/ASSURANCE-MODEL.md`
- Assurance lanes / independence rule: `quality/assurance-lanes.md`
- Formal Quality Gates (DoD v0.2): `quality/formal-gates.md`
- Ownership DoD: `quality/ownership-dod.md`
- LLM first-pass review checklist: `quality/llm-first-review-checklist.md`
- Guarded automation template: `quality/guarded-automation-template.md`
- Incident triage template: `quality/incident-triage-template.md`
- Artifacts contract: `quality/ARTIFACTS-CONTRACT.md`
- Doc consistency lint: `quality/doc-consistency-lint.md`
- Contract taxonomy (DbC / API / Artifacts): `quality/contract-taxonomy.md`
- Verify-first gate baseline: `quality/verify-first-gate-baseline.md`
- Verify-first failure diagnostic template: `quality/verify-first-failure-diagnostic-template.md`
- Verify-first failure comment design: `quality/verify-first-failure-comment-design.md`
- Verify-first artifacts catalog: `quality/verify-first-artifacts-catalog.md`
- Verify-first implementation runbook: `quality/verify-first-implementation-runbook.md`
- Assurance profile / level: `quality/assurance-profile.md`
- Adoption sample flow: `quality/adoption-sample-flow.md`
- Runbooks / Traceability / Runtime Contracts: see `./quality` and `./verify`
- Coverage policy: `quality/coverage-policy.md`（しきい値の由来/Required化の運用）
- Formal runbook: `quality/formal-runbook.md`（ラベル/dispatch/要約/環境変数）
- CSP verification (cspx runner): `quality/formal-csp.md`（使い方/成果物/実行結果例）
- Usefulness evaluation: `quality/usefulness-evaluation.md`（4軸スコア算出/終了コード契約）
- Issue requirements traceability: `quality/issue-requirements-traceability.md`（extract-ids/matrix/strict validate）
- PoC success criteria (#2409 first slice): `quality/poc-success-criteria-2409.md`（performance/reproducibility/cost/ops/exit）
- PoC comparison template (TS baseline vs Go/Rust): `templates/quality/poc-comparison-metrics-template.md`
- ADR template for adoption/rejection decision: `templates/quality/adr-poc-adoption-template.md`
- CI policy: `ci-policy.md`（PR必須ゲート/opt-in/運用方針）
- Docs Doctest policy: `ci/docs-doctest-policy.md`（PR軽量チェック + 週次全量チェック）
- CI operations handbook: `ci/ci-operations-handbook.md`（日次確認/再実行/停止復帰）
- CI troubleshooting guide: `ci/ci-troubleshooting-guide.md`（失敗分類/復旧runbook）
- Harness failure taxonomy: `ci/harness-taxonomy.md`（ゲート横断の分類/重要度/次アクション）
- PR automation runbook: `ci/pr-automation.md`（Copilot→auto-fix→auto-merge）
- Review topology matrix validation: `ci/review-topology-matrix.md`（solo/team/override の比較検証）
- Change Package runbook: `ci/change-package.md`（証跡パッケージ生成/検証/PR要約連携）
- Workflow role matrix: `ci/workflow-role-matrix.md`（core / optional / report の責務整理）
- Workflow topology mapping (4 tracks): `ci/workflow-topology-mapping-2026-03-04.md`（56 workflows の4系統再配置案）
- Opt-in controls: `ci/OPT-IN-CONTROLS.md`（ラベル/Slash/dispatchの一覧）
- CI docs boundary matrix: `ci/ci-doc-boundary-matrix.md`（方針文書とrunbookの責務境界）
- Copilot Review Gate: `ci/copilot-review-gate.md`（レビュー必須化）
- Copilot Auto Fix: `ci/copilot-auto-fix.md`（suggestion自動適用）
- Codex Autopilot Lane: `ci/codex-autopilot-lane.md`（touchless merge の opt-in）
- Auto Merge: `ci/auto-merge.md`（auto-merge自動有効化）
- Automation Failure Policies: `ci/automation-failure-policies.md`（fail-open/fail-closedとコメントテンプレ）
- Automation Rollback Runbook: `ci/automation-rollback-runbook.md`（段階停止/復帰/巻き戻し）
- Rollback Validation Report (2026-02-14): `ci/automation-rollback-validation-2026-02-14.md`（dry-run実行ログ）
- Automation Profiles: `ci/automation-profiles.md`（自動化設定の一括プロファイル）
- Automation Observability: `ci/automation-observability.md`（共通JSON/Step Summary出力）
- Automation Alerting: `ci/automation-alerting.md`（通知条件/テンプレート/重複抑止）
- Automation SLO/MTTR: `ci/automation-slo-mttr.md`（成功率SLOと復旧時間MTTRの定義）
- OTel/Artifacts/Gate Integration Plan: `ci/otel-artifacts-gate-integration-plan.md`（Issue #2380 の段階導入設計）
- Trace Required Criteria: `ci/trace-required-criteria.md`（Go/No-Go基準/集計手順/preset昇格）
- Context Pack Gate Rollout: `ci/context-pack-gate-rollout.md`（non-blocking→blocking 段階導入）
- Automation Permission Boundaries: `ci/automation-permission-boundaries.md`（workflow_dispatch / issue_comment の権限境界）
- Workflow dispatch validation report (2026-02-12): `ci/workflow-dispatch-validation-2026-02-12.md`

For the complete navigation with highlights, see the Japanese section below (same links).

---

> エージェント協調型SDLCオーケストレーター兼 assurance control plane の包括的ドキュメント

## 🚀 はじめに

ae-frameworkは、エージェント協調型のSDLCオーケストレーター兼 assurance control plane です。Claude Code / CodeX 連携やMCPサーバを通じて、要件→仕様→検証→証跡→運用判断のフローを統一します。

## 📖 ドキュメント構成

### 🏁 [getting-started/](./getting-started/) - 導入・クイックスタート
最初に読むべきドキュメント群

- **[QUICK-START-GUIDE.md](./getting-started/QUICK-START-GUIDE.md)** ⭐ **推奨** - 15分で始めるae-framework
- **[PHASE-6-GETTING-STARTED.md](./getting-started/PHASE-6-GETTING-STARTED.md)** ⭐ **最新** - Phase 6 UI/UX専用クイックスタート  
- [SETUP.md](./getting-started/SETUP.md) - 基本セットアップ手順

### 🧩 [product/](./product/) - プロダクト資料
- [OVERVIEW.md](./product/OVERVIEW.md) - 概要説明資料
- [DETAIL.md](./product/DETAIL.md) - 詳細説明資料
- [USER-MANUAL.md](./product/USER-MANUAL.md) - 利用マニュアル
- [POSITIONING.md](./product/POSITIONING.md) - 類似ツールとの棲み分け・導入指針
- [ASSURANCE-CONTROL-PLANE.md](./product/ASSURANCE-CONTROL-PLANE.md) - assurance control plane としての価値定義
- [PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md](./product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md) - 適用対象 × 入力 × 出力 × ツール適性

### 🧭 [strategy/](./strategy/) - 戦略・責務境界
- [CODEX-AE-BOUNDARY-VERIFY-FIRST.md](./strategy/CODEX-AE-BOUNDARY-VERIFY-FIRST.md) - Codex との責務境界、Verify-first、Thread→Repo→CI の標準化
- [plan-to-spec-normalization-template.md](./templates/plan-to-spec-normalization-template.md) - Plan を repo SSOT に正規化する最小テンプレート

### 🧭 ポジショニングの図とフロー
- 概念図/システム図: `architecture/ARCHITECTURE.md`
- リファレンスフロー（Web API + DB）: `reference/REFERENCE-FLOW-WEB-API-DB.md`
- 導入の最小フロー: `quality/adoption-sample-flow.md`
- フォーマル最小フロー: `quality/formal-mini-flow.md`

### 📖 [guides/](./guides/) - 実用ガイド・チュートリアル
実際の開発で使える実用ガイド

- **[DEVELOPMENT-INSTRUCTIONS-GUIDE.md](./guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md)** ⭐ **最新** - 開発指示の具体的方法
- **[CLAUDE-CODE-AUTOMATION-GUIDE.md](./guides/CLAUDE-CODE-AUTOMATION-GUIDE.md)** ⭐ **重要** - Claude Code完全自動化
- **🆕 [PHASE-2-ADVANCED-FEATURES-GUIDE.md](./guides/PHASE-2-ADVANCED-FEATURES-GUIDE.md)** ⭐ **NEW** - Phase 2.1-2.3統合ガイド
- **🆕 [ADVANCED-TROUBLESHOOTING-GUIDE.md](./guides/ADVANCED-TROUBLESHOOTING-GUIDE.md)** ⭐ **NEW** - 高度な機能のトラブルシューティング
- [context-pack-onboarding-checklist.md](./guides/context-pack-onboarding-checklist.md) - Context Pack 導入チェックリスト（入力準備→検証→修正→再検証）
- [context-pack-phase5-cookbook.md](./guides/context-pack-phase5-cookbook.md) - Context Pack Phase5+ の実践レシピ
- [context-pack-troubleshooting.md](./operations/context-pack-troubleshooting.md) - Context Pack 検証失敗時の復旧ランブック
- [THREAD-REPO-CI-FLOW.md](./guides/THREAD-REPO-CI-FLOW.md) - Plan を repo SSOT に正規化する標準フロー
- [USAGE.md](./guides/USAGE.md) - 一般的な使い方ガイド
- [CLI-MIGRATION.md](./guides/CLI-MIGRATION.md) - CLI entry 移行ガイド
- [test-generation-guide.md](./guides/test-generation-guide.md) - テスト生成ガイド
- [EXECPLAN-SCHEMA.md](./guides/EXECPLAN-SCHEMA.md) - ExecPlan JSONスキーマ

### 🛠️ [development/](./development/) - 開発向け実装ドキュメント
- [enhanced-state-manager.md](./development/enhanced-state-manager.md) - SSOT管理・バージョニング・トランザクション・EventBus連携を備えた状態管理設計。
- [circuit-breaker.md](./development/circuit-breaker.md) - CLOSED/OPEN/HALF_OPENの遷移で障害連鎖を防ぐ回路遮断パターンの実装ガイド。
- [agent-collaboration-setup.md](./development/agent-collaboration-setup.md) - GitHub駆動 multi-agent 連携セットアップと役割分担。

### 🎯 [phases/](./phases/) - フェーズ別詳細ドキュメント
6フェーズの詳細仕様とガイド

- [PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md](./phases/PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md) - 自然言語要件処理
- **🆕 [PHASE-2-2-RUNTIME-CONFORMANCE.md](./phases/PHASE-2-2-RUNTIME-CONFORMANCE.md)** ⭐ **NEW** - リアルタイム適合性検証システム
- **🆕 [telemetry-as-context.md](./operate/telemetry-as-context.md)** ⭐ **NEW** - Trace Bundle ingest による運用テレメトリの正規化
- **🆕 [release-engineering.md](./operate/release-engineering.md)** ⭐ **NEW** - rollout/rollback を機械可読ポリシーとして扱う運用契約
- **🆕 [PHASE-2-3-INTEGRATION-TESTING.md](./phases/PHASE-2-3-INTEGRATION-TESTING.md)** ⭐ **NEW** - 統合テストとE2Eテストシステム
- [PHASE-3-USER-STORIES-CREATION.md](./phases/PHASE-3-USER-STORIES-CREATION.md) - ユーザーストーリー生成
- [PHASE-4-VALIDATION.md](./phases/PHASE-4-VALIDATION.md) - 品質検証システム
- [PHASE-5-DOMAIN-MODELING.md](./phases/PHASE-5-DOMAIN-MODELING.md) - ドメイン駆動設計
- **[phase-6-uiux.md](./phases/phase-6-uiux.md)** ⭐ **重要** - UI/UX & Frontend Delivery
- **[frontend-foundation.md](./phases/frontend-foundation.md)** ⭐ **技術仕様** - フロントエンド基盤詳細
- **[telemetry-configuration.md](./phases/telemetry-configuration.md)** ⭐ **最新** - OpenTelemetryテレメトリ設定

### 🔗 [integrations/](./integrations/) - 統合・ワークフロー
Claude CodeやMCPとの統合

- **[CLAUDE-CODE-TASK-TOOL-INTEGRATION.md](./integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)** ⭐ **重要** - Task Tool統合仕様
- [CLAUDECODE-WORKFLOW.md](./integrations/CLAUDECODE-WORKFLOW.md) - Claude Codeワークフロー
- [CODEX-INTEGRATION.md](./integrations/CODEX-INTEGRATION.md) - CodeX統合（PoC/MCP/Adapter）
- [CODEX-CONTINUATION-CONTRACT.md](./integrations/CODEX-CONTINUATION-CONTRACT.md) - 継続実行 Contract（No Human Bottleneck v1）
- [CODEX-VENDOR-NEUTRAL-BOUNDARY.md](./integrations/CODEX-VENDOR-NEUTRAL-BOUNDARY.md) - Codex連携の責務境界とVendor-neutral最小コア

### 📚 [reference/](./reference/) - リファレンス・API仕様
コマンドやAPIの詳細仕様

- **[CLI-COMMANDS-REFERENCE.md](./reference/CLI-COMMANDS-REFERENCE.md)** ⭐ **重要** - 全CLIコマンドリファレンス
- [API.md](./reference/API.md) - API仕様
- [SCHEMA-GOVERNANCE.md](./reference/SCHEMA-GOVERNANCE.md) - schema `$id` canonical URI 方針
- [CONTRACT-CATALOG.md](./reference/CONTRACT-CATALOG.md) - 契約カタログ（input/decision/evidence/operation）
- [change-package-v2.md](./reference/change-package-v2.md) - proof-carrying change package v2 の契約と v1 との差分
- [SPEC-VERIFICATION-KIT-MIN.md](./reference/SPEC-VERIFICATION-KIT-MIN.md) - Spec & Verification Kit（最小パッケージ・有効化手順）
- [legacy-6-phase.md](../plans/archive/legacy-6-phase.md) - 旧6フェーズExecPlan（非推奨）

### 🏗️ [architecture/](./architecture/) - アーキテクチャ・設計
システム設計と新機能仕様

- **[TDD-FRAMEWORK-ARCHITECTURE.md](./architecture/TDD-FRAMEWORK-ARCHITECTURE.md)** ⭐ **重要** - TDDフレームワーク設計
- **🆕 [CEGIS-DESIGN.md](./architecture/CEGIS-DESIGN.md)** ⭐ **NEW** - CEGIS自動修復システム設計
- **🆕 [RUNTIME-CONFORMANCE-DESIGN.md](./architecture/RUNTIME-CONFORMANCE-DESIGN.md)** ⭐ **NEW** - Runtime Conformance設計
- **🆕 [ZERO-BASED-IDEAL-DESIGN.md](./architecture/ZERO-BASED-IDEAL-DESIGN.md)** ⭐ **NEW** - ゼロベース再設計（理想アーキテクチャ + 技術再選定）
- **🆕 [PR-STATE-EXECUTION-PLAN-V1-DRAFT.md](./architecture/PR-STATE-EXECUTION-PLAN-V1-DRAFT.md)** ⭐ **NEW** - PR状態機械と実行計画の v1 契約ドラフト（Issue #2405）
- [ARCHITECTURE.md](./architecture/ARCHITECTURE.md) - システムアーキテクチャ
- [NEW_FEATURES.md](./architecture/NEW_FEATURES.md) - 新機能仕様

### ✅ [quality/](./quality/) - 品質ゲート・検証
フォーマル検証や品質基準

- [ASSURANCE-MODEL.md](./quality/ASSURANCE-MODEL.md) - claim / level / lane / evidence kind の共通モデル
- **[formal-gates.md](./quality/formal-gates.md)** ⭐ フォーマル品質ゲート（v0.2 DoD）
- **[formal-csp.md](./quality/formal-csp.md)** ⭐ CSP 検証（cspx 連携・summary/result 契約）
- **[formal-full-run.md](./quality/formal-full-run.md)** ⭐ 全形式ツールのスモークテスト（CSP/Lean 含む）
- **[formal-runbook.md](./quality/formal-runbook.md)** ⭐ 実行運用（ラベルゲート/dispatch/集約）
- [ownership-dod.md](./quality/ownership-dod.md) - Ownership DoD（説明責任/運用/ロールバック）
- [llm-first-review-checklist.md](./quality/llm-first-review-checklist.md) - LLM一次レビューの標準チェック
- [guarded-automation-template.md](./quality/guarded-automation-template.md) - Guarded automation 運用テンプレ
- [incident-triage-template.md](./quality/incident-triage-template.md) - インシデント一次切り分けテンプレ
- [ARTIFACTS-CONTRACT.md](./quality/ARTIFACTS-CONTRACT.md) - 成果物契約（Required/Optional）
- [doc-consistency-lint.md](./quality/doc-consistency-lint.md) - ドキュメント参照整合チェック（pnpm script / path）
- [contract-taxonomy.md](./quality/contract-taxonomy.md) - contract 用語の基準（DbC / API / Artifacts）
- [verify-first-gate-baseline.md](./quality/verify-first-gate-baseline.md) - Verify-first の最小Required/Opt-inゲート基準
- [verify-first-failure-diagnostic-template.md](./quality/verify-first-failure-diagnostic-template.md) - CI失敗時の診断テンプレ（再現手順/Evidence）
- [verify-first-failure-comment-design.md](./quality/verify-first-failure-comment-design.md) - 失敗診断テンプレをPR自動コメントに連携する設計案
- [verify-first-artifacts-catalog.md](./quality/verify-first-artifacts-catalog.md) - Verify-first の最小成果物（SSOT/AC/NFR/Evidence）定義
- [verify-first-implementation-runbook.md](./quality/verify-first-implementation-runbook.md) - Verify-first 実装運用の標準手順（Plan→Spec→Gate→Evidence）
- [assurance-profile.md](./quality/assurance-profile.md) - assurance profile / level の入力契約（claim / level / lanes / evidence kinds）
- [path-normalization-contract.md](./quality/path-normalization-contract.md) - 成果物パス正規化契約（repo-relative優先）
- [run-manifest-freshness-contract.md](./quality/run-manifest-freshness-contract.md) - run-manifest鮮度判定契約（stale artifact 検出）
- [issue-requirements-traceability.md](./quality/issue-requirements-traceability.md) - Issue要件ID起点の traceability 手順（extract/matrix/strict validate）
- [usefulness-evaluation.md](./quality/usefulness-evaluation.md) - 有用性評価レポート契約（4軸/JSON+Markdown）
- [adoption-sample-flow.md](./quality/adoption-sample-flow.md) - 導入の最小フロー（エンドツーエンド）
- [formal-ops-guidelines.md](./quality/formal-ops-guidelines.md) - 運用パターン/命名/証跡/CI分割の指針
- [formal-tools-setup.md](./quality/formal-tools-setup.md) - ローカル環境セットアップ（Apalache/TLC/Z3/cvc5）
- [formal-mini-flow.md](./quality/formal-mini-flow.md) - 反例→失敗テスト→修正→緑の最小フロー
- [poc-success-criteria-2409.md](./quality/poc-success-criteria-2409.md) - #2409 first slice の PoC成功基準（性能/再現性/実装コスト/運用差分/撤収条件）
- [poc-comparison-metrics-template.md](./templates/quality/poc-comparison-metrics-template.md) - TS baseline vs Go/Rust 比較計測テンプレート
- [adr-poc-adoption-template.md](./templates/quality/adr-poc-adoption-template.md) - PoC採用/不採用判定用 ADR テンプレート

### 🛠️ [maintenance/](./maintenance/) - リポジトリ整理・改善計画
- [repo-layout-policy.md](./maintenance/repo-layout-policy.md) - ルート配置ルールと生成物配置方針
- [code-improvement-plan.md](./maintenance/code-improvement-plan.md) - 型安全性/分割/テスト改善の実行計画
- [worktree-cleanup-runbook.md](./maintenance/worktree-cleanup-runbook.md) - マージ済み作業worktreeの安全な削除手順
- [remote-branch-triage-runbook.md](./maintenance/remote-branch-triage-runbook.md) - remote branch の triage と operator approval 手順
- [phase0-inventory-2026-02-17.md](./maintenance/phase0-inventory-2026-02-17.md) - Phase 0棚卸しスナップショット
- [workflow-inventory-2026-02-17.md](./maintenance/workflow-inventory-2026-02-17.md) - Phase 3向けCI workflow棚卸し（目的/入力/重複/必須任意）

### 🧠 現行実装ベース全体像（推奨）
- **[architecture/CURRENT-SYSTEM-OVERVIEW.md](./architecture/CURRENT-SYSTEM-OVERVIEW.md)** - 2026-03 時点の全体構成（CLI/CI/Formal/Artifacts）
- **[architecture/ZERO-BASED-IDEAL-DESIGN.md](./architecture/ZERO-BASED-IDEAL-DESIGN.md)** - ゼロベースで再設計する場合の理想像（設計/技術構成）
- [product/OVERVIEW.md](./product/OVERVIEW.md) - 概要説明資料
- [product/DETAIL.md](./product/DETAIL.md) - 詳細説明資料
- [product/USER-MANUAL.md](./product/USER-MANUAL.md) - 利用マニュアル

### 📐 [spec/](./spec/) - 仕様レジストリ
仕様の配置と規約

- **[registry.md](./spec/registry.md)** ⭐ 仕様配置レジストリ（TLA+/Alloy/Cedar/Trace）
- [context-pack.md](./spec/context-pack.md) - Context Pack v1 の配置・検証ルール

### 🔬 [research/](./research/) - 調査・研究・サーベイ
理論的背景や技術調査の成果物

- [ae-framework-foundation-survey.md](./research/ae-framework-foundation-survey.md) - AE Framework 基礎調査（Formal Methods × AI）

### 💡 [proposals/](./proposals/) - 提案・実験的ドキュメント
将来機能の提案や実験的な設計

- [SUPERCLAUDE_INTEGRATION_PROPOSAL.md](./proposals/SUPERCLAUDE_INTEGRATION_PROPOSAL.md) - SuperClaude統合提案
- [agent-architecture-proposal.md](./proposals/agent-architecture-proposal.md) - エージェントアーキテクチャ提案

### 📜 [legacy/](./legacy/) - 古い・廃止予定ドキュメント
古いバージョンや廃止予定のドキュメント

- [QUICK_START.md](./legacy/QUICK_START.md) - 古いクイックスタート
- [CLAUDE-CODE-TASK-TOOL.md](./legacy/CLAUDE-CODE-TASK-TOOL.md) - 古いTask Toolガイド
- [PHASE3.3_DESIGN.md](./legacy/PHASE3.3_DESIGN.md) - 古いPhase 3設計
- [phase3-1-*.md](./legacy/) - Phase 3.1関連の古い設計
- [agents/](./legacy/agents/) - 古いエージェント設計
- [container-verification.md](./legacy/container-verification.md) - 古いコンテナ検証

## 🎯 用途別ドキュメント推奨

### 🔰 初めて使う方
1. **[getting-started/QUICK-START-GUIDE.md](./getting-started/QUICK-START-GUIDE.md)** - 15分で体験
2. **[guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md](./guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md)** - 実際の指示方法
3. **[integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md](./integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)** - Claude Code統合
4. **🆕 [guides/PHASE-2-ADVANCED-FEATURES-GUIDE.md](./guides/PHASE-2-ADVANCED-FEATURES-GUIDE.md)** - 高度な機能の活用法

### 🎨 Phase 6 UI/UX開発者
1. **[getting-started/PHASE-6-GETTING-STARTED.md](./getting-started/PHASE-6-GETTING-STARTED.md)** - Phase 6専用ガイド
2. **[phases/phase-6-uiux.md](./phases/phase-6-uiux.md)** - UI/UX詳細仕様
3. **[phases/frontend-foundation.md](./phases/frontend-foundation.md)** - 技術基盤仕様
4. **[phases/telemetry-configuration.md](./phases/telemetry-configuration.md)** - テレメトリ設定

### 💻 フルスタック開発者
1. **[architecture/TDD-FRAMEWORK-ARCHITECTURE.md](./architecture/TDD-FRAMEWORK-ARCHITECTURE.md)** - 全体アーキテクチャ
2. **[phases/](./phases/)** - 全フェーズの詳細
3. **[reference/CLI-COMMANDS-REFERENCE.md](./reference/CLI-COMMANDS-REFERENCE.md)** - CLIリファレンス

### 🏢 プロジェクトマネージャー
1. **[guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md](./guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md)** - 効果的な指示方法
2. **[guides/CLAUDE-CODE-AUTOMATION-GUIDE.md](./guides/CLAUDE-CODE-AUTOMATION-GUIDE.md)** - 自動化活用法
3. **[architecture/NEW_FEATURES.md](./architecture/NEW_FEATURES.md)** - 機能概要

### 🧪 品質保証・テストエンジニア
1. **🆕 [phases/PHASE-2-2-RUNTIME-CONFORMANCE.md](./phases/PHASE-2-2-RUNTIME-CONFORMANCE.md)** - リアルタイム適合性検証
2. **🆕 [phases/PHASE-2-3-INTEGRATION-TESTING.md](./phases/PHASE-2-3-INTEGRATION-TESTING.md)** - 統合テスト・E2Eテスト
3. **🆕 [architecture/CEGIS-DESIGN.md](./architecture/CEGIS-DESIGN.md)** - 自動修復システム
4. **🆕 [guides/ADVANCED-TROUBLESHOOTING-GUIDE.md](./guides/ADVANCED-TROUBLESHOOTING-GUIDE.md)** - 問題解決ガイド
5. **[quality/type-coverage-policy.md](./quality/type-coverage-policy.md)** - 型カバレッジポリシー（運用ルール）

## 🔄 更新履歴

### 🆕 2025年8月 - Phase 2 Advanced Features完全実装
- **Phase 2.1: CEGIS自動修復システム**: 反例誘導帰納合成による自動コード修復
- **Phase 2.2: Runtime Conformance System**: リアルタイム適合性検証とCEGIS連携
- **Phase 2.3: Integration Testing System**: 包括的統合テストとE2Eテストオーケストレーション
- **新ドキュメント追加**: 実践ガイド・トラブルシューティング・CLIリファレンス更新

### 2025年8月 - Phase 6 UI/UX & Frontend Delivery完全実装
- **Phase 6実装完了**: React + Next.js 14 UI自動生成
- **OpenTelemetryテレメトリ**: リアルタイム品質監視
- **包括的ドキュメント更新**: 実用ガイド・開発指示方法

### ドキュメント構造改善
- **カテゴリ別整理**: 8つのカテゴリでドキュメントを体系化
- **重要度明示**: ⭐マークで重要・最新ドキュメントを識別
- **legacyフォルダ**: 古いドキュメントの分離
- **proposalsフォルダ**: 将来機能提案の整理

## 🤝 貢献・フィードバック

- **GitHub Issues**: [https://github.com/itdojp/ae-framework/issues](https://github.com/itdojp/ae-framework/issues)
- **Pull Requests**: ドキュメント改善・追加をお待ちしています

## 🎉 次のステップ

1. **[getting-started/QUICK-START-GUIDE.md](./getting-started/QUICK-START-GUIDE.md)** で15分体験
2. **[guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md](./guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md)** で実践的な使い方を学習
3. 実際のプロジェクトでae-frameworkを活用

---

**🤖 ae-framework で、AI-Enhanced Development の未来を今すぐ体験してください！**

---

## 🗣️ Docs Language Policy / ドキュメント言語方針

- Language toggle: 可能な限り各ドキュメント先頭に「Language / 言語」トグルを配置（English | 日本語）。
- Mirrored content: 重要セクション（概要、手順、コマンド、しきい値、CI例）は英日で同等の内容を保つ。
- Minimalism: 冗長な重複は避け、片側に詳細がある場合は他方に「詳細は反対言語側」注記を明記。
- Operational snippets: できるだけ実行可能なスニペット（コマンド、YAML、JSON）を両言語に設置。
- Terminology: 用語は初出時に対訳（例: 適合性=conformance）を併記。以降は文脈に応じて片側表記も可。
