# 📚 ae-framework Documentation / ドキュメント

> 🌍 Language / 言語: English | 日本語

---

## English

Comprehensive documentation for the AI‑Enhanced Development Framework.

### Getting Started
- Quick Start (15 minutes): `getting-started/QUICK-START-GUIDE.md`
- Phase 6 Quick Start (UI/UX): `getting-started/PHASE-6-GETTING-STARTED.md`
- Setup: `getting-started/SETUP.md`

### Guides
- Development Instructions: `guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md`
- Claude Code Automation Guide: `guides/CLAUDE-CODE-AUTOMATION-GUIDE.md`
- Phase 2 Advanced Features (2.1–2.3): `guides/PHASE-2-ADVANCED-FEATURES-GUIDE.md`
- Advanced Troubleshooting: `guides/ADVANCED-TROUBLESHOOTING-GUIDE.md`
- General Usage: `guides/USAGE.md`
- ExecPlan JSON schema: `guides/EXECPLAN-SCHEMA.md`

### Phases
- Natural Language Requirements: `phases/PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md`
- Runtime Conformance: `phases/PHASE-2-2-RUNTIME-CONFORMANCE.md`
- Integration Testing / E2E: `phases/PHASE-2-3-INTEGRATION-TESTING.md`
- User Stories, Validation, DDD Modeling, Phase 6 UI/UX, Telemetry

### Integrations
- Claude Code Task Tool Integration: `integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`
- Claude Code Workflow: `integrations/CLAUDECODE-WORKFLOW.md`
- CodeX Integration (PoC/MCP/Adapter): `integrations/CODEX-INTEGRATION.md`

### Reference
- CLI Commands: `reference/CLI-COMMANDS-REFERENCE.md`
- API Reference: `reference/API.md`
 - Legacy ExecPlan (6-phase, deprecated): `../plans/archive/legacy-6-phase.md`

### Architecture
- TDD Framework Architecture: `architecture/TDD-FRAMEWORK-ARCHITECTURE.md`
- CEGIS Design: `architecture/CEGIS-DESIGN.md`
- Runtime Conformance Design: `architecture/RUNTIME-CONFORMANCE-DESIGN.md`

### Quality / Verification
- Formal Quality Gates (DoD v0.2): `quality/formal-gates.md`
- Ownership DoD: `quality/ownership-dod.md`
- LLM first-pass review checklist: `quality/llm-first-review-checklist.md`
- Guarded automation template: `quality/guarded-automation-template.md`
- Incident triage template: `quality/incident-triage-template.md`
- Adoption sample flow: `quality/adoption-sample-flow.md`
- Runbooks / Traceability / Runtime Contracts: see `docs/quality` and `docs/verify`
 - Coverage policy: `quality/coverage-policy.md`（しきい値の由来/Required化の運用）
 - Formal runbook: `quality/formal-runbook.md`（ラベル/dispatch/要約/環境変数）

For the complete navigation with highlights, see the Japanese section below (same links).

---

> AI-Enhanced Development Framework の包括的ドキュメント

## 🚀 はじめに

ae-frameworkは、AI-Powered TDDによる6フェーズでソフトウェア開発を自動化するフレームワークです。Claude Codeと統合し、要件分析からUI/UX実装まで一気通貫でサポートします。

## 📖 ドキュメント構成

### 🏁 [getting-started/](./getting-started/) - 導入・クイックスタート
最初に読むべきドキュメント群

- **[QUICK-START-GUIDE.md](./getting-started/QUICK-START-GUIDE.md)** ⭐ **推奨** - 15分で始めるae-framework
- **[PHASE-6-GETTING-STARTED.md](./getting-started/PHASE-6-GETTING-STARTED.md)** ⭐ **最新** - Phase 6 UI/UX専用クイックスタート  
- [SETUP.md](./getting-started/SETUP.md) - 基本セットアップ手順

### 📖 [guides/](./guides/) - 実用ガイド・チュートリアル
実際の開発で使える実用ガイド

- **[DEVELOPMENT-INSTRUCTIONS-GUIDE.md](./guides/DEVELOPMENT-INSTRUCTIONS-GUIDE.md)** ⭐ **最新** - 開発指示の具体的方法
- **[CLAUDE-CODE-AUTOMATION-GUIDE.md](./guides/CLAUDE-CODE-AUTOMATION-GUIDE.md)** ⭐ **重要** - Claude Code完全自動化
- **🆕 [PHASE-2-ADVANCED-FEATURES-GUIDE.md](./guides/PHASE-2-ADVANCED-FEATURES-GUIDE.md)** ⭐ **NEW** - Phase 2.1-2.3統合ガイド
- **🆕 [ADVANCED-TROUBLESHOOTING-GUIDE.md](./guides/ADVANCED-TROUBLESHOOTING-GUIDE.md)** ⭐ **NEW** - 高度な機能のトラブルシューティング
- [USAGE.md](./guides/USAGE.md) - 一般的な使い方ガイド
- [test-generation-guide.md](./guides/test-generation-guide.md) - テスト生成ガイド
- [EXECPLAN-SCHEMA.md](./guides/EXECPLAN-SCHEMA.md) - ExecPlan JSONスキーマ

### 🎯 [phases/](./phases/) - フェーズ別詳細ドキュメント
6フェーズの詳細仕様とガイド

- [PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md](./phases/PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md) - 自然言語要件処理
- **🆕 [PHASE-2-2-RUNTIME-CONFORMANCE.md](./phases/PHASE-2-2-RUNTIME-CONFORMANCE.md)** ⭐ **NEW** - リアルタイム適合性検証システム
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

### 📚 [reference/](./reference/) - リファレンス・API仕様
コマンドやAPIの詳細仕様

- **[CLI-COMMANDS-REFERENCE.md](./reference/CLI-COMMANDS-REFERENCE.md)** ⭐ **重要** - 全CLIコマンドリファレンス
- [API.md](./reference/API.md) - API仕様
- [legacy-6-phase.md](../plans/archive/legacy-6-phase.md) - 旧6フェーズExecPlan（非推奨）

### 🏗️ [architecture/](./architecture/) - アーキテクチャ・設計
システム設計と新機能仕様

- **[TDD-FRAMEWORK-ARCHITECTURE.md](./architecture/TDD-FRAMEWORK-ARCHITECTURE.md)** ⭐ **重要** - TDDフレームワーク設計
- **🆕 [CEGIS-DESIGN.md](./architecture/CEGIS-DESIGN.md)** ⭐ **NEW** - CEGIS自動修復システム設計
- **🆕 [RUNTIME-CONFORMANCE-DESIGN.md](./architecture/RUNTIME-CONFORMANCE-DESIGN.md)** ⭐ **NEW** - Runtime Conformance設計
- [ARCHITECTURE.md](./architecture/ARCHITECTURE.md) - システムアーキテクチャ
- [NEW_FEATURES.md](./architecture/NEW_FEATURES.md) - 新機能仕様

### ✅ [quality/](./quality/) - 品質ゲート・検証
フォーマル検証や品質基準

- **[formal-gates.md](./quality/formal-gates.md)** ⭐ フォーマル品質ゲート（v0.2 DoD）
- [ownership-dod.md](./quality/ownership-dod.md) - Ownership DoD（説明責任/運用/ロールバック）
- [llm-first-review-checklist.md](./quality/llm-first-review-checklist.md) - LLM一次レビューの標準チェック
- [guarded-automation-template.md](./quality/guarded-automation-template.md) - Guarded automation 運用テンプレ
- [incident-triage-template.md](./quality/incident-triage-template.md) - インシデント一次切り分けテンプレ
- [adoption-sample-flow.md](./quality/adoption-sample-flow.md) - 導入の最小フロー（エンドツーエンド）
- [formal-runbook.md](./quality/formal-runbook.md) - 実行・運用手順（ラベルゲート/手動実行）
- [formal-tools-setup.md](./quality/formal-tools-setup.md) - ローカル環境セットアップ（Apalache/TLC/Z3/cvc5）
 - [formal-mini-flow.md](./quality/formal-mini-flow.md) - 反例→失敗テスト→修正→緑の最小フロー

### 📐 [spec/](./spec/) - 仕様レジストリ
仕様の配置と規約

- **[registry.md](./spec/registry.md)** ⭐ 仕様配置レジストリ（TLA+/Alloy/Cedar/Trace）

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
- **Discord**: リアルタイム質問・情報交換

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
