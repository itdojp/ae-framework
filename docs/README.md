# 📚 ae-framework Documentation

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
- [USAGE.md](./guides/USAGE.md) - 一般的な使い方ガイド
- [test-generation-guide.md](./guides/test-generation-guide.md) - テスト生成ガイド

### 🎯 [phases/](./phases/) - フェーズ別詳細ドキュメント
6フェーズの詳細仕様とガイド

- [PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md](./phases/PHASE-2-NATURAL-LANGUAGE-REQUIREMENTS.md) - 自然言語要件処理
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

### 🏗️ [architecture/](./architecture/) - アーキテクチャ・設計
システム設計と新機能仕様

- **[TDD-FRAMEWORK-ARCHITECTURE.md](./architecture/TDD-FRAMEWORK-ARCHITECTURE.md)** ⭐ **重要** - TDDフレームワーク設計
- [ARCHITECTURE.md](./architecture/ARCHITECTURE.md) - システムアーキテクチャ
- [NEW_FEATURES.md](./architecture/NEW_FEATURES.md) - 新機能仕様

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

## 🔄 更新履歴

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