# AE Framework Integration Guide

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**AE Framework Integration Methods and Setup Guide**

### 📋 Integration Methods Overview

#### 🤖 Claude Code Integration (Primary Integration)
- **File**: [CLAUDE-CODE-TASK-TOOL-INTEGRATION.md](./CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)
- **Overview**: Seamless workflow from natural language to UI generation via Claude Code Task Tool integration
- **Features**: 
  - 🚀 21 files UI generation in 30 seconds
  - 🛡️ Automatic WCAG 2.1 AA compliance
  - 📊 Lighthouse >90 automatic achievement
  - 🔧 Full TypeScript support

#### 🔧 Task Tool Integration
- **File**: [CLAUDE-CODE-TASK-TOOL-INTEGRATION.md](./CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)
- **Overview**: Detailed Claude Code Task Tool specifications and implementation guide
- **Features**:
  - Complete automation of Phase 1-6
  - Proactive guidance
  - Quality gate integration

#### 🔌 MCP Server Integration
- **File**: [MCP-SERVER-INTEGRATION.md](./MCP-SERVER-INTEGRATION.md)
- **Overview**: Model Context Protocol Server implementation
- **Features**:
  - Backup integration method
  - Standalone execution support

#### 💻 CLI Integration
- **File**: [CLI-INTEGRATION-GUIDE.md](./CLI-INTEGRATION-GUIDE.md)
- **Overview**: Command line integration and script execution
- **Features**:
  - Direct execution for developers
  - CI/CD integration support

### 🎯 Recommended Integration Order

#### 1. Claude Code Integration (Highest Priority)
```bash
# Natural language instructions only in Claude Code environment
User: "Please create an e-commerce product management feature"
→ Complete web application in under 4 minutes
```

#### 2. CLI Integration (For Developers)
```bash
# Direct command line execution
npx ae-framework generate --domain "Product Management" --ui react
```

#### 3. MCP Server Integration (Backup)
```bash
# Execution via MCP Server
npm run mcp:start
```

### 📊 Integration Method Comparison

| Integration Method | Ease of Use | Feature Completeness | Speed | Recommended Use |
|-------------------|-------------|---------------------|-------|-----------------|
| Claude Code | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | **Primary Use** |
| CLI | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | Direct developer execution |
| MCP Server | ⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | Backup |

### 🚀 Quick Start

#### Using Claude Code Environment
```
User: "Create an inventory management system"

Claude Code: Analyzing requirements with Intent Task Adapter...
✅ Phase 1 Complete → Executing Phase 2...
✅ Phase 2 Complete → Executing Phase 3...
...
✅ Phase 6 Complete: React UI generated (21 files/30 seconds)
```

#### Direct Use in Development Environment
```bash
# Installation
npm install -g ae-framework

# Execute UI generation
ae-framework ui scaffold --input domain-model.json
```

### 📚 Detailed Documentation

- **[Claude Code Integration Guide](./CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)** - 🔥 Primary integration method
- **[Technical Implementation Details](../architecture/TECHNICAL-IMPLEMENTATION-DETAILS.md)** - Architecture details
- **[Phase 6 UI Generation](../phases/phase-6-uiux.md)** - UI auto-generation details
- **[Quality Assurance System](../quality/quality-implementation-status.md)** - Quality management details

### 🎯 Next Steps

1. **Review [Claude Code Integration Guide](./CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)**
2. **Try in actual development project**
3. **Provide feedback and improvement suggestions**

---

## Japanese

**AE Framework の各種統合方式とセットアップガイド**

### 📋 統合方式一覧

#### 🤖 Claude Code統合 (メイン統合)
- **ファイル**: [CLAUDE-CODE-TASK-TOOL-INTEGRATION.md](./CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)
- **概要**: Claude Code Task Tool統合による自然言語からUI生成まで一貫ワークフロー
- **特徴**: 
  - 🚀 30秒で21ファイルUI生成
  - 🛡️ WCAG 2.1 AA自動準拠
  - 📊 Lighthouse >90自動達成
  - 🔧 完全TypeScript対応

#### 🔧 Task Tool統合
- **ファイル**: [CLAUDE-CODE-TASK-TOOL-INTEGRATION.md](./CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)
- **概要**: Claude Code Task Tool仕様詳細と実装ガイド
- **特徴**:
  - Phase 1-6の完全自動化
  - プロアクティブガイダンス
  - 品質ゲート統合

#### 🔌 MCP Server統合
- **ファイル**: [MCP-SERVER-INTEGRATION.md](./MCP-SERVER-INTEGRATION.md)
- **概要**: Model Context Protocol Server実装
- **特徴**:
  - バックアップ統合方式
  - スタンドアロン実行対応

#### 💻 CLI統合
- **ファイル**: [CLI-INTEGRATION-GUIDE.md](./CLI-INTEGRATION-GUIDE.md)
- **概要**: コマンドライン統合とスクリプト実行
- **特徴**:
  - 開発者向け直接実行
  - CI/CD統合対応

### 🎯 推奨統合順序

#### 1. Claude Code統合 (最優先)
```bash
# Claude Code環境で自然言語指示のみ
User: "ECサイトの商品管理機能を作ってください"
→ 4分以内で完全なWebアプリケーション完成
```

#### 2. CLI統合 (開発者向け)
```bash
# コマンドライン直接実行
npx ae-framework generate --domain "商品管理" --ui react
```

#### 3. MCP Server統合 (バックアップ)
```bash
# MCP Server経由実行
npm run mcp:start
```

### 📊 統合方式比較

| 統合方式 | 使いやすさ | 機能完全性 | 速度 | 推奨用途 |
|----------|------------|------------|------|----------|
| Claude Code | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | **メイン使用** |
| CLI | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 開発者直接実行 |
| MCP Server | ⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | バックアップ |

### 🚀 クイックスタート

#### Claude Code環境での使用
```
User: "在庫管理システムを作成してください"

Claude Code: Intent Task Adapterで要件分析中...
✅ Phase 1完了 → Phase 2実行...
✅ Phase 2完了 → Phase 3実行...
...
✅ Phase 6完了: React UI生成 (21ファイル/30秒)
```

#### 開発環境での直接使用
```bash
# インストール
npm install -g ae-framework

# UI生成実行
ae-framework ui scaffold --input domain-model.json
```

### 📚 詳細ドキュメント

- **[Claude Code統合ガイド](./CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)** - 🔥 メイン統合方式
- **[技術実装詳細](../architecture/TECHNICAL-IMPLEMENTATION-DETAILS.md)** - アーキテクチャ詳細
- **[Phase 6 UI生成](../phases/phase-6-uiux.md)** - UI自動生成詳細
- **[品質保証システム](../quality/quality-implementation-status.md)** - 品質管理詳細

### 🎯 次のステップ

1. **[Claude Code統合ガイド](./CLAUDE-CODE-TASK-TOOL-INTEGRATION.md)を確認**
2. **実際の開発プロジェクトで試用**
3. **フィードバックと改善提案**

---

**🌟 Experience next-generation AI development with AE Framework! / AE Frameworkで次世代AI開発を体験しましょう！**