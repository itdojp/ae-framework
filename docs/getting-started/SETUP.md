# AE Framework Setup Guide

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Installation and setup guide for AE Framework's complete 6-phase agent system and MCP server**

### 📋 Prerequisites

#### System Requirements
- **Node.js**: 18.0.0 or higher
- **pnpm**: 8.0.0 or higher (recommended package manager)
- **TypeScript**: 5.5.0 or higher
- **Git**: 2.0 or higher
- **Playwright**: 1.47.0 or higher (for E2E testing)

#### Recommended Environment
- **OS**: Linux, macOS, Windows (WSL2 recommended)
- **Memory**: 4GB or more
- **Storage**: 1GB+ free space

### 🚀 Installation

#### 1. Clone Repository

```bash
git clone https://github.com/itdojp/ae-framework.git
cd ae-framework
```

#### 2. Install Dependencies

**Using pnpm (recommended):**
```bash
pnpm install
```

**Using npm also possible:**
```bash
npm install
```

#### 3. Phase 6 Playwright Setup

Install Playwright browsers for E2E testing and visual regression testing:

```bash
npx playwright install
```

#### 4. TypeScript Build

```bash
pnpm run build
```

#### 5. Git Hooks Setup (Optional)

Set up pre-commit hooks to enable TDD enforcement features:

```bash
pnpm run setup-hooks
```

### 🔧 Configuration

#### 1. Environment Variables

Create `.env` file with the following configuration:

```bash
# OpenTelemetry (optional)
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
OTEL_SERVICE_NAME=ae-framework

# Database configuration (optional)
DATABASE_URL=postgresql://username:password@localhost:5432/ae-framework

# Log level
LOG_LEVEL=info
```

#### 2. Claude Code Integration Setup

**Automatic Integration (Recommended):**
ae-framework is automatically integrated as Claude Code Task Tool. No additional setup required.

**MCP Server Setup (Optional):**

Configuration file example for using MCP Server in Claude Code:

```json
{
  "mcpServers": {
    "ae-intent": {
      "command": "npx",
      "args": ["tsx", "src/mcp-server/intent-server.ts"],
      "cwd": "/path/to/ae-framework",
      "env": {
        "NODE_ENV": "production"
      }
    },
    "ae-formal": {
      "command": "npx", 
      "args": ["tsx", "src/mcp-server/formal-server.ts"],
      "cwd": "/path/to/ae-framework"
    },
    "ae-test": {
      "command": "npx",
      "args": ["tsx", "src/mcp-server/test-generation-server.ts"], 
      "cwd": "/path/to/ae-framework"
    }
  }
}
```

### ✅ Installation Verification

#### 1. Build Verification

```bash
pnpm run build
# Confirm no errors appear
```

#### 2. Test Execution

```bash
# Run all tests
pnpm test

# Vitest Projects separated testing
pnpm run test:unit      # Unit tests (10s timeout)
pnpm run test:int       # Integration tests (60s timeout)
pnpm run test:perf      # Performance tests (180s timeout)

# Fast test execution (CI optimized)
pnpm run test:fast

# Confirm all tests pass
```

#### 3. Lint Check

```bash
pnpm run lint
# Confirm no lint warnings/errors
```

#### 4. Agent Operation Verification

**Intent Agent**
```bash
pnpm run intent-agent
# Should display "Intent Agent MCP server running on stdio"
```

**Test Generation Agent**
```bash
pnpm run mcp:test
# Should display "Test Generation MCP server running on stdio"
```

**UI Generation Agent (Phase 6)**
```bash
pnpm run ui:server
# Should display "UI Generation MCP server running on stdio"
```

#### 5. Latest CI/CD System Verification ✨ **NEW**

**Fast CI Pipeline Check**
```bash
# Fast CI (under 5 minutes)
pnpm run test:unit
pnpm run lint
```

**Quality Gates Check**
```bash
# Quality gates (under 15 minutes)
pnpm run test:int
pnpm run test:a11y
pnpm run test:coverage
```

**Flake Detection & Isolation System**
```bash
# Flake detection
pnpm run flake:detect

# Flake isolation management
pnpm run flake:list
pnpm run flake:report
```

**Performance Budget System**
```bash
# Performance budget check
pnpm run perf:budgets
pnpm run test:budgets
```

### 🛠️ Development Environment Setup

#### 1. Development Watch Mode

Start agents in development mode (auto-restart on file changes):

```bash
# Intent Agent (development)
pnpm run intent-agent:build

# Formal Agent (development)  
pnpm run formal-agent:dev

# UI Generation Agent (development)
pnpm run ui:dev
```

#### 2. Coverage Measurement

```bash
pnpm run coverage
# Coverage report will be generated
```

#### 3. Quality Analysis

```bash
# Project-wide quality analysis
pnpm run quality:scorecard
pnpm run package:quality

# Security analysis
pnpm run security:full

# Accessibility analysis
pnpm run accessibility:full
```

### 🔍 Troubleshooting

#### Common Issues and Solutions

**1. Node.js Version Error**
```bash
Error: Node.js version 16.x is not supported
```
**Solution**: Update to Node.js 18 or higher

**2. TypeScript Compile Error**
```bash
error TS2307: Cannot find module './types.js'
```
**Solution**: ES module format requires `.js` extension
```typescript
// ❌ Wrong
import { Type } from './types';

// ✅ Correct  
import { Type } from './types.js';
```

**3. MCP Server Connection Error**
```bash
MCP server connection failed
```
**Solution**: 
- Check path (use absolute path)
- Check permissions (execution permission)
- Check Node.js version

**4. Playwright Browser Error**
```bash
Error: Browser not found. Please run 'npx playwright install'
```
**Solution**: 
```bash
npx playwright install
```

**5. Performance Budget Error** ✨ **NEW**
```bash
Error: Performance budget validation failed
```
**Solution**:
```bash
# Check performance budget settings
cat config/performance-budgets.json

# Individual budget check
pnpm run perf:budgets:dev
pnpm run perf:budgets:prod
```

### 📚 Next Steps

Once installation is complete, refer to the [Usage Guide](./USAGE.md) to learn how to use each agent.

### 🆘 Support

If issues persist, you can get support through:

1. Report on [GitHub Issues](https://github.com/itdojp/ae-framework/issues)
2. Check logs (detailed output from `npm run build`)
3. Check environment information:
   ```bash
   node --version
   npm --version
   npx tsc --version
   ```

### 📝 Updates

Update to latest version:

```bash
git pull origin main
pnpm install
pnpm run build
```

Regular updates are recommended to get the latest features and fixes.

---

## Japanese

**ae-frameworkの全6フェーズエージェントとMCPサーバーのインストール・セットアップ方法について説明します**

### 📋 前提条件

#### システム要件
- **Node.js**: 18.0.0 以上
- **pnpm**: 8.0.0 以上 (推奨パッケージマネージャー)
- **TypeScript**: 5.5.0 以上
- **Git**: 2.0 以上
- **Playwright**: 1.47.0 以上 (E2Eテスト用)

#### 推奨環境
- **OS**: Linux, macOS, Windows (WSL2推奨)
- **メモリ**: 4GB以上
- **ストレージ**: 1GB以上の空き容量

### 🚀 インストール

#### 1. リポジトリのクローン

```bash
git clone https://github.com/itdojp/ae-framework.git
cd ae-framework
```

#### 2. 依存関係のインストール

**pnpm使用（推奨）:**
```bash
pnpm install
```

**npmでも可能:**
```bash
npm install
```

#### 3. Phase 6 Playwright設定

E2Eテストと視覚回帰テスト用のPlaywrightブラウザをインストール：

```bash
npx playwright install
```

#### 4. TypeScriptのビルド

```bash
pnpm run build
```

#### 5. Git Hooksの設定（オプション）

TDD強制機能を有効にするためのpre-commitフックを設定：

```bash
pnpm run setup-hooks
```

### 🔧 設定

#### 1. 環境変数の設定

`.env`ファイルを作成して以下を設定：

```bash
# OpenTelemetry (オプション)
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
OTEL_SERVICE_NAME=ae-framework

# データベース設定 (オプション)
DATABASE_URL=postgresql://username:password@localhost:5432/ae-framework

# ログレベル
LOG_LEVEL=info
```

#### 2. Claude Code 統合設定

**自動統合（推奨）:**
ae-framework は Claude Code Task Tool として自動統合されています。追加設定は不要です。

**MCP サーバー設定（オプション）:**

Claude Code で MCP Server も使用する場合の設定ファイル例：

```json
{
  "mcpServers": {
    "ae-intent": {
      "command": "npx",
      "args": ["tsx", "src/mcp-server/intent-server.ts"],
      "cwd": "/path/to/ae-framework",
      "env": {
        "NODE_ENV": "production"
      }
    },
    "ae-formal": {
      "command": "npx", 
      "args": ["tsx", "src/mcp-server/formal-server.ts"],
      "cwd": "/path/to/ae-framework"
    },
    "ae-test": {
      "command": "npx",
      "args": ["tsx", "src/mcp-server/test-generation-server.ts"], 
      "cwd": "/path/to/ae-framework"
    }
  }
}
```

### ✅ インストール確認

#### 1. ビルドの確認

```bash
pnpm run build
# エラーが出ないことを確認
```

#### 2. テストの実行

```bash
# 全テスト実行
pnpm test

# Vitest Projects分離テスト
pnpm run test:unit      # ユニットテスト (10秒タイムアウト)
pnpm run test:int       # 統合テスト (60秒タイムアウト)
pnpm run test:perf      # パフォーマンステスト (180秒タイムアウト)

# 高速テスト実行 (CI最適化版)
pnpm run test:fast

# 全てのテストがパスすることを確認
```

#### 3. Lintチェック

```bash
pnpm run lint
# Lint警告/エラーがないことを確認
```

#### 4. 各エージェントの動作確認

**Intent Agent**
```bash
pnpm run intent-agent
# "Intent Agent MCP server running on stdio" が表示されればOK
```

**Test Generation Agent**
```bash
pnpm run mcp:test
# "Test Generation MCP server running on stdio" が表示されればOK
```

**UI Generation Agent (Phase 6)**
```bash
pnpm run ui:server
# "UI Generation MCP server running on stdio" が表示されればOK
```

#### 5. Issue #127 最新CI/CDシステムの動作確認 ✨ **NEW**

**Fast CI Pipeline確認**
```bash
# 高速CI (5分以内)
pnpm run test:unit
pnpm run lint
```

**Quality Gates確認**
```bash
# 品質ゲート (15分以内)
pnpm run test:int
pnpm run test:a11y
pnpm run test:coverage
```

**フレーク検知・隔離システム**
```bash
# フレーク検知
pnpm run flake:detect

# フレーク隔離管理
pnpm run flake:list
pnpm run flake:report
```

**パフォーマンス予算システム**
```bash
# パフォーマンス予算チェック
pnpm run perf:budgets
pnpm run test:budgets
```

### 🛠️ 開発環境のセットアップ

#### 1. 開発用監視モード

各エージェントを開発モードで起動（ファイル変更時の自動再起動）：

```bash
# Intent Agent (開発用)
pnpm run intent-agent:build

# Formal Agent (開発用)  
pnpm run formal-agent:dev

# UI Generation Agent (開発用)
pnpm run ui:dev
```

#### 2. カバレッジ測定

```bash
pnpm run coverage
# カバレッジレポートが生成される
```

#### 3. 品質分析

```bash
# プロジェクト全体の品質分析
pnpm run quality:scorecard
pnpm run package:quality

# セキュリティ分析
pnpm run security:full

# アクセシビリティ分析
pnpm run accessibility:full
```

### 🔍 トラブルシューティング

#### よくある問題と解決方法

**1. Node.js バージョンエラー**
```bash
Error: Node.js version 16.x is not supported
```
**解決方法**: Node.js 18以上にアップデート

**2. TypeScriptコンパイルエラー**
```bash
error TS2307: Cannot find module './types.js'
```
**解決方法**: ESモジュール形式で`.js`拡張子が必要
```typescript
// ❌ 間違い
import { Type } from './types';

// ✅ 正しい  
import { Type } from './types.js';
```

**3. MCPサーバー接続エラー**
```bash
MCP server connection failed
```
**解決方法**: 
- パスの確認（絶対パスを使用）
- 権限の確認（実行権限があるか）
- Node.jsのバージョン確認

**4. Playwright ブラウザエラー**
```bash
Error: Browser not found. Please run 'npx playwright install'
```
**解決方法**: 
```bash
npx playwright install
```

**5. パフォーマンス予算エラー** ✨ **NEW**
```bash
Error: Performance budget validation failed
```
**解決方法**:
```bash
# パフォーマンス予算設定確認
cat config/performance-budgets.json

# 個別予算チェック
pnpm run perf:budgets:dev
pnpm run perf:budgets:prod
```

### 📚 次のステップ

インストールが完了したら、[使い方ガイド](./USAGE.md)を参照して各エージェントの使用方法を確認してください。

### 🆘 サポート

問題が解決しない場合は、以下の方法でサポートを受けられます：

1. [GitHub Issues](https://github.com/itdojp/ae-framework/issues) での報告
2. ログの確認（`npm run build`の詳細出力）
3. 環境情報の確認：
   ```bash
   node --version
   npm --version
   npx tsc --version
   ```

### 📝 アップデート

最新版への更新：

```bash
git pull origin main
pnpm install
pnpm run build
```

定期的に更新して最新の機能と修正を入手することを推奨します。

---

**🚀 Ready to start developing with AE Framework! / AE Frameworkでの開発準備完了です！**