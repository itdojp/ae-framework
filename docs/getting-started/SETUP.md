# AE Framework Setup Guide

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Installation and setup guide for ae-framework's current assurance control plane baseline**

### 📋 Prerequisites

#### System Requirements
- **Node.js**: 20.11 以上（22系でも動作確認済み）
- **pnpm**: 10.0.0（`package.json` の `packageManager` と一致させる）
- **TypeScript**: 5.9.x 以上
- **Git**: 2.0 or higher
- **Playwright**: 1.47.0 or higher (for E2E testing)

#### Recommended Environment
- **OS**: Linux, macOS, Windows (WSL2 recommended)
- **Memory**: 4GB or more
- **Storage**: 1GB+ free space

### 🚀 Installation

Note: With Node.js 20.11+ (<23), enable Corepack to use the bundled pnpm:
```bash
corepack enable
corepack prepare pnpm@10.0.0 --activate
```

#### 1. Clone Repository

```bash
git clone https://github.com/itdojp/ae-framework.git
cd ae-framework
```

#### 2. Install Dependencies

**Using pnpm (recommended):**
```bash
# CI環境等でロックファイルの読み書きが制限されている場合は --no-frozen-lockfile を使用
pnpm install --no-frozen-lockfile
```

Lockfile reproducibility self-check (optional):
```bash
pnpm run ci:lockfile:verify
```

注: このプロジェクトは pnpm を前提としています。

#### 3. Phase 6 Playwright Setup

Install Playwright browsers for E2E testing and visual regression testing:

```bash
npx playwright install
```

#### 4. Baseline Verification

```bash
pnpm run first-run
pnpm run verify:lite
```

Check:
- `artifacts/first-run/**`
- `artifacts/verify-lite/verify-lite-run-summary.json`

#### 5. Assurance Summary (Optional)

```bash
pnpm run verify:assurance \
  --assurance-profile fixtures/assurance/sample.assurance-profile.json \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --output-json artifacts/assurance/assurance-summary.json \
  --output-md artifacts/assurance/assurance-summary.md
node scripts/ci/validate-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json \
  schema/assurance-summary.schema.json
```

For project onboarding and strict/report-only operations:
- `docs/guides/assurance-onboarding-checklist.md`
- `docs/quality/assurance-operations-runbook.md`

#### 6. Git Hooks Setup (Optional)

Set up pre-commit hooks to enable TDD enforcement features:

```bash
pnpm run setup-hooks
```

### 🔎 Command Discovery

After setup, use the following commands to discover available scripts and consolidated runners:

```bash
# Script groups and consolidated runner entry points
pnpm run help

# CLI parity with pnpm run help
pnpm exec ae help

# Project setup templates (optional)
pnpm exec ae setup list
pnpm exec ae setup suggest
pnpm exec ae setup wizard
```

See `docs/reference/CLI-COMMANDS-REFERENCE.md` and `docs/guides/CLI-MIGRATION.md` for the full CLI reference and migration details.

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

#### 1. Baseline Verification

```bash
pnpm run first-run
pnpm run verify:lite
# Confirm no errors appear and verify-lite summary is generated
```

#### 2. Assurance Verification (Optional)

```bash
pnpm run verify:assurance \
  --assurance-profile fixtures/assurance/sample.assurance-profile.json \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --output-json artifacts/assurance/assurance-summary.json \
  --output-md artifacts/assurance/assurance-summary.md
node scripts/ci/validate-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json \
  schema/assurance-summary.schema.json
```

#### 3. Test Execution

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

#### 4. Lint Check

```bash
pnpm run lint
# Confirm no lint warnings/errors
```

#### 5. Agent Operation Verification

**Intent Agent**
```bash
pnpm run intent-agent
# Should display "Intent Agent MCP server running on stdio"
```

**Test Generation Agent**
```bash
pnpm run mcp:test
# The MCP server starts and waits for stdio requests (it may not print a startup log)
```

**Operate Agent (Phase 6)**
```bash
pnpm run operate:server
# Should display "Operate MCP server running on stdio"
```

#### 6. Latest CI/CD System Verification ✨ **NEW**

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
備考: 一部のテスト/型チェックは既知の制約により失敗する場合があります。ハンドオフREADMEの対象テスト（ベンチマーク系）での確認を推奨します。

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

# Operate Agent (development)
pnpm run operate:dev
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
**Solution**: Update to Node.js 20.11 or higher

**2. TypeScript Compile Error**
```bash
error TS2307: Cannot find module './types.js'
```
**Solution**: ES module format requires `.js` extension（verbatimModuleSyntax 対応）
```typescript
// ❌ Wrong
const wrongImportPath = './types';

// ✅ Correct  
const correctImportPath = './types.js';
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

Once installation is complete, refer to the [Usage Guide](../guides/USAGE.md) to learn how to use each agent.

### 🆘 Support

If issues persist, you can get support through:

1. Report on [GitHub Issues](https://github.com/itdojp/ae-framework/issues)
2. Check logs (detailed output from `pnpm run build`)
3. Check environment information:
   ```bash
   node --version
   pnpm --version
   corepack --version
   npx tsc --version
   ```

### 📝 Updates

Update to latest version:

```bash
git pull origin main
pnpm install
pnpm run build
```

### 🔎 Quick Functional Checks（CLI）

代表的なCLIの動作確認例です。

```bash
# Runtime Conformance（サンプル生成→検証）
pnpm tsx src/cli/conformance-cli.ts sample \
  --rules configs/samples/sample-rules.json \
  --config configs/samples/sample-config.json \
  --data configs/samples/sample-data.json \
  --context configs/samples/sample-context.json

pnpm tsx src/cli/conformance-cli.ts verify \
  --input configs/samples/sample-data.json \
  --context-file configs/samples/sample-context.json \
  --rules configs/samples/sample-rules.json \
  --format json --output artifacts/conformance/conformance-results.json

# SBOM 生成（依存グラフ抽出はロックファイルが無い場合に警告）
pnpm tsx src/cli/index.ts sbom generate --format json --output sbom.json --verbose

# 脆弱性情報付き SBOM（OSV querybatch 連携）
pnpm tsx src/cli/index.ts sbom generate --format json --include-vulns --output sbom.json --verbose
# 連携先/タイムアウトの調整（任意）
SBOM_OSV_ENDPOINT="https://api.osv.dev/v1/querybatch" SBOM_OSV_TIMEOUT_MS=10000 \
  pnpm tsx src/cli/index.ts sbom generate --format json --include-vulns --output sbom.json

# UI Scaffold（Dry Run）
pnpm tsx src/cli/ui-scaffold-cli.ts generate \
  --state samples/phase-state.example.json \
  --output ./.ae/ui --dry-run

# ベンチマーク一覧とドライラン
pnpm tsx src/cli/benchmark-cli.ts list --enabled-only
pnpm tsx src/cli/benchmark-cli.ts run --ci --dry-run

# セキュリティ設定の表示
pnpm tsx src/cli/index.ts security show-config --env development
```

`--include-vulns` は OSV API を参照します。レート制限・ネットワーク障害時は SBOM 生成自体は失敗させず、警告ログを出して `vulnerabilities: []` を返します。

Regular updates are recommended to get the latest features and fixes.

---

## Japanese

**ae-framework の現行 assurance control plane baseline をセットアップする手順です**

### 📋 前提条件

#### システム要件
- **Node.js**: 20.11 以上（<23）
- **pnpm**: 10.0.0（`package.json` の `packageManager` と一致）
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

```bash
corepack enable
corepack prepare pnpm@10.0.0 --activate
```

**pnpm使用（推奨）:**
```bash
pnpm install --no-frozen-lockfile
```

注: このプロジェクトは pnpm を前提としています。

Lockfile の再現性確認（任意）:
```bash
pnpm run ci:lockfile:verify
```

#### 3. Baseline 検証

```bash
pnpm run first-run
pnpm run verify:lite
```

確認対象:
- `artifacts/first-run/**`
- `artifacts/verify-lite/verify-lite-run-summary.json`

#### 4. Assurance Summary（任意）

```bash
pnpm run verify:assurance \
  --assurance-profile fixtures/assurance/sample.assurance-profile.json \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --output-json artifacts/assurance/assurance-summary.json \
  --output-md artifacts/assurance/assurance-summary.md
node scripts/ci/validate-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json \
  schema/assurance-summary.schema.json
```

運用詳細:
- `docs/guides/assurance-onboarding-checklist.md`
- `docs/quality/assurance-operations-runbook.md`

#### 5. Phase 6 Playwright設定

E2Eテストと視覚回帰テスト用のPlaywrightブラウザをインストール：

```bash
npx playwright install
```

#### 6. TypeScriptのビルド

```bash
pnpm run build
```

#### 7. Git Hooksの設定（オプション）

TDD強制機能を有効にするためのpre-commitフックを設定：

```bash
pnpm run setup-hooks
```

### 🔎 コマンドの確認

セットアップ後に利用できるスクリプトと統一 runner を確認します。

```bash
# スクリプト群と統一 runner の一覧
pnpm run help

# CLI から同等の一覧を表示
pnpm exec ae help

# テンプレート導入（任意）
pnpm exec ae setup list
pnpm exec ae setup suggest
pnpm exec ae setup wizard
```

詳細は `docs/reference/CLI-COMMANDS-REFERENCE.md` と `docs/guides/CLI-MIGRATION.md` を参照してください。

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

#### 1. Baseline の確認

```bash
pnpm run first-run
pnpm run verify:lite
# エラーが出ず、verify-lite summary が生成されることを確認
```

#### 2. Assurance の確認（任意）

```bash
pnpm run verify:assurance \
  --assurance-profile fixtures/assurance/sample.assurance-profile.json \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --output-json artifacts/assurance/assurance-summary.json \
  --output-md artifacts/assurance/assurance-summary.md
node scripts/ci/validate-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json \
  schema/assurance-summary.schema.json
```

#### 3. テストの実行

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

#### 4. Lintチェック

```bash
pnpm run lint
# Lint警告/エラーがないことを確認
```

#### 5. 各エージェントの動作確認

**Intent Agent**
```bash
pnpm run intent-agent
# "Intent Agent MCP server running on stdio" が表示されればOK
```

**Test Generation Agent**
```bash
pnpm run mcp:test
# 起動し、stdio のリクエスト待ち状態になればOK（明示ログが出ない場合があります）
```

**Operate Agent (Phase 6)**
```bash
pnpm run operate:server
# "Operate MCP server running on stdio" が表示されればOK
```

#### 6. Issue #127 最新CI/CDシステムの動作確認 ✨ **NEW**

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

# Operate Agent (開発用)
pnpm run operate:dev
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
**解決方法**: Node.js 20.11以上（<23）にアップデート

**2. TypeScriptコンパイルエラー**
```bash
error TS2307: Cannot find module './types.js'
```
**解決方法**: ESモジュール形式で`.js`拡張子が必要
```typescript
// ❌ 間違い
const wrongImportPath = './types';

// ✅ 正しい  
const correctImportPath = './types.js';
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

インストールが完了したら、[使い方ガイド](../guides/USAGE.md)を参照して各エージェントの使用方法を確認してください。

### 🆘 サポート

問題が解決しない場合は、以下の方法でサポートを受けられます：

1. [GitHub Issues](https://github.com/itdojp/ae-framework/issues) での報告
2. ログの確認（`pnpm run build`の詳細出力）
3. 環境情報の確認：
   ```bash
   node --version
   pnpm --version
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
