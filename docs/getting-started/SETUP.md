# AE Framework セットアップガイド

ae-frameworkの全6フェーズエージェントとMCPサーバーのインストール・セットアップ方法について説明します。

## 📋 前提条件

### システム要件
- **Node.js**: 18.0.0 以上
- **pnpm**: 8.0.0 以上 (推奨パッケージマネージャー)
- **TypeScript**: 5.5.0 以上
- **Git**: 2.0 以上
- **Playwright**: 1.47.0 以上 (E2Eテスト用)

### 推奨環境
- **OS**: Linux, macOS, Windows (WSL2推奨)
- **メモリ**: 4GB以上
- **ストレージ**: 1GB以上の空き容量

## 🚀 インストール

### 1. リポジトリのクローン

```bash
git clone https://github.com/itdojp/ae-framework.git
cd ae-framework
```

### 2. 依存関係のインストール

**pnpm使用（推奨）:**
```bash
pnpm install
```

**npmでも可能:**
```bash
npm install
```

### 3. Phase 3.2 Playwright設定

E2Eテストと視覚回帰テスト用のPlaywrightブラウザをインストール：

```bash
npx playwright install
```

### 4. TypeScriptのビルド

```bash
pnpm run build
```

### 5. Git Hooksの設定（オプション）

TDD強制機能を有効にするためのpre-commitフックを設定：

```bash
pnpm run setup-hooks
```

## 🔧 設定

### 1. 環境変数の設定

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

### 2. Claude Code 統合設定

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
    },
    "ae-code": {
      "command": "npx",
      "args": ["tsx", "src/mcp-server/code-generation-server.ts"],
      "cwd": "/path/to/ae-framework"
    },
    "ae-verify": {
      "command": "npx",
      "args": ["tsx", "src/mcp-server/verify-server.ts"],
      "cwd": "/path/to/ae-framework"
    },
    "ae-operate": {
      "command": "npx",
      "args": ["tsx", "src/mcp-server/operate-server.ts"],
      "cwd": "/path/to/ae-framework"
    },
    "ae-tdd": {
      "command": "npx",
      "args": ["tsx", "src/mcp-server/tdd-server.ts"],
      "cwd": "/path/to/ae-framework"
    }
  }
}
```

## ✅ インストール確認

### 1. ビルドの確認

```bash
pnpm run build
# エラーが出ないことを確認
```

### 2. テストの実行

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

### 3. Lintチェック

```bash
pnpm run lint
# Lint警告/エラーがないことを確認
```

### 4. 各エージェントの動作確認

#### Intent Agent
```bash
pnpm run intent-agent
# "Intent Agent MCP server running on stdio" が表示されればOK
```

#### Formal Agent  
```bash
pnpm run formal-agent
# "Formal Agent MCP server running on stdio" が表示されればOK
```

#### Test Generation Agent
```bash
pnpm run mcp:test
# "Test Generation MCP server running on stdio" が表示されればOK
```

#### Code Generation Agent
```bash
pnpm run mcp:code
# "Code Generation MCP server running on stdio" が表示されればOK
```

#### Verify Agent
```bash
pnpm run verify:server
# "Verify Agent MCP server running on stdio" が表示されればOK
```

#### Operate Agent
```bash
pnpm run operate:server
# "Operate Agent MCP server running on stdio" が表示されればOK
```

#### TDD Agent
```bash
pnpm run mcp:tdd
# "TDD MCP server running on stdio" が表示されればOK
```

### 5. Issue #127 最新CI/CDシステムの動作確認 ✨ **NEW**

#### Fast CI Pipeline確認
```bash
# 高速CI (5分以内)
pnpm run test:unit
pnpm run lint
```

#### Quality Gates確認
```bash
# 品質ゲート (15分以内)
pnpm run test:int
pnpm run test:a11y
pnpm run test:coverage
```

#### フレーク検知・隔離システム
```bash
# フレーク検知
pnpm run flake:detect

# フレーク隔離管理
pnpm run flake:list
pnpm run flake:report
```

#### パフォーマンス予算システム
```bash
# パフォーマンス予算チェック
pnpm run perf:budgets
pnpm run test:budgets
```

### 6. リソースリーク検知システム ✨ **NEW**

```bash
# リソースリーク検知付きテスト実行
pnpm run test:int
# ハンドルリーク警告が表示され、自動クリーンアップされることを確認
```

### 7. 品質スコアカードシステム

```bash
# プロジェクト全体の品質分析
pnpm run quality:scorecard
pnpm run package:quality

# セキュリティ分析
pnpm run security:full

# アクセシビリティ分析
pnpm run accessibility:full
```

## 🛠️ 開発環境のセットアップ

### 1. 開発用監視モード

各エージェントを開発モードで起動（ファイル変更時の自動再起動）：

```bash
# Intent Agent (開発用)
pnpm run intent-agent:build

# Formal Agent (開発用)  
pnpm run formal-agent:dev

# Operate Agent (開発用)
pnpm run operate:dev
```

### 2. カバレッジ測定

```bash
pnpm run coverage
# カバレッジレポートが生成される
```

### 3. Mutation Testing

```bash
pnpm run mutation
# Strykerによる変異テストが実行される
```

### 4. CI/CD 最適化設定 ✨ **Issue #127実装済み**

CI実行時間を大幅最適化：

```bash
# Fast CI (5分以内): 基本テスト + lint
# - 自動実行: プッシュ・プルリクエスト時
# - 実行時間: ~5分

# Quality Gates (15分以内): 統合テスト + 品質チェック
# - 自動実行: プルリクエスト時
# - 実行時間: ~15分

# Nightly Matrix (30分以内): クロスプラットフォーム + 性能テスト
# - 自動実行: 毎日18:00 JST
# - 実行時間: ~30分
```

## 🔍 トラブルシューティング

### よくある問題と解決方法

#### 1. Node.js バージョンエラー
```bash
Error: Node.js version 16.x is not supported
```
**解決方法**: Node.js 18以上にアップデート

#### 2. TypeScriptコンパイルエラー
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

#### 3. MCPサーバー接続エラー
```bash
MCP server connection failed
```
**解決方法**: 
- パスの確認（絶対パスを使用）
- 権限の確認（実行権限があるか）
- Node.jsのバージョン確認

#### 4. 依存関係エラー
```bash
Module not found: @modelcontextprotocol/sdk
```
**解決方法**: 
```bash
pnpm install --force
pnpm run build
```

#### 5. Playwright ブラウザエラー
```bash
Error: Browser not found. Please run 'npx playwright install'
```
**解決方法**: 
```bash
npx playwright install
```

#### 6. E2Eテスト実行エラー
```bash
Error: Test timeout exceeded
```
**解決方法**: 
```bash
# タイムアウト設定を確認 (Vitest Projects設定で自動調整済み)
pnpm run test:int  # 60秒タイムアウト
pnpm run test:perf # 180秒タイムアウト
```

#### 7. 視覚回帰テストエラー
```bash
Error: Baseline screenshots not found
```
**解決方法**: 
```bash
# ベースライン画像を生成
npm run visual:baseline
```

#### 8. フレーク検知システムエラー ✨ **NEW**
```bash
Error: Flake isolation manager not found
```
**解決方法**:
```bash
# フレーク検知システム確認
pnpm run flake:detect:quick
pnpm run flake:list

# フレーク隔離設定確認
ls -la config/flaky-tests.json
ls -la config/test-patterns.json
```

#### 9. パフォーマンス予算エラー ✨ **NEW**
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

#### 10. Vitest Projects設定エラー ✨ **NEW**
```bash
Error: Project 'unit' not found
```
**解決方法**:
```bash
# Vitest設定確認
cat vitest.config.ts

# プロジェクト別実行確認
pnpm run test:unit
pnpm run test:int
pnpm run test:perf
```

## 📚 次のステップ

インストールが完了したら、[使い方ガイド](./USAGE.md)を参照して各エージェントの使用方法を確認してください。

## 🆘 サポート

問題が解決しない場合は、以下の方法でサポートを受けられます：

1. [GitHub Issues](https://github.com/itdojp/ae-framework/issues) での報告
2. ログの確認（`npm run build`の詳細出力）
3. 環境情報の確認：
   ```bash
   node --version
   npm --version
   npx tsc --version
   ```

## 📝 アップデート

最新版への更新：

```bash
git pull origin main
pnpm install
pnpm run build
```

定期的に更新して最新の機能と修正を入手することを推奨します。