# AE Framework セットアップガイド

ae-frameworkの全6フェーズエージェントとMCPサーバーのインストール・セットアップ方法について説明します。

## 📋 前提条件

### システム要件
- **Node.js**: 18.0.0 以上
- **npm**: 9.0.0 以上  
- **TypeScript**: 5.5.0 以上
- **Git**: 2.0 以上
- **Playwright**: 1.47.0 以上 (Phase 3.2 E2Eテスト用)

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
npm run build
```

### 5. Git Hooksの設定（オプション）

TDD強制機能を有効にするためのpre-commitフックを設定：

```bash
npm run setup-hooks
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

### 2. MCPサーバー設定

Claude Codeで使用する場合の設定ファイル例：

```json
{
  "mcpServers": {
    "ae-intent": {
      "command": "npx",
      "args": ["tsx", "src/mcp-server/intent-server.ts"],
      "cwd": "/path/to/ae-framework"
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
npm run build
# エラーが出ないことを確認
```

### 2. テストの実行

```bash
# 全テスト実行
npm test

# 高速テスト実行 (CI最適化版)
npm run test:fast

# Phase 3.2 コア機能テスト
npm run test:phase3.2:core

# 全てのテストがパスすることを確認
```

### 3. Lintチェック

```bash
npm run lint
# Lint警告/エラーがないことを確認
```

### 4. 各エージェントの動作確認

#### Intent Agent
```bash
npm run intent-agent
# "Intent Agent MCP server running on stdio" が表示されればOK
```

#### Formal Agent  
```bash
npm run formal-agent
# "Formal Agent MCP server running on stdio" が表示されればOK
```

#### Test Generation Agent
```bash
npm run mcp:test
# "Test Generation MCP server running on stdio" が表示されればOK
```

#### Code Generation Agent
```bash
npm run mcp:code
# "Code Generation MCP server running on stdio" が表示されればOK
```

#### Verify Agent
```bash
npm run verify:server
# "Verify Agent MCP server running on stdio" が表示されればOK
```

#### Operate Agent
```bash
npm run operate:server
# "Operate Agent MCP server running on stdio" が表示されればOK
```

#### TDD Agent
```bash
npm run mcp:tdd
# "TDD MCP server running on stdio" が表示されればOK
```

### 5. Phase 3.2 新機能の動作確認

#### E2Eテスト自動生成デモ
```bash
npm run e2e:demo
# Playwright統合システムの動作確認
```

#### 視覚回帰テストデモ
```bash
npm run visual:demo
# Visual Regression Testing の動作確認
```

#### 依存関係分析デモ
```bash
npm run analyze:demo
# Phase 3.1 Sequential Inference Engine の動作確認
```

## 🛠️ 開発環境のセットアップ

### 1. 開発用監視モード

各エージェントを開発モードで起動（ファイル変更時の自動再起動）：

```bash
# Intent Agent (開発用)
npm run intent-agent:build

# Formal Agent (開発用)  
npm run formal-agent:dev

# Operate Agent (開発用)
npm run operate:dev
```

### 2. カバレッジ測定

```bash
npm run coverage
# カバレッジレポートが生成される
```

### 3. Mutation Testing

```bash
npm run mutation
# Strykerによる変異テストが実行される
```

### 4. CI/CD 最適化設定

Phase 3.2では CI実行時間を 2時間→2分 に最適化：

```bash
# 高速CI（開発用）: 基本テストのみ
# - 自動実行: プッシュ・プルリクエスト時
# - 実行時間: 約2分

# フルCI（包括的）: mutation testing含む  
# - 自動実行: 毎週日曜日、リリースタグ時
# - 手動実行: gh workflow run "Full CI"
# - 実行時間: 約30分（重要コンポーネントのみ）
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
npm install --force
npm run build
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
# タイムアウト設定を確認
npm run test:playwright -- --timeout=60000
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
npm install
npm run build
```

定期的に更新して最新の機能と修正を入手することを推奨します。