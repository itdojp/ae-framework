# Advanced Troubleshooting Guide

> Phase 2.1-2.3の高度な機能における問題解決ガイド

## 🔧 Phase 2.1: CEGIS Auto-Fix System

### 問題1: 修復候補が生成されない

**症状:**
```bash
ae-framework cegis fix --files src/ --violations violations.json
# 出力: No fix candidates generated
```

**原因と解決方法:**

#### 1. 違反定義の不備
```bash
# 問題のある違反定義
{
  "violations": [
    {
      "id": "generic-error",
      "message": "Something is wrong"
    }
  ]
}

# 改善された違反定義
{
  "violations": [
    {
      "id": "email-validation-incomplete",
      "type": "logic_error",
      "severity": "medium",
      "file": "src/validator.ts",
      "line": 15,
      "message": "Email validation logic is incomplete",
      "counterExample": {
        "input": {"email": "invalid@"},
        "expectedBehavior": "should return false",
        "actualBehavior": "returns true"
      },
      "context": {
        "functionName": "validateEmail",
        "className": "UserValidator",
        "relatedCode": ["email.includes('@')"]
      },
      "fixHints": [
        "Add regex validation for email format",
        "Check for domain part after @"
      ]
    }
  ]
}
```

#### 2. ファイルパスの問題
```bash
# 相対パスと絶対パスの確認
pwd
ls -la src/

# デバッグ情報の確認
ae-framework cegis fix --files src/ --violations violations.json --verbose
```

#### 3. 複雑すぎる修復対象
```bash
# 段階的なアプローチ
ae-framework cegis fix --files src/simple-module.ts --violations simple-violations.json
ae-framework cegis generate-candidates --violations violations.json --max-candidates 10 --verbose
```

### 問題2: 修復の検証に失敗

**症状:**
```bash
ae-framework cegis fix --files src/ --verify-fix
# 出力: Fix verification failed: Tests still failing
```

**解決方法:**

#### 1. テスト環境の確認
```bash
# テストが正常に実行できるか確認
npm test
# または
npx vitest run

# テストファイルの存在確認
find . -name "*.test.*" -o -name "*.spec.*"
```

#### 2. 修復スコープの調整
```bash
# より限定的な修復
ae-framework cegis fix --files src/specific-file.ts --violations specific-violations.json --verify-fix

# 修復後の手動テスト
ae-framework cegis fix --files src/ --no-verify
npm test
```

#### 3. 修復履歴の確認
```bash
ae-framework cegis history --limit 5
ae-framework cegis stats --format table
```

### 問題3: メモリ不足エラー

**症状:**
```bash
# JavaScript heap out of memory
FATAL ERROR: Reached heap limit Allocation failed - JavaScript heap out of memory
```

**解決方法:**

```bash
# Node.jsヒープサイズの増加
node --max-old-space-size=8192 node_modules/.bin/ae-framework cegis fix --files src/

# 並行処理の制限
ae-framework cegis fix --files src/ --max-concurrent-fixes 2

# バッチ処理
ae-framework cegis fix --files src/module1/ --violations violations1.json
ae-framework cegis fix --files src/module2/ --violations violations2.json
```

## 🛡️ Phase 2.2: Runtime Conformance System

### 問題1: 規則実行が遅い

**症状:**
```bash
ae-framework conformance verify --rules rules.json
# 出力: Rule execution taking over 30 seconds
```

**解決方法:**

#### 1. サンプリング率の調整
```bash
# サンプリング率を下げる
ae-framework conformance verify --rules rules.json --sample-rate 0.1

# 段階的にサンプリング率を上げる
ae-framework conformance verify --rules rules.json --sample-rate 0.01  # 1%
ae-framework conformance verify --rules rules.json --sample-rate 0.05  # 5%
ae-framework conformance verify --rules rules.json --sample-rate 0.1   # 10%
```

#### 2. 並行実行の最適化
```bash
# 並行数を制限
ae-framework conformance config --set maxConcurrentRules=3

# タイムアウトの調整
ae-framework conformance verify --rules rules.json --timeout 10000
```

#### 3. 規則の最適化
```json
{
  "rules": [
    {
      "id": "optimized-rule",
      "configuration": {
        "caching": true,
        "batchSize": 100,
        "executionTimeout": 5000
      }
    }
  ]
}
```

### 問題2: メトリクス収集でメモリリーク

**症状:**
```bash
# メモリ使用量が継続的に増加
ae-framework conformance metrics --live
# プロセスのメモリ使用量: 2GB+ and growing
```

**解決方法:**

#### 1. メトリクス収集間隔の調整
```bash
# 収集間隔を長くする
ae-framework conformance metrics --live --refresh 300  # 5分間隔

# バッファサイズの制限
ae-framework conformance config --set metricsBufferSize=1000
```

#### 2. ガベージコレクションの強制実行
```bash
# ガベージコレクション付きで実行
node --expose-gc node_modules/.bin/ae-framework conformance verify --rules rules.json

# メモリ使用量の監視
ae-framework conformance metrics --memory-monitoring
```

#### 3. メトリクス設定の最適化
```json
{
  "metricsConfig": {
    "retentionDays": 1,
    "maxBufferSize": 500,
    "compressionEnabled": true,
    "cleanupInterval": 3600
  }
}
```

### 問題3: 違反検出の誤検知

**症状:**
```bash
# 正常な動作が違反として検出される
ae-framework conformance verify --rules rules.json
# 出力: Violation detected: Normal API response flagged as error
```

**解決方法:**

#### 1. 規則の詳細化
```json
{
  "rules": [
    {
      "id": "api-response-rule",
      "configuration": {
        "excludePatterns": ["/health", "/metrics"],
        "allowedStatusCodes": [200, 201, 202, 204],
        "responseTimeThreshold": 5000,
        "contextAware": true
      }
    }
  ]
}
```

#### 2. 学習期間の設定
```bash
# 学習モードで実行
ae-framework conformance verify --rules rules.json --learning-mode --duration 3600

# ベースライン設定
ae-framework conformance config --set-baseline --duration 24h
```

#### 3. 段階的ルール適用
```bash
# 警告レベルから開始
ae-framework conformance verify --rules rules.json --violation-level warning

# 段階的に厳しくする
ae-framework conformance verify --rules rules.json --violation-level error
```

## 🧪 Phase 2.3: Integration Testing System

### 問題1: E2Eテストの不安定性

**症状:**
```bash
ae-framework integration run --tests e2e-tests.json
# 出力: Test failed intermittently: Element not found
```

**解決方法:**

#### 1. 待機戦略の改善
```json
{
  "steps": [
    {
      "id": "wait-for-element",
      "action": "wait:selector:.loading-spinner",
      "timeout": 30000
    },
    {
      "id": "click-button",
      "action": "click:button.submit",
      "timeout": 10000,
      "retry": true
    }
  ]
}
```

#### 2. 実行環境の安定化
```bash
# ヘッドレスモードでの実行
ae-framework integration run --tests e2e-tests.json --headless

# ビューポートサイズの固定
ae-framework integration generate --type test --test-type e2e --viewport 1280x720

# スローモーションの追加（デバッグ用）
ae-framework integration run --tests e2e-tests.json --slow-mo 100
```

#### 3. リトライ戦略の実装
```bash
# リトライ回数の調整
ae-framework integration run --tests e2e-tests.json --retries 3 --timeout 60000

# テストレベルでのリトライ設定
cat > stable-e2e-config.json << 'EOF'
{
  "configuration": {
    "retries": 2,
    "timeout": 45000,
    "waitStrategy": "networkidle",
    "screenshotOnFailure": true
  }
}
EOF
```

### 問題2: APIテストの認証問題

**症状:**
```bash
ae-framework integration run --tests api-tests.json
# 出力: API test failed: 401 Unauthorized
```

**解決方法:**

#### 1. 認証設定の確認
```json
{
  "environment": {
    "name": "test",
    "apiUrl": "http://localhost:3000/api",
    "auth": {
      "type": "bearer",
      "token": "${TEST_API_TOKEN}"
    },
    "headers": {
      "Authorization": "Bearer ${TEST_API_TOKEN}",
      "Content-Type": "application/json"
    }
  }
}
```

#### 2. 環境変数の設定
```bash
# 環境変数の確認
echo $TEST_API_TOKEN

# トークンの生成（開発用）
export TEST_API_TOKEN=$(curl -s -X POST \
  -H "Content-Type: application/json" \
  -d '{"username":"testuser","password":"testpass"}' \
  http://localhost:3000/auth/login | jq -r '.token')

# 環境設定の確認
ae-framework integration list --type environments --detailed
```

#### 3. 認証フローの自動化
```json
{
  "setup": [
    "api:POST:/auth/login:{\"username\":\"testuser\",\"password\":\"testpass\"}"
  ],
  "steps": [
    {
      "id": "login-step",
      "action": "api:request:POST:/auth/login",
      "data": {
        "body": {
          "username": "testuser",
          "password": "testpass"
        }
      }
    },
    {
      "id": "use-token",
      "action": "api:request:GET:/protected-endpoint",
      "data": {
        "headers": {
          "Authorization": "Bearer ${AUTH_TOKEN}"
        }
      }
    }
  ]
}
```

### 問題3: 並列実行でのリソース競合

**症状:**
```bash
ae-framework integration run --tests tests.json --parallel --max-concurrency 4
# 出力: Database connection error: Too many connections
```

**解決方法:**

#### 1. 並行数の調整
```bash
# 並行数を減らす
ae-framework integration run --tests tests.json --parallel --max-concurrency 2

# システムリソースに基づく動的調整
CORES=$(nproc)
MAX_CONCURRENCY=$((CORES / 2))
ae-framework integration run --tests tests.json --parallel --max-concurrency $MAX_CONCURRENCY
```

#### 2. リソース分離の実装
```json
{
  "configuration": {
    "parallel": true,
    "resourceIsolation": {
      "database": "per-test-transaction",
      "filesystem": "temp-directory",
      "network": "port-allocation"
    }
  }
}
```

#### 3. 依存関係の管理
```bash
# テスト間の依存関係を明示
cat > test-dependencies.json << 'EOF'
{
  "suites": [
    {
      "id": "database-setup-suite",
      "runBefore": ["user-tests", "order-tests"]
    },
    {
      "id": "user-tests",
      "dependencies": ["database-setup-suite"]
    }
  ]
}
EOF

ae-framework integration run --suites test-dependencies.json --respect-dependencies
```

## 🚨 緊急時対応

### システム全体の停止

```bash
# すべてのae-frameworkプロセスを停止
pkill -f "ae-framework"

# バックグラウンドジョブの確認
jobs -l

# 特定プロセスの強制終了
ps aux | grep ae-framework
kill -9 <PID>
```

### 設定の初期化

```bash
# 設定ファイルのバックアップ
cp -r .ae/ .ae-backup-$(date +%Y%m%d_%H%M%S)

# デフォルト設定の復元
ae-framework conformance config --reset
ae-framework integration config --reset
ae-framework cegis config --reset

# 設定の検証
ae-framework conformance config --validate
ae-framework integration list --type environments
ae-framework cegis status
```

### ログ収集と診断

```bash
# 詳細ログの収集
DEBUG=ae-framework:* ae-framework conformance verify --rules rules.json > debug.log 2>&1

# システム状態の包括的レポート
ae-framework status --all-phases --detailed --format json > system-status.json

# 診断用データの収集
cat > collect-diagnostics.sh << 'EOF'
#!/bin/bash

DIAG_DIR="ae-framework-diagnostics-$(date +%Y%m%d_%H%M%S)"
mkdir -p $DIAG_DIR

# システム情報
uname -a > $DIAG_DIR/system-info.txt
node --version > $DIAG_DIR/node-version.txt
npm list ae-framework > $DIAG_DIR/package-version.txt

# 設定情報
ae-framework conformance config --show > $DIAG_DIR/conformance-config.json
ae-framework integration list --type all --format json > $DIAG_DIR/integration-resources.json
ae-framework cegis stats --format json > $DIAG_DIR/cegis-stats.json

# ログファイル
cp -r .ae/logs/ $DIAG_DIR/ 2>/dev/null || echo "No logs directory found"

# 最近の実行結果
cp -r ./test-results/ $DIAG_DIR/ 2>/dev/null || echo "No test results found"

echo "Diagnostics collected in: $DIAG_DIR"
tar -czf $DIAG_DIR.tar.gz $DIAG_DIR
echo "Archive created: $DIAG_DIR.tar.gz"
EOF

chmod +x collect-diagnostics.sh
./collect-diagnostics.sh
```

## 📞 サポートリソース

### コミュニティサポート

- **GitHub Issues**: [ae-framework/issues](https://github.com/ae-framework/issues)
- **Discussions**: [ae-framework/discussions](https://github.com/ae-framework/discussions)
- **Stack Overflow**: タグ `ae-framework`

### ドキュメントリンク

- [Phase 2.1: CEGIS Design](../architecture/CEGIS-DESIGN.md)
- [Phase 2.2: Runtime Conformance](../phases/PHASE-2-2-RUNTIME-CONFORMANCE.md)
- [Phase 2.3: Integration Testing](../phases/PHASE-2-3-INTEGRATION-TESTING.md)
- [CLI Commands Reference](../reference/CLI-COMMANDS-REFERENCE.md)

### 問題報告テンプレート

```markdown
# Bug Report

## Environment
- ae-framework version: 
- Node.js version: 
- Operating System: 
- Phase: 

## Problem Description
<!-- Describe the issue clearly -->

## Steps to Reproduce
1. 
2. 
3. 

## Expected Behavior
<!-- What should happen -->

## Actual Behavior
<!-- What actually happens -->

## Logs
```
<!-- Paste relevant logs here -->
```

## Configuration
<!-- Include relevant configuration files -->

## Additional Context
<!-- Any other relevant information -->
```

---

**Advanced Troubleshooting Guide** - 問題解決による開発効率の最適化 🔧