# Advanced Troubleshooting Guide

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

Phase 2.1〜2.3 の高度機能（CEGIS/Runtime Conformance/Integration Testing）における代表的な問題と対処法をまとめたガイドです。症状→原因→解決の順に、CLI コマンド例と JSON 例を交えて解説します。

詳細なケースは以下の英語・日本語の本文を参照してください。

## English

### Phase 2.1: CEGIS Auto-Fix – No candidates generated
Symptoms
```bash
ae-framework fix apply --input failures.json --dry-run
# Output: No fix candidates generated
```
Causes & Fixes
- Incomplete violation spec → add `counterExample` (input/expected/actual), file/line, and clear message
- Wrong file path → use repo-relative paths; ensure files exist

### Phase 2.2: Conformance – Rules not executed
Symptoms: summary shows `Rules Executed: 0`
Fixes
- Check `rules.json` schema; validate with `jq` and schema if provided
- Ensure `--rules <file>` passed and not overridden; confirm working directory

### Phase 2.3: Integration – E2E flakiness
Fixes
- Run label-gated on PRs; increase retries; stabilize selectors; move flaky suites to nightly until fixed

### Logs & Tips
- Check Playwright trace viewer for failing steps
- Stabilize by using data-testid selectors and explicit waits for network idle
- Record failing tests locally and compare traces with CI

### Schema Validation Failures (Adapters)
Symptoms: aggregator fails to read adapter summaries
```bash
npx ajv -s docs/schemas/artifacts-adapter-summary.schema.json \
  -d artifacts/*/summary.json --strict=false
```
Fixes
- Remove unknown fields or map them under `extras`
- Ensure `status` ∈ {ok|warn|error} and include short `summary`

### Formal Summary Validation (TLA+/Alloy)
```bash
# Validate formal summary if present
npx ajv -s docs/schemas/formal-summary.schema.json -d formal/summary.json --strict=false
```
Fixes
- Ensure required fields (e.g., `result`, `violations`) exist and types match
- Keep messages short; link to logs under `artifacts/codex/*.tlc.log.txt`

### Properties Summary (array vs object)
Symptoms: aggregator expects an object but found an array in `artifacts/properties/summary.json`
Fixes
- When array, validate each element separately (see docs/examples/property-harness.md)
- Convert to per-trace files under `artifacts/properties/<traceId>.summary.json` for simpler aggregation

### Schema Missing Field (example)
Symptoms: `status` missing in adapter summary
```json
{ "adapter": "lighthouse", "summary": "Perf 78, A11y 96, PWA 55" }
```
Fix: add required `status` ∈ {"ok","warn","error"}
```json
{ "adapter": "lighthouse", "status": "warn", "summary": "Perf 78, A11y 96, PWA 55" }
```

### Type Mismatch (example)
Symptoms: `violations` expected array, got object
```json
{ "result": "fail", "violations": { "count": 1 } }
```
Fix: make `violations` an array
```json
{ "result": "fail", "violations": [ { "id": "inv-001", "message": "allocated <= onHand" } ] }
```

### Extra Keys (example)
Symptoms: schema allows only known keys
```json
{ "adapter": "playwright", "status": "ok", "summary": "12/12 passed", "extra": 123 }
```
Fix: move to `extras`
```json
{ "adapter": "playwright", "status": "ok", "summary": "12/12 passed", "extras": { "extra": 123 } }
```

### Reading ajv Errors (quick)
```
error: data/violations must be array at formal/summary.json
```
Tips
- `data/<path>` が示すキーの型/存在を確認（`jq` で該当箇所を抽出）
- スキーマ側で許容されない余剰キーは `extras` に移動

#### jq one-liners
```bash
# 抽出: violations の型と要素数
jq '.violations | type, length' formal/summary.json

# 修正ヒント: 余剰キーの一覧
jq 'paths | select(.[-1] | strings) | join(".")' artifacts/*/summary.json
```

### Short Error Template (aggregator)
```
❌ adapter: invalid data at artifacts/lighthouse/summary.json (key=status, traceId=inv-001)
```

### Playwright Traces (view & compare)
```bash
# show a trace locally
npx playwright show-trace artifacts/integration/traces/test-001.zip

# record traces for failed tests (config)
# playwright.config.ts → use trace: 'on-first-retry' or 'retain-on-failure'
```

### Path/CWD Issues
Symptoms: runner cannot find artifacts or writes to unexpected locations
Fixes
- Use absolute `cwd` without spaces for Windows; prefer WSL
- Pass `--output` or env (`CODEX_ARTIFACTS_DIR`) explicitly to avoid surprises

> Phase 2.1-2.3の高度な機能における問題解決ガイド

## 🔧 Phase 2.1: CEGIS Auto-Fix System

※ 現行CLIでは `cegis` サブコマンドは提供されず、`ae-framework fix ...` に統合されています。入力は failure artifacts JSON を想定します（`fix create-artifact` で生成可）。

### 問題1: 修復候補が生成されない

**症状:**
```bash
ae-framework fix apply --input failures.json --dry-run
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
ae-framework fix apply --input failures.json --dry-run
```

#### 3. 複雑すぎる修復対象
```bash
# 段階的なアプローチ
ae-framework fix apply --input simple-failures.json --dry-run
ae-framework fix analyze --input failures.json
```

### 問題2: 修復の検証に失敗

**症状:**
```bash
ae-framework fix apply --input failures.json --verify
# 出力: Fix verification failed: Tests still failing
```

**解決方法:**

#### 1. テスト環境の確認
```bash
# テストが正常に実行できるか確認
pnpm test
# または
npx vitest run

# テストファイルの存在確認
find . -name "*.test.*" -o -name "*.spec.*"
```

#### 2. 修復スコープの調整
```bash
# より限定的な修復
ae-framework fix apply --input specific-failures.json --verify

# 修復後の手動テスト
ae-framework fix apply --input failures.json
pnpm test
```

#### 3. 修復履歴の確認
```bash
ae-framework fix status
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
node --max-old-space-size=8192 node_modules/.bin/ae-framework fix apply --input failures.json

# 並行処理の制限（現行CLIには専用フラグなし）
# 必要に応じて失敗アーティファクトの分割を検討

# バッチ処理
ae-framework fix apply --input failures1.json
ae-framework fix apply --input failures2.json
```

## 🛡️ Phase 2.2: Runtime Conformance System

### 問題1: 規則実行が遅い

**症状:**
```bash
ae-framework conformance verify --input data.json --rules rules.json
# 出力: Rule execution taking over 30 seconds
```

**解決方法:**

#### 1. サンプリング率の調整
```bash
# サンプリング率を下げる
ae-framework conformance config --set sampling.enabled=true
ae-framework conformance config --set sampling.rate=0.1

# 段階的にサンプリング率を上げる
ae-framework conformance config --set sampling.rate=0.01  # 1%
ae-framework conformance config --set sampling.rate=0.05  # 5%
ae-framework conformance config --set sampling.rate=0.1   # 10%
```

#### 2. 並行実行の最適化
```bash
# 並行数を制限
ae-framework conformance config --set performance.maxConcurrentChecks=3

# タイムアウトの調整
ae-framework conformance config --set performance.timeoutMs=10000
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
ae-framework conformance metrics --format json --export metrics.json
# プロセスのメモリ使用量: 2GB+ and growing
```

**解決方法:**

#### 1. メトリクス収集間隔の調整
```bash
# 収集間隔を長くする
ae-framework conformance metrics --format json --export metrics.json  # 定期実行

# バッチサイズの調整
ae-framework conformance config --set reporting.batchSize=1000
ae-framework conformance config --set reporting.flushIntervalMs=300000
```

#### 2. ガベージコレクションの強制実行
```bash
# ガベージコレクション付きで実行
node --expose-gc node_modules/.bin/ae-framework conformance verify --input data.json --rules rules.json
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
ae-framework conformance verify --input data.json --rules rules.json
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

#### 2. 運用モードの調整
```bash
# 監視のみ（違反を検知するが厳格に失敗させない）
ae-framework conformance config --set mode=monitor_only

# 緩和モード（デフォルト）
ae-framework conformance config --set mode=permissive

# 厳格モード
ae-framework conformance config --set mode=strict
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
ae-framework integration list --type environments
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

# 設定の検証
ae-framework conformance config --show
ae-framework integration list --type environments
ae-framework fix status
```

### ログ収集と診断

```bash
# 詳細ログの収集
ae-framework conformance verify --input data.json --rules rules.json --verbose > debug.log 2>&1

# システム状態の包括的レポート
ae-framework status > system-status.txt

# 診断用データの収集
cat > collect-diagnostics.sh << 'EOF'
#!/bin/bash

DIAG_DIR="ae-framework-diagnostics-$(date +%Y%m%d_%H%M%S)"
mkdir -p $DIAG_DIR

# システム情報
uname -a > $DIAG_DIR/system-info.txt
node --version > $DIAG_DIR/node-version.txt
pnpm list ae-framework > $DIAG_DIR/package-version.txt

# 設定情報
ae-framework conformance config --show > $DIAG_DIR/conformance-config.json
ae-framework integration list --type environments > $DIAG_DIR/integration-environments.txt
ae-framework integration list --type runners > $DIAG_DIR/integration-runners.txt
ae-framework fix status > $DIAG_DIR/fix-status.txt

# ログファイル
cp -r .ae/logs/ $DIAG_DIR/ 2>/dev/null || echo "No logs directory found"

# 最近の実行結果
cp -r ./artifacts/integration/test-results/ $DIAG_DIR/ 2>/dev/null || echo "No test results found"

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
