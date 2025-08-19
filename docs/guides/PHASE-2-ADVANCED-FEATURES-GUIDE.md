# Phase 2 Advanced Features Guide

> Phase 2.1-2.3の新機能を活用した実践的な開発ワークフロー

## 概要

Phase 2では、従来の自然言語要件処理に加えて、3つの高度なシステムが追加されました：

- **Phase 2.1**: CEGIS自動修復システム - 反例誘導帰納合成による自動コード修復
- **Phase 2.2**: Runtime Conformance System - リアルタイム適合性検証
- **Phase 2.3**: Integration Testing System - 包括的統合テストオーケストレーション

これらのシステムは相互に連携し、開発プロセス全体の品質と効率性を大幅に向上させます。

## 🚀 クイックスタート（15分で体験）

### ステップ1: プロジェクト初期化

```bash
# プロジェクトディレクトリの作成
mkdir my-ae-project
cd my-ae-project

# ae-frameworkの初期化
ae-framework init . --with-advanced-features

# 基本構造の確認
tree .
```

### ステップ2: Phase 2.2 Runtime Conformance の設定

```bash
# サンプル規則の生成
ae-framework conformance sample --rules --output rules.json

# サンプル設定の生成
ae-framework conformance config --create-sample --output conformance-config.json

# 生成されたファイルの確認
cat rules.json | jq '.rules[0]'
```

### ステップ3: Phase 2.3 Integration Testing の設定

```bash
# テスト環境の生成
ae-framework integration generate --type environment --name test --output test-env.json

# E2Eテストサンプルの生成
ae-framework integration generate --type test --test-type e2e --name "Sample Login Test" --output login-test.json

# APIテストサンプルの生成
ae-framework integration generate --type test --test-type api --name "Users API Test" --output users-api-test.json

# テストスイートの生成
ae-framework integration generate --type suite --name "Authentication Suite" --output auth-suite.json
```

### ステップ4: Phase 2.1 CEGIS の体験

```bash
# サンプルコードの作成（意図的にバグを含む）
mkdir -p src
cat > src/user-validator.ts << 'EOF'
export interface User {
  id: string;
  name: string;
  email: string;
  age?: number;
}

export class UserValidator {
  validateUser(user: User): boolean {
    // Bug: emailの検証が不完全
    if (!user.name || user.name.length < 2) {
      return false;
    }
    
    if (!user.email || !user.email.includes('@')) {
      return false;
    }
    
    // Bug: ageの範囲チェックが不十分
    if (user.age && user.age < 0) {
      return false;
    }
    
    return true;
  }
}
EOF

# 違反定義の作成
cat > violations.json << 'EOF'
{
  "violations": [
    {
      "id": "email-validation-incomplete",
      "type": "logic_error",
      "severity": "medium",
      "file": "src/user-validator.ts",
      "line": 12,
      "message": "Email validation is incomplete - should check for valid email format",
      "counterExample": {
        "input": {"email": "@invalid"},
        "expectedBehavior": "should return false",
        "actualBehavior": "returns true"
      }
    },
    {
      "id": "age-validation-incomplete", 
      "type": "logic_error",
      "severity": "low",
      "file": "src/user-validator.ts",
      "line": 18,
      "message": "Age validation should include upper bound check",
      "counterExample": {
        "input": {"age": 200},
        "expectedBehavior": "should return false",
        "actualBehavior": "returns true"
      }
    }
  ]
}
EOF

# CEGIS修復の実行
ae-framework cegis fix --files src/ --violations violations.json

# 修復結果の確認
cat src/user-validator.ts
```

### ステップ5: 統合ワークフローの実行

```bash
# 1. Runtime Conformance による検証
ae-framework conformance verify --rules rules.json --collect-metrics

# 2. Integration Testing の実行
ae-framework integration run --tests login-test.json,users-api-test.json --environment test

# 3. 結果の確認
ae-framework conformance status
ae-framework integration status

# 4. 総合レポートの生成
ae-framework conformance metrics --format html --output conformance-report.html
ae-framework integration reports --list
```

## 🏗️ 実践的なワークフロー

### 開発サイクルでの統合

#### 1. 開発開始時

```bash
# プロジェクト状態の確認
ae-framework status --all-phases

# 適合性規則の設定
ae-framework conformance config --validate

# テスト環境の準備
ae-framework integration list --type environments
```

#### 2. コーディング中

```bash
# リアルタイム適合性監視（別ターミナルで実行）
ae-framework conformance verify --rules rules.json --live

# ファイル変更の監視とCEGIS修復
ae-framework cegis fix --files src/ --watch --auto-apply
```

#### 3. テスト実行前

```bash
# CEGIS による事前修復
ae-framework cegis analyze --violations violations.json
ae-framework cegis fix --files src/ --verify-fix

# 統合テストの発見と準備
ae-framework integration discover --patterns "./tests/**/*.json" --type all
```

#### 4. テスト実行

```bash
# 並列テスト実行
ae-framework integration run \
  --suites auth-suite.json,api-suite.json \
  --environment test \
  --parallel \
  --max-concurrency 4 \
  --report-format html,json
```

#### 5. 結果分析

```bash
# 包括的な状態確認
ae-framework conformance metrics --detailed
ae-framework integration status --detailed
ae-framework cegis stats --format table

# 問題の特定と修復
ae-framework cegis history --limit 5
ae-framework conformance status --live
```

### CI/CDパイプライン統合

#### GitHub Actions 設定例

```yaml
# .github/workflows/ae-framework-advanced.yml
name: AE Framework Advanced Pipeline

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  phase2-advanced-validation:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Setup Node.js
      uses: actions/setup-node@v3
      with:
        node-version: '18'
        
    - name: Install dependencies
      run: npm ci
      
    - name: Phase 2.1 - CEGIS Auto-Fix
      run: |
        ae-framework cegis analyze --violations .ae/violations.json
        ae-framework cegis fix --files src/ --verify-fix --timeout 300000
        
    - name: Phase 2.2 - Runtime Conformance
      run: |
        ae-framework conformance verify \
          --rules .ae/conformance-rules.json \
          --collect-metrics \
          --timeout 180000 \
          --output-dir ./conformance-results
          
    - name: Phase 2.3 - Integration Testing
      run: |
        # テスト環境の起動
        npm run start:test-env &
        TEST_PID=$!
        
        # テストの実行
        ae-framework integration run \
          --suites ./tests/integration/suites/*.json \
          --environment ci \
          --parallel \
          --max-concurrency 4 \
          --timeout 600000 \
          --output-dir ./integration-results \
          --report-format json,html
          
        # クリーンアップ
        kill $TEST_PID
        
    - name: Upload Results
      uses: actions/upload-artifact@v3
      if: always()
      with:
        name: phase2-advanced-results
        path: |
          ./conformance-results/
          ./integration-results/
          
    - name: Quality Gate Check
      run: |
        # 最低品質基準のチェック
        conformance_success=$(jq -r '.success' ./conformance-results/metrics.json)
        integration_pass_rate=$(jq -r '.statistics.passRate' ./integration-results/summary.json)
        
        if [[ "$conformance_success" != "true" ]]; then
          echo "❌ Conformance verification failed"
          exit 1
        fi
        
        if (( $(echo "$integration_pass_rate < 90" | bc -l) )); then
          echo "❌ Integration test pass rate below 90%: $integration_pass_rate%"
          exit 1
        fi
        
        echo "✅ All Phase 2 advanced quality gates passed"
```

## 📊 監視とメトリクス

### ダッシュボードの構築

リアルタイム監視用のダッシュボードを構築できます：

```bash
# メトリクス収集の開始
ae-framework conformance metrics --live --refresh 30 --output metrics.json &
ae-framework integration status --watch --refresh 60 --json > integration-status.json &

# ダッシュボード用データの準備
cat > dashboard-data.js << 'EOF'
// リアルタイムメトリクスの取得
const conformanceMetrics = require('./metrics.json');
const integrationStatus = require('./integration-status.json');

// グラフ用データの生成
const generateDashboardData = () => {
  return {
    conformance: {
      successRate: conformanceMetrics.execution?.successRate || 0,
      violations: conformanceMetrics.violations?.total || 0,
      responseTime: conformanceMetrics.performance?.averageResponseTime || 0
    },
    integration: {
      passRate: integrationStatus.statistics?.passRate || 0,
      totalTests: integrationStatus.statistics?.total || 0,
      executionTime: integrationStatus.lastExecution?.duration || 0
    },
    cegis: {
      fixesApplied: 0, // CEGISメトリクスを追加
      violationsResolved: 0
    }
  };
};

console.log(JSON.stringify(generateDashboardData(), null, 2));
EOF

node dashboard-data.js
```

### アラート設定

```bash
# 品質閾値の設定
cat > quality-thresholds.yaml << 'EOF'
conformance:
  successRate:
    warning: 95
    critical: 90
  responseTime:
    warning: 1000
    critical: 2000
  violations:
    warning: 5
    critical: 10

integration:
  passRate:
    warning: 95
    critical: 90
  executionTime:
    warning: 600000  # 10分
    critical: 900000 # 15分

cegis:
  unfixableViolations:
    warning: 3
    critical: 5
EOF

# アラート監視スクリプト
cat > monitor-quality.sh << 'EOF'
#!/bin/bash

check_thresholds() {
  local metrics_file=$1
  local thresholds_file=$2
  
  # メトリクスの取得
  local success_rate=$(jq -r '.execution.successRate' $metrics_file)
  local violations=$(jq -r '.violations.total' $metrics_file)
  
  # 閾値チェック
  if (( $(echo "$success_rate < 90" | bc -l) )); then
    echo "🚨 CRITICAL: Conformance success rate below 90%: $success_rate%"
    # Slack通知やメール送信
    # curl -X POST -H 'Content-type: application/json' --data '{"text":"Critical: Conformance failure"}' $SLACK_WEBHOOK
  elif (( $(echo "$success_rate < 95" | bc -l) )); then
    echo "⚠️  WARNING: Conformance success rate below 95%: $success_rate%"
  fi
  
  if (( violations > 10 )); then
    echo "🚨 CRITICAL: Too many violations detected: $violations"
  elif (( violations > 5 )); then
    echo "⚠️  WARNING: Multiple violations detected: $violations"
  fi
}

# 定期チェックの実行
while true; do
  ae-framework conformance metrics --format json --output current-metrics.json
  check_thresholds current-metrics.json quality-thresholds.yaml
  sleep 300  # 5分間隔でチェック
done
EOF

chmod +x monitor-quality.sh
```

## 🛠️ トラブルシューティング

### よくある問題と解決方法

#### 1. CEGIS修復の失敗

```bash
# 問題: 修復候補が生成されない
ae-framework cegis generate-candidates --violations violations.json --max-candidates 10 --verbose

# 解決: 違反定義の詳細化
cat > detailed-violations.json << 'EOF'
{
  "violations": [
    {
      "id": "validation-issue",
      "type": "logic_error",
      "severity": "medium",
      "file": "src/validator.ts",
      "line": 15,
      "message": "Validation logic incomplete",
      "counterExample": {
        "input": {"value": "invalid@"},
        "expectedBehavior": "return false",
        "actualBehavior": "return true"
      },
      "context": {
        "functionName": "validateEmail",
        "className": "UserValidator",
        "relatedCode": ["email.includes('@')", "email.length > 5"]
      },
      "fixHints": [
        "Add proper email regex validation",
        "Check for domain part after @",
        "Validate email format completely"
      ]
    }
  ]
}
EOF

ae-framework cegis fix --violations detailed-violations.json --files src/
```

#### 2. Runtime Conformance パフォーマンス問題

```bash
# 問題: 検証が遅い
ae-framework conformance metrics --detailed

# 解決: サンプリング率の調整
ae-framework conformance verify --rules rules.json --sample-rate 0.1

# 並行実行数の調整
ae-framework conformance config --set maxConcurrentRules=5
```

#### 3. Integration Testing の不安定性

```bash
# 問題: テストが断続的に失敗
ae-framework integration status --detailed

# 解決: タイムアウトの調整
ae-framework integration run --tests tests.json --timeout 60000 --retries 3

# テスト環境の確認
ae-framework integration list --type environments --detailed
```

## 🎯 ベストプラクティス

### 1. 段階的導入

```bash
# Step 1: Runtime Conformance から開始
ae-framework conformance sample --rules --output basic-rules.json
ae-framework conformance verify --rules basic-rules.json --sample-rate 0.05

# Step 2: Integration Testing の追加
ae-framework integration generate --type test --test-type api --output basic-api-test.json
ae-framework integration run --tests basic-api-test.json --environment dev

# Step 3: CEGIS の統合
ae-framework cegis analyze --violations simple-violations.json
ae-framework cegis fix --files src/ --violations simple-violations.json --verify-fix
```

### 2. チーム連携

```bash
# 共有設定の管理
mkdir -p .ae/shared
ae-framework conformance config --export .ae/shared/conformance-config.json
ae-framework integration generate --type environment --name shared --output .ae/shared/test-environment.json

# チーム用スクリプトの作成
cat > scripts/team-validation.sh << 'EOF'
#!/bin/bash
echo "🚀 Running team validation workflow..."

# 1. 適合性検証
ae-framework conformance verify --rules .ae/shared/conformance-rules.json

# 2. 統合テスト（基本セット）
ae-framework integration run --suites .ae/shared/basic-test-suite.json --environment shared

# 3. 修復が必要な問題の確認
ae-framework cegis analyze --violations .ae/shared/common-violations.json

echo "✅ Team validation complete"
EOF

chmod +x scripts/team-validation.sh
```

### 3. 継続的改善

```bash
# メトリクス分析スクリプト
cat > scripts/analyze-trends.sh << 'EOF'
#!/bin/bash

# 過去30日のメトリクス分析
ae-framework conformance metrics --historical --days 30 --format json > conformance-trends.json
ae-framework integration reports --list --last-30-days --format json > integration-trends.json
ae-framework cegis stats --historical --days 30 --format json > cegis-trends.json

# トレンド分析レポートの生成
node scripts/generate-trend-report.js conformance-trends.json integration-trends.json cegis-trends.json
EOF

# トレンド分析ツール
cat > scripts/generate-trend-report.js << 'EOF'
const fs = require('fs');

const [conformanceFile, integrationFile, cegisFile] = process.argv.slice(2);

const conformanceData = JSON.parse(fs.readFileSync(conformanceFile, 'utf8'));
const integrationData = JSON.parse(fs.readFileSync(integrationFile, 'utf8'));
const cegisData = JSON.parse(fs.readFileSync(cegisFile, 'utf8'));

console.log('# Phase 2 Advanced Features - 30-Day Trend Report\n');

console.log('## Runtime Conformance Trends');
console.log(`- Average Success Rate: ${conformanceData.averageSuccessRate}%`);
console.log(`- Violation Trend: ${conformanceData.violationTrend}`);
console.log(`- Performance Trend: ${conformanceData.performanceTrend}\n`);

console.log('## Integration Testing Trends');
console.log(`- Average Pass Rate: ${integrationData.averagePassRate}%`);
console.log(`- Execution Time Trend: ${integrationData.executionTimeTrend}`);
console.log(`- Stability Trend: ${integrationData.stabilityTrend}\n`);

console.log('## CEGIS Auto-Fix Trends');
console.log(`- Fix Success Rate: ${cegisData.fixSuccessRate}%`);
console.log(`- Average Fixes Per Day: ${cegisData.averageFixesPerDay}`);
console.log(`- Complexity Trend: ${cegisData.complexityTrend}\n`);

// 改善提案の生成
console.log('## Recommendations');
if (conformanceData.averageSuccessRate < 95) {
  console.log('- 🎯 Focus on improving conformance rules and system stability');
}
if (integrationData.averagePassRate < 90) {
  console.log('- 🧪 Review integration test stability and environment setup');
}
if (cegisData.fixSuccessRate < 80) {
  console.log('- 🔧 Enhance violation definitions and fix candidate generation');
}
EOF

chmod +x scripts/analyze-trends.sh
```

## 🚀 次のステップ

Phase 2の高度な機能をマスターしたら、以下のステップに進むことができます：

### 1. カスタマイズの深化

```bash
# カスタム規則の作成
ae-framework conformance generate-rule-template --output custom-rule-template.json

# カスタムテストランナーの作成
ae-framework integration generate-runner-template --type custom --output custom-runner-template.ts

# カスタム修復戦略の実装
ae-framework cegis generate-strategy-template --output custom-strategy-template.ts
```

### 2. エンタープライズ統合

- **監視システム**: Prometheus、Grafana との統合
- **アラートシステム**: PagerDuty、Slack 通知
- **ログ集約**: ELK Stack、Fluentd との連携
- **セキュリティ**: SIEM システムとの統合

### 3. 他のフェーズとの連携

- **Phase 3**: User Stories との要件トレーサビリティ
- **Phase 4**: Validation システムとの品質ゲート統合
- **Phase 5**: Domain Modeling からのテストケース生成
- **Phase 6**: UI/UX との E2E テスト自動化

## 📚 関連ドキュメント

- [Phase 2.1: CEGIS Design Document](../architecture/CEGIS-DESIGN.md)
- [Phase 2.2: Runtime Conformance System](../phases/PHASE-2-2-RUNTIME-CONFORMANCE.md)
- [Phase 2.3: Integration Testing System](../phases/PHASE-2-3-INTEGRATION-TESTING.md)
- [CLI Commands Reference](../reference/CLI-COMMANDS-REFERENCE.md)
- [TDD Framework Architecture](../architecture/TDD-FRAMEWORK-ARCHITECTURE.md)

---

**Phase 2 Advanced Features** - 次世代開発ワークフローの実現 🚀