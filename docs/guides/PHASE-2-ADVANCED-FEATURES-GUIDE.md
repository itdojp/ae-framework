---
docRole: derived
canonicalSource:
- docs/architecture/CURRENT-SYSTEM-OVERVIEW.md
- README.md
lastVerified: '2026-03-10'
---
# Phase 2 Advanced Features Guide

> 🌍 Language / 言語: 日本語 | English

---

## English (Overview)

Practical workflows leveraging Phase 2.1–2.3: CEGIS Auto‑Fix (counterexample‑guided repair), Runtime Conformance (real‑time conformance verification), and Integration Testing (E2E orchestration). Quick start, commands, and how the systems interoperate.

## English

### Quick Start (15 minutes)
```bash
# Conformance samples
ae-framework conformance sample --rules rules.json
ae-framework conformance sample --config conformance-config.json

# Integration testing samples
ae-framework integration generate --type environment --name test --output test-env.json
ae-framework integration generate --type test --test-type e2e --name "Sample Login Test" --output login-test.json
ae-framework integration generate --type test --test-type api --name "Users API Test" --output users-api-test.json

# CEGIS demo (failure artifacts) then fix
ae-framework fix create-artifact --type error --message "Sample failure" --file src/app.ts --line 10 --output failure.json
ae-framework fix apply --input failure.json --output .ae/auto-fix --dry-run
```

### Interoperability
- 2.2 (Conformance) produces metrics/violations → can feed 2.1 (CEGIS) to synthesize repair candidates
- 2.3 (Integration) provides E2E/API feedback → informs conformance rules and repair priorities

### Reports & Artifacts
- Conformance: `artifacts/conformance/conformance-results.json` / `reports/conformance/**` (集計)
- Integration: `artifacts/integration/test-results/**`（`--output-dir` で変更）
- CEGIS: `.ae/auto-fix/**`（適用結果/レポート）

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

# ae-frameworkの導入
pnpm add ae-framework

# CLI確認
npx ae-framework --help
```

### ステップ2: Phase 2.2 Runtime Conformance の設定

```bash
# サンプル規則の生成
ae-framework conformance sample --rules rules.json

# サンプル設定の生成
ae-framework conformance sample --config conformance-config.json

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

# 失敗アーティファクトの作成
ae-framework fix create-artifact \
  --type error \
  --message "Email validation is incomplete" \
  --file src/user-validator.ts \
  --line 12 \
  --output failure.json

# CEGIS修復の実行（dry-run）
ae-framework fix apply --input failure.json --output .ae/auto-fix --dry-run

# 修復結果の確認
cat src/user-validator.ts
```

### ステップ5: 統合ワークフローの実行

```bash
# 1. Runtime Conformance による検証
ae-framework conformance verify --input data.json --rules rules.json

# 2. Integration Testing の実行
ae-framework integration run --tests login-test.json,users-api-test.json --environment test

# 3. 結果の確認
ae-framework conformance status
ae-framework integration status

# 4. 総合レポートの生成
ae-framework conformance metrics --format json --export conformance-metrics.json
ae-framework integration reports --list
```

## English (Selected Outputs)

### 2.2 Conformance – Sample metrics JSON
```json
{
  "counts": {
    "totalVerifications": 25,
    "totalViolations": 3,
    "uniqueRules": 25,
    "uniqueViolations": 2
  },
  "performance": {
    "averageExecutionTime": 12.4,
    "p95ExecutionTime": 18.7,
    "p99ExecutionTime": 22.0,
    "timeouts": 0,
    "errors": 0
  }
}
```

### 2.3 Integration – E2E run summary (text)
```
Suite completed: 14 total, 13 passed (92.8%)
Report: test-results/test-report-<id>.html
```

### 2.1 CEGIS – Fix stats (text)
```
Violations Found: 8 / Fix Candidates: 12 / Applied: 7 / Verified: 6
files_scanned=12, files_modified=2, candidates=3, accepted=2
time=3.2s, confidence=0.78
```

### 2.2 Conformance – Violation sample (JSON)
```json
{
  "ruleId": "api_rate_limit",
  "severity": "major",
  "resource": "/api/users",
  "evidence": { "requestsPerMinute": 180, "limit": 120 }
}
```

### 2.3 Integration – Attachments
- Reports: `artifacts/integration/test-results/test-report-*.html`
- Screenshots: `artifacts/integration/test-results/screenshots/*.png`（`--screenshots` 有効時）
- Traces: `artifacts/integration/test-results/traces/*`（`--trace` 有効時）
- Videos: `artifacts/integration/test-results/videos/*`（`--video` 有効時）
※ 現行実装ではスクリーンショット/トレース/動画は `artifacts/integration/test-results` に保存されます。

### 2.1 CEGIS – Diff example (pseudo)
```diff
- if (!user.email || !user.email.includes('@')) {
+ if (!user.email || !/^\S+@\S+\.\S+$/.test(user.email)) {
    return false;
  }
  
- if (user.age && user.age < 0) {
+ if (user.age != null && (user.age < 0 || user.age > 130)) {
    return false;
  }
```

## 日本語（サンプル出力）

### 2.2 Conformance – メトリクスJSON（例）
```json
{
  "counts": {
    "totalVerifications": 25,
    "totalViolations": 3,
    "uniqueRules": 25,
    "uniqueViolations": 2
  },
  "performance": {
    "averageExecutionTime": 12.4,
    "p95ExecutionTime": 18.7,
    "p99ExecutionTime": 22.0,
    "timeouts": 0,
    "errors": 0
  }
}
```

### 2.3 Integration – 実行サマリ（テキスト例）
```
Suite completed: 14 total, 13 passed (92.8%)
Report: test-results/test-report-<id>.html
```

### 2.1 CEGIS – 修復サマリ（テキスト）
```
Violations Found: 8 / Fix Candidates: 12 / Applied: 7 / Verified: 6
files_scanned=12, files_modified=2, candidates=3, accepted=2
time=3.2s, confidence=0.78
```

### 2.2 Conformance – Gate excerpt (text)
```
🔧 Rules Executed: 25
✅ Rules Passed: 22
❌ Rules Failed: 3
⏭️  Rules Skipped: 0
🚨 Rules Error: 0
```

### 2.3 Integration – Summary (text)
```
Overall Summary:
Total Tests: 14
Passed: 13
Pass Rate: 92.8%
Report: test-results/test-report-<id>.html
```

### 2.3 Integration – Attachments (paths)
```
Reports:     test-results/test-report-*.html
Screenshots: test-results/screenshots/*.png
Traces:      test-results/traces/*
Videos:      test-results/videos/*
```

### 2.3 Integration – Discovered tests (path)
```
例: test-results/discovered.json（--output で指定したパスに出力）
```

### 2.1 CEGIS – Candidates (JSON excerpt)
```json
[
  { "id": "email-validation-incomplete", "file": "src/user-validator.ts", "fix": "use regex for email" },
  { "id": "age-validation-incomplete",   "file": "src/user-validator.ts", "fix": "add upper bound check" }
]
```

### 2.2 Conformance – Violation (JSON)
```json
{ "ruleId": "schema_validation", "severity": "minor", "resource": "/api/items", "evidence": { "missing": ["name"] } }
```

### 2.2 Conformance – Metrics path
```
reports/conformance/conformance-summary.json
```

### 2.1 CEGIS – Applied fix (text)
```
Applied: email-validation-incomplete (src/user-validator.ts:12)
Applied: age-validation-incomplete   (src/user-validator.ts:18)
Verified: 2/2
```

## 🏗️ 実践的なワークフロー

### 開発サイクルでの統合

#### 1. 開発開始時

```bash
# プロジェクト状態の確認
ae-framework status

# 適合性規則の設定
ae-framework conformance config --show

# テスト環境の準備
ae-framework integration list --type environments
```

#### 2. コーディング中

```bash
# 適合性検証（別ターミナルで定期実行）
ae-framework conformance verify --input data.json --rules rules.json

# CEGIS修復（failure artifactベース）
ae-framework fix apply --input failures.json --apply
```

#### 3. テスト実行前

```bash
# CEGIS による事前修復
ae-framework fix analyze --input failures.json
ae-framework fix apply --input failures.json --verify

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
  --report-format html
```

#### 5. 結果分析

```bash
# 包括的な状態確認
ae-framework conformance metrics --format json
ae-framework integration status
ae-framework fix status

# 問題の特定と修復
ae-framework conformance status --monitors
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
      run: pnpm install --frozen-lockfile
      
    - name: Phase 2.1 - CEGIS Auto-Fix
      run: |
        ae-framework fix analyze --input .ae/failures.json
        ae-framework fix apply --input .ae/failures.json --output .ae/auto-fix --verify --verify-profile lite
        
    - name: Phase 2.2 - Runtime Conformance
      run: |
        mkdir -p ./artifacts/conformance
        ae-framework conformance verify \
          --input .ae/conformance-data.json \
          --context-file .ae/conformance-context.json \
          --rules .ae/conformance-rules.json \
          --output ./artifacts/conformance/conformance-results.json
          
    - name: Phase 2.3 - Integration Testing
      run: |
        # テスト環境の起動
        pnpm run start:server &
        TEST_PID=$!
        
        # テストの実行
        ae-framework integration run \
          --suites ./tests/integration/suites/*.json \
          --environment ci \
          --parallel \
          --max-concurrency 4 \
          --timeout 600000 \
          --output-dir ./integration-results \
          --report-format html
          
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
        conformance_status=$(jq -r '.overall' ./artifacts/conformance/conformance-results.json)
        if [[ "$conformance_status" != "pass" ]]; then
          echo "❌ Conformance verification failed"
          exit 1
        fi

        echo "ℹ️ Integration reports: ./integration-results/test-report-*.html"
        echo "✅ Phase 2 advanced quality gates (conformance) passed"
```

## 📊 監視とメトリクス

### ダッシュボードの構築

リアルタイム監視用のダッシュボードを構築できます：

```bash
# メトリクス収集の開始
ae-framework conformance metrics --format json --export metrics.json
ae-framework integration status --watch --refresh 60 > integration-status.log &

# ダッシュボード用データの準備
cat > dashboard-data.js << 'EOF'
// リアルタイムメトリクスの取得
const fs = require('fs');
const conformanceMetrics = require('./metrics.json');
const integrationReportPath = './integration-results/test-report-*.html';

// グラフ用データの生成
const generateDashboardData = () => {
  return {
    conformance: {
      totalVerifications: conformanceMetrics.counts?.totalVerifications || 0,
      totalViolations: conformanceMetrics.counts?.totalViolations || 0,
      averageExecutionTimeMs: conformanceMetrics.performance?.averageExecutionTime || 0
    },
    integration: {
      reportPath: integrationReportPath,
      passRate: null,      // HTMLのみのため機械集計はカスタム実装が必要
      totalTests: null,
      executionTimeMs: null
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
  totalViolations:
    warning: 5
    critical: 10
  averageExecutionTimeMs:
    warning: 1000
    critical: 2000

integration:
  # HTMLレポートのみのため、機械判定が必要ならカスタムReporterを実装
  passRate:
    warning: 95
    critical: 90
EOF

# アラート監視スクリプト
cat > monitor-quality.sh << 'EOF'
#!/bin/bash

check_thresholds() {
  local metrics_file=$1
  local thresholds_file=$2
  
  # メトリクスの取得
  local violations=$(jq -r '.counts.totalViolations' $metrics_file)
  local avg_exec=$(jq -r '.performance.averageExecutionTime' $metrics_file)
  
  # 閾値チェック
  if (( violations > 10 )); then
    echo "🚨 CRITICAL: Too many violations detected: $violations"
  elif (( violations > 5 )); then
    echo "⚠️  WARNING: Multiple violations detected: $violations"
  fi

  if (( $(echo "$avg_exec > 2000" | bc -l) )); then
    echo "🚨 CRITICAL: Average execution time above 2000ms: $avg_exec"
  elif (( $(echo "$avg_exec > 1000" | bc -l) )); then
    echo "⚠️  WARNING: Average execution time above 1000ms: $avg_exec"
  fi
}

# 定期チェックの実行
while true; do
  ae-framework conformance metrics --format json --export current-metrics.json
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
# 問題: 修復候補が適用されない
ae-framework fix analyze --input failures.json

# 解決: failure artifact の情報を増やす
ae-framework fix create-artifact \
  --type error \
  --message "Validation logic incomplete" \
  --file src/validator.ts \
  --line 15 \
  --output failure.json
ae-framework fix apply --input failure.json --output .ae/auto-fix --dry-run
```

#### 2. Runtime Conformance パフォーマンス問題

```bash
# 問題: 検証が遅い
ae-framework conformance metrics --format json

# 解決: サンプリング率の調整
ae-framework conformance config --set sampling.enabled=true
ae-framework conformance config --set sampling.rate=0.1

# 並行実行数の調整
ae-framework conformance config --set performance.maxConcurrentChecks=5
```

#### 3. Integration Testing の不安定性

```bash
# 問題: テストが断続的に失敗
ae-framework integration status

# 解決: タイムアウトの調整
ae-framework integration run --tests tests.json --timeout 60000 --retries 3

# テスト環境の確認
ae-framework integration list --type environments
```

## 🎯 ベストプラクティス

### 1. 段階的導入

```bash
# Step 1: Runtime Conformance から開始
ae-framework conformance sample --rules basic-rules.json
ae-framework conformance verify --input data.json --rules basic-rules.json

# Step 2: Integration Testing の追加
ae-framework integration generate --type test --test-type api --output basic-api-test.json
ae-framework integration run --tests basic-api-test.json --environment dev

# Step 3: CEGIS の統合
ae-framework fix analyze --input simple-failures.json
ae-framework fix apply --input simple-failures.json --verify
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
ae-framework conformance verify \
  --input .ae/shared/conformance-data.json \
  --context-file .ae/shared/conformance-context.json \
  --rules .ae/shared/conformance-rules.json

# 2. 統合テスト（基本セット）
ae-framework integration run --suites .ae/shared/basic-test-suite.json --environment shared

# 3. 修復が必要な問題の確認
ae-framework fix analyze --input .ae/shared/common-failures.json

echo "✅ Team validation complete"
EOF

chmod +x scripts/team-validation.sh
```

### 3. 継続的改善

現行CLIには履歴メトリクスの自動集計コマンドがありません。CIで保存した成果物を外部で集計してください。

- Conformance: `artifacts/conformance/conformance-results.json` / `reports/conformance/**`
- Integration: `test-report-*.html`（出力ディレクトリ配下、現行はHTMLのみ）
- CEGIS: `.ae/auto-fix/**`（適用結果/レポート）

例: Conformance結果の集計
```bash
ae-framework conformance report --directory artifacts/hermetic-reports/conformance --format both
```

## 🚀 次のステップ

Phase 2の高度な機能をマスターしたら、以下のステップに進むことができます：

### 1. カスタマイズの深化

```bash
# カスタム規則の作成
ae-framework conformance sample --rules custom-rule-template.json

# カスタムテストランナーの作成
ae-framework integration generate --type test --test-type api --name "Custom API Test" --output custom-test.json

# カスタム修復戦略の実装
ae-framework fix create-artifact --type error --message "Custom failure" --file src/app.ts --line 1 --output custom-failure.json
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
