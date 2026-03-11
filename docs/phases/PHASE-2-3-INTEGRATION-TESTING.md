---
docRole: ssot
lastVerified: 2026-03-11
owner: phase-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Phase 2.3: Integration Testing and End-to-End Testing System

> 🌍 Language / 言語: 日本語 | English

---

## English (Overview)

Phase 2.3 offers an orchestration system for integration and end‑to‑end testing at scale. It features a multi‑runner architecture, rich reporting, and CLI workflow to discover, run, and analyze complex test suites.

Highlights
- Event‑driven orchestration, discovery/filtering, parallel/sequential runs
- Runners: E2E (Playwright‑compatible), API (HTTP contract), extensible design
- Reporters: interactive HTML, artifacts (screenshots, logs, traces), failure analysis
- CLI: `run`, `discover`, `list`, `generate`, `status`, `reports`

See the Japanese sections for system architecture and CLI examples.

## English (Detailed)

### Runners
- E2E Runner (Playwright-compatible): browser automation and a11y hooks
- API Contract Runner: HTTP contract checks, auth helpers
- Extensible: add custom runners with a common result schema

### CLI
```text
ae-framework integration discover         # detect suites/tests/fixtures
ae-framework integration list             # list environments/runners/reporters
ae-framework integration run              # run suites/tests
ae-framework integration generate         # scaffold samples
ae-framework integration reports          # list/clean reports
```

### Reports & Artifacts
- HTML reporter with filters
- Default output: `artifacts/integration/test-results` (reports only; change with `--output-dir`)
- Attachments: screenshots/traces/videos are written under `artifacts/integration/test-results`

### Minimal CI YAML (English)
```text
name: Integration Tests
on: [pull_request]
jobs:
  integration:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: pnpm install --frozen-lockfile
      - run: ae-framework integration discover --patterns "./tests/**/*.json" --type tests --output artifacts/integration/test-results/discovery.json
      - run: ae-framework integration run --suites ./tests/integration/suites/*.json --environment default --output-dir artifacts/integration/test-results
      - uses: actions/upload-artifact@v4
        if: always()
        with:
          name: integration-artifacts
          path: |
            artifacts/integration/test-results/**
            apps/**/__e2e__/**
```

### Best Practices
- Keep E2E label-gated on PRs; run nightly for full coverage
- Stabilize flaky suites or move behind labels until fixed

> 包括的な統合テストとエンドツーエンドテストのオーケストレーション

## 概要

Phase 2.3では、複雑なアプリケーションの統合テストとエンドツーエンドテストを効率的に管理・実行するための統合システムを提供します。このシステムは、マルチランナーアーキテクチャと豊富なレポート機能により、大規模なテストスイートの実行と分析を支援します。

## 主要機能

### 1. 統合テストオーケストレーター
- **イベント駆動アーキテクチャ**: 非同期でのテスト実行とリソース管理
- **テスト発見とフィルタリング**: 柔軟な条件でのテスト選択
- **並列・順次実行**: パフォーマンス最適化された実行戦略
- **包括的レポート**: 詳細な実行結果とメトリクス

### 2. マルチランナーアーキテクチャ
- **E2Eテストランナー**: Playwright互換のブラウザ自動化
- **APIテストランナー**: HTTP契約検証と認証サポート
- **拡張可能設計**: カスタムランナーの簡単な追加

### 3. 豊富なレポート機能
- **HTMLレポーター**: インタラクティブなチャートとフィルタリング
- **アーティファクト管理**: スクリーンショット、ログ、トレース収集
- **失敗分析**: 詳細なエラー分析と可視化

### 4. 完全なCLI統合
- **6つのメインコマンド**: run、discover、list、generate、status、reports
- **ワークフロー管理**: 発見から実行まで完全な管理
- **サンプル生成**: テストケース、スイート、環境の自動生成

## アーキテクチャ

### システム構成

```
┌─────────────────────────────┐
│   Integration CLI           │
├─────────────────────────────┤
│ ┌─────────────────────────┐ │
│ │ Test Orchestrator       │ │
│ │ (Event-driven)          │ │
│ └─────────┬───────────────┘ │
│           │                 │
│ ┌─────────┼───────────────┐ │
│ │ Test Runners            │ │
│ │ ├── E2E Runner          │ │
│ │ └── API Runner          │ │
│ └─────────┼───────────────┘ │
│           │                 │
│ ┌─────────┼───────────────┐ │
│ │ Reporters               │ │
│ │ └── HTML Reporter       │ │
│ └─────────────────────────┘ │
└─────────────────────────────┘
```

### 技術スタック
- **TypeScript**: 型安全性と開発効率
- **Zod**: スキーマ検証とデータ型安全性  
- **EventEmitter**: 非同期イベント処理
- **Commander.js**: CLI フレームワーク
- **Playwright-compatible**: ブラウザ自動化（モック実装付き）
- **Vitest**: テスティングフレームワーク

## インストールと設定

### 基本セットアップ

```text
# ae-frameworkのインストール
pnpm add ae-framework

# CLI確認
ae-framework integration --help
```

### プロジェクト初期化

```text
# サンプル環境の生成
ae-framework integration generate --type environment --name test-env --output test-environment.json

# サンプルテストの生成
ae-framework integration generate --type test --test-type e2e --name "Login Test" --output login-test.json

# サンプルスイートの生成
ae-framework integration generate --type suite --name "Authentication Suite" --output auth-suite.json
```

## 基本使用方法

### 1. テスト発見

```text
# テストファイルの発見
ae-framework integration discover --patterns "./tests/**/*.json" --type tests

# すべてのリソース（テスト、スイート、フィクスチャ）の発見
ae-framework integration discover --patterns "./tests/**/*.json" --type all

# 発見結果をファイルに保存
ae-framework integration discover --patterns "./tests/**/*.json" --type all --output discovery-results.json
```

### 2. リソース一覧表示

```text
# 利用可能な環境の表示
ae-framework integration list --type environments

# テストランナーの表示
ae-framework integration list --type runners

# レポーターの表示
ae-framework integration list --type reporters
```

### 3. テスト実行

```text
# 基本的なテスト実行
ae-framework integration run --tests tests.json --environment default

# スイート実行
ae-framework integration run --suites test-suites.json --environment staging

# フィルタリング付き実行
ae-framework integration run --tests tests.json --categories e2e,integration --tags smoke --environment production

# 並列実行
ae-framework integration run --tests tests.json --parallel --max-concurrency 4 --environment default
```

### 4. システム状態監視

```text
# システム状態表示
ae-framework integration status

# ウォッチモード（リアルタイム監視）
ae-framework integration status --watch --refresh 5
```

### 5. レポート管理

```text
# レポート一覧表示
ae-framework integration reports --list

# 古いレポートのクリーンアップ
ae-framework integration reports --clean --days 7
```

## テスト定義

### テストケース定義

```text
{
  "id": "login-e2e-test",
  "name": "User Login E2E Test",
  "description": "End-to-end test for user login functionality",
  "category": "e2e",
  "severity": "critical",
  "enabled": true,
  "preconditions": [
    "User database is accessible",
    "Test user exists in database"
  ],
  "steps": [
    {
      "id": "navigate-step",
      "description": "Navigate to login page",
      "action": "navigate:/login",
      "data": {},
      "expectedResult": "Login page displayed"
    },
    {
      "id": "fill-username",
      "description": "Enter username",
      "action": "type:input[name=username]:testuser",
      "data": {
        "selector": "input[name=username]",
        "value": "testuser"
      },
      "expectedResult": "Username entered"
    },
    {
      "id": "fill-password",
      "description": "Enter password",
      "action": "type:input[name=password]:testpass",
      "data": {
        "selector": "input[name=password]",
        "value": "testpass"
      },
      "expectedResult": "Password entered"
    },
    {
      "id": "click-submit",
      "description": "Click login button",
      "action": "click:button[type=submit]",
      "data": {
        "selector": "button[type=submit]"
      },
      "expectedResult": "Login submitted"
    },
    {
      "id": "verify-success",
      "description": "Verify successful login",
      "action": "verify:text:.welcome:Welcome, testuser!",
      "data": {
        "selector": ".welcome"
      },
      "validation": {
        "type": "text",
        "expected": "Welcome, testuser!"
      },
      "expectedResult": "Welcome message displayed"
    }
  ],
  "expectedResults": [
    "User successfully logs in",
    "Welcome message is displayed"
  ],
  "fixtures": ["user-data-fixture"],
  "dependencies": [],
  "tags": ["authentication", "e2e", "smoke"],
  "metadata": {
    "estimatedDuration": 30000,
    "complexity": "medium",
    "stability": "stable",
    "lastUpdated": "2024-01-15T10:00:00.000Z"
  }
}
```

### APIテストケース定義

```text
{
  "id": "api-users-test",
  "name": "Users API Test",
  "description": "Test users API endpoints",
  "category": "integration",
  "severity": "major",
  "enabled": true,
  "steps": [
    {
      "id": "get-users",
      "description": "Get all users",
      "action": "api:request:GET:/api/users",
      "data": {
        "method": "GET",
        "url": "/api/users",
        "headers": {
          "Accept": "application/json"
        }
      },
      "validation": {
        "type": "status",
        "expected": 200
      }
    },
    {
      "id": "create-user",
      "description": "Create new user",
      "action": "api:request:POST:/api/users",
      "data": {
        "method": "POST",
        "url": "/api/users",
        "headers": {
          "Content-Type": "application/json"
        },
        "body": {
          "name": "Test User",
          "email": "test@example.com"
        }
      },
      "validation": {
        "type": "status",
        "expected": 201
      }
    }
  ],
  "tags": ["api", "users", "crud"]
}
```

### テストスイート定義

```text
{
  "id": "authentication-suite",
  "name": "Authentication Test Suite",
  "description": "Comprehensive authentication testing",
  "category": "e2e",
  "tests": [
    "login-e2e-test",
    "logout-e2e-test",
    "password-reset-test"
  ],
  "fixtures": ["user-data-fixture", "auth-config-fixture"],
  "configuration": {
    "parallel": false,
    "maxConcurrency": 2,
    "timeout": 300000,
    "retries": 1,
    "skipOnFailure": false,
    "failFast": false
  },
  "setup": [
    "sql:TRUNCATE users",
    "api:POST:/api/test/seed-users"
  ],
  "teardown": [
    "sql:TRUNCATE users",
    "shell:rm -rf ./tmp/test-data"
  ],
  "metadata": {
    "estimatedDuration": 600000,
    "priority": "high",
    "owner": "QA Team",
    "tags": ["authentication", "critical"]
  }
}
```

### 環境設定

```text
{
  "name": "test",
  "baseUrl": "http://localhost:3000",
  "apiUrl": "http://localhost:3000/api",
  "database": {
    "host": "localhost",
    "port": 5432,
    "name": "test_db",
    "username": "test_user",
    "password": "test_pass"
  },
  "variables": {
    "TEST_MODE": "true",
    "LOG_LEVEL": "debug"
  },
  "timeouts": {
    "default": 30000,
    "api": 10000,
    "ui": 5000,
    "database": 15000
  },
  "retries": {
    "max": 3,
    "delay": 1000
  }
}
```

## プログラマティック使用

※ 以下のAPI例はリポジトリ内の `src/integration` を直接参照する場合のみ有効です（npm公開版では未提供）。import パスは利用環境に合わせて調整してください。

### 基本的なAPI使用

```text
import { IntegrationTestOrchestrator } from '<repo>/src/integration/test-orchestrator.js';
import { E2ETestRunner } from '<repo>/src/integration/runners/e2e-runner.js';
import { APITestRunner } from '<repo>/src/integration/runners/api-runner.js';
import { HTMLTestReporter } from '<repo>/src/integration/reporters/html-reporter.js';

// オーケストレーター設定
const config = {
  environments: [
    {
      name: 'test',
      baseUrl: 'http://localhost:3000',
      apiUrl: 'http://localhost:3000/api',
      variables: { TEST_MODE: 'true' },
      timeouts: { default: 30000, api: 10000, ui: 5000 },
      retries: { max: 3, delay: 1000 }
    }
  ],
  defaultEnvironment: 'test',
  runners: [
    new E2ETestRunner({
      browser: 'chromium',
      headless: true,
      viewport: { width: 1280, height: 720 },
      timeout: 30000,
      retries: 1,
      screenshots: true,
      video: false,
      trace: false,
      slowMo: 0
    }),
    new APITestRunner({
      timeout: 10000,
      retries: 2,
      validateSchema: true,
      followRedirects: true,
      validateSSL: true,
      maxResponseSize: 1024 * 1024,
      defaultHeaders: { 'User-Agent': 'AE-Framework-Test' }
    })
  ],
  reporters: [new HTMLTestReporter()],
  globalTimeout: 600000,
  globalRetries: 1,
  parallelSuites: false,
  maxSuiteConcurrency: 2,
  artifactRetention: { days: 7, maxSize: 100 },
  notifications: { 
    enabled: false, 
    channels: [], 
    onFailure: false, 
    onSuccess: false 
  }
};

// オーケストレーター初期化
const orchestrator = new IntegrationTestOrchestrator(config);
await orchestrator.initialize();
```

### テスト実行

```text
// テスト発見
const mockDiscovery = {
  async discoverTests(): Promise<TestCase[]> {
    return [/* テストケース配列 */];
  },
  async discoverSuites(): Promise<TestSuite[]> {
    return [/* テストスイート配列 */];
  },
  async discoverFixtures(): Promise<TestFixture[]> {
    return [/* フィクスチャ配列 */];
  }
};

// テスト発見とキャッシュ
const discovered = await orchestrator.discoverTests(
  mockDiscovery, 
  ['./tests/**/*.json']
);

console.log(`Found ${discovered.tests.length} tests`);
console.log(`Found ${discovered.suites.length} suites`);
console.log(`Found ${discovered.fixtures.length} fixtures`);

// 単一テストの実行
const testResult = await orchestrator.executeTest(
  'login-e2e-test', 
  'test',
  {
    environment: 'test',
    parallel: false,
    maxConcurrency: 1,
    timeout: 60000,
    retries: 1,
    generateReport: true,
    outputDir: 'artifacts/integration/test-results'
  }
);

console.log(`Test ${testResult.testId} completed with status: ${testResult.status}`);

// テストスイートの実行
const suiteResult = await orchestrator.executeSuite(
  'authentication-suite',
  'test',
  {
    environment: 'test',
    parallel: true,
    maxConcurrency: 2,
    timeout: 300000,
    retries: 1,
    generateReport: true,
    captureScreenshots: true,
    collectLogs: true,
    outputDir: 'artifacts/integration/test-results',
    reportFormat: ['html'], // 現行実装はHTMLのみ
    filters: {
      categories: ['e2e'],
      tags: ['smoke'],
      severity: ['critical', 'major']
    }
  }
);

console.log(`Suite completed: ${suiteResult.statistics.total} total, ${suiteResult.statistics.passed} passed`);
```

### イベント監視

```text
// テスト実行イベントの監視
orchestrator.on('test_started', ({ testId, environment }) => {
  console.log(`Test ${testId} started in ${environment}`);
});

orchestrator.on('test_completed', ({ testId, status, duration }) => {
  console.log(`Test ${testId} completed: ${status} (${duration}ms)`);
});

orchestrator.on('suite_started', ({ suiteId, environment, executionId }) => {
  console.log(`Suite ${suiteId} started (${executionId})`);
});

orchestrator.on('suite_completed', ({ suiteId, executionId, duration, statistics }) => {
  console.log(`Suite ${suiteId} completed in ${duration}ms`);
  console.log(`Results: ${statistics.passed}/${statistics.total} passed`);
});

orchestrator.on('violation_detected', (violation) => {
  console.error(`Violation detected: ${violation.message}`);
});
```

## E2Eテストランナー

### 基本的な使用方法

```text
import { E2ETestRunner } from '<repo>/src/integration/runners/e2e-runner.js';

const e2eRunner = new E2ETestRunner({
  browser: 'chromium',
  headless: false,
  viewport: { width: 1920, height: 1080 },
  timeout: 30000,
  retries: 2,
  screenshots: true,
  video: true,
  trace: true,
  slowMo: 100
});

// 環境のセットアップ
await e2eRunner.setup(environment);

// テスト実行
const result = await e2eRunner.runTest(testCase, environment);

// 環境のクリーンアップ
await e2eRunner.teardown(environment);
```

### 対応するアクション

E2Eテストランナーは以下のアクションをサポートします：

- `navigate:url` - ページナビゲーション
- `click:selector` - 要素クリック
- `type:selector:value` - テキスト入力
- `select:selector:value` - セレクト操作
- `wait:timeout` - 待機
- `verify:type:selector:expected` - 検証
- `screenshot` - スクリーンショット取得
- `custom:action` - カスタムアクション

### 検証タイプ

- `text` - テキスト内容の検証
- `attribute` - 属性値の検証
- `exists` - 要素存在の検証
- `count` - 要素数の検証
- `css` - CSS プロパティの検証

## APIテストランナー

### 基本的な使用方法

```text
import { APITestRunner } from '<repo>/src/integration/runners/api-runner.js';

const apiRunner = new APITestRunner({
  timeout: 15000,
  retries: 3,
  validateSchema: true,
  followRedirects: true,
  validateSSL: true,
  maxResponseSize: 2 * 1024 * 1024,
  defaultHeaders: {
    'User-Agent': 'AE-Framework-API-Test',
    'Accept': 'application/json'
  }
});

// API テスト実行
const result = await apiRunner.runTest(apiTestCase, environment);
```

### サポートする検証

- **ステータスコード**: HTTP レスポンスステータスの検証
- **レスポンススキーマ**: JSON スキーマによる構造検証
- **ヘッダー**: レスポンスヘッダーの検証
- **レスポンス時間**: パフォーマンス要件の検証
- **認証**: 様々な認証方式のサポート

## HTMLレポーター

HTMLレポーターは、テスト結果を視覚的に分析できるインタラクティブなレポートを生成します。

### 生成されるレポート機能

1. **実行サマリー**: 総テスト数、成功率、実行時間
2. **インタラクティブチャート**: 結果の視覚化
3. **フィルタリング機能**: ステータス、カテゴリ、タグによる絞り込み
4. **詳細ビュー**: 個別テスト結果の詳細表示
5. **アーティファクト表示**: スクリーンショット、ログの表示
6. **失敗分析**: エラーメッセージとスタックトレース
7. **トレンド分析**: 過去実行との比較

### カスタマイズ

```text
import { HTMLTestReporter } from '<repo>/src/integration/reporters/html-reporter.js';

// 現行実装ではオプション引数は未提供。
// カスタムレポートが必要な場合は独自Reporterを実装して差し替える。
const htmlReporter = new HTMLTestReporter();
```

## CLI コマンドリファレンス

### `ae-framework integration run`
テスト実行

```text
ae-framework integration run [options]

Options:
  --tests <files>         テストファイル（カンマ区切り）
  --suites <files>        スイートファイル（カンマ区切り）
  --environment <name>    実行環境
  --categories <list>     カテゴリフィルター
  --tags <list>           タグフィルター
  --exclude <list>        除外テストID
  --parallel [boolean]    並列実行
  --max-concurrency <n>   最大並行数
  --timeout <ms>          実行タイムアウト
  --retries <n>           リトライ回数
  --fail-fast             最初の失敗で停止
  --skip-on-failure       失敗後の残りテストをスキップ
  --output-dir <dir>      出力ディレクトリ
  --report-format <fmt>   レポート形式 (html。json/xml/junitは未実装)
  --screenshots           失敗時スクリーンショット
  --video                 実行動画を保存
  --coverage              カバレッジ計測
```

### `ae-framework integration discover`
テスト発見

```text
ae-framework integration discover [options]

Options:
  --patterns <patterns>   検索パターン（カンマ区切り）
  --type <type>          リソースタイプ (tests|suites|fixtures|all)
  --output <file>        出力ファイル
  --format <format>      出力形式 (json|table)
```

### `ae-framework integration list`
リソース一覧

```text
ae-framework integration list [options]

Options:
  --type <type>          リソースタイプ (environments|runners|reporters)
```

### `ae-framework integration generate`
サンプル生成

```text
ae-framework integration generate [options]

Options:
  --type <type>          生成タイプ (test|suite|fixture|environment)
  --test-type <type>     テストタイプ (e2e|api|unit)
  --name <name>          名前
  --output <file>        出力ファイル
```

### `ae-framework integration status`
システム状態

```text
ae-framework integration status [options]

Options:
  --watch                ウォッチモード
  --refresh <seconds>    更新間隔
```

### `ae-framework integration reports`
レポート管理

```text
ae-framework integration reports [options]

Options:
  --list                 レポート一覧
  --view <reportId>      レポートの表示
  --clean                古いレポート削除
  --days <days>          保持期間（日数）
```

## 実践的な使用例

### CI/CDパイプライン統合

```text
# .github/workflows/integration-tests.yml
name: Integration Tests

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  integration-tests:
    runs-on: ubuntu-latest
    
    services:
      postgres:
        image: postgres:13
        env:
          POSTGRES_PASSWORD: test
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5

    steps:
    - uses: actions/checkout@v3
    
    - name: Setup Node.js
      uses: actions/setup-node@v3
      with:
        node-version: '18'
        
    - name: Install dependencies
      run: pnpm install --frozen-lockfile
      
    - name: Start test environment
      run: |
        pnpm run start:server &
        npx wait-on http://localhost:3000
        
    - name: Run integration tests
      run: |
        ae-framework integration run \
          --suites ./tests/integration/suites/*.json \
          --environment ci \
          --parallel \
          --max-concurrency 4 \
          --timeout 300000 \
          --retries 2 \
          --output-dir artifacts/integration/test-results \
          --report-format html
          
    - name: Upload test results
      uses: actions/upload-artifact@v3
      if: always()
      with:
        name: integration-test-results
        path: artifacts/integration/test-results/
      # NOTE: 現行実装はHTMLレポートのみ。JUnit/JSONが必要ならカスタムReporterを追加。
```

### Docker環境での実行

```dockerfile
# Dockerfile.integration-tests
FROM mcr.microsoft.com/playwright:v1.40.0-focal

WORKDIR /app

COPY package*.json ./
RUN corepack enable && pnpm install --frozen-lockfile

COPY . .
RUN pnpm run build

# テスト実行用スクリプト
COPY integration-test-entrypoint.sh /entrypoint.sh
RUN chmod +x /entrypoint.sh

ENTRYPOINT ["/entrypoint.sh"]
```

```text
#!/bin/bash
# integration-test-entrypoint.sh

set -e

# 環境変数の設定
export NODE_ENV=test
export TEST_PARALLEL=${TEST_PARALLEL:-true}
export MAX_CONCURRENCY=${MAX_CONCURRENCY:-4}

# テスト実行
ae-framework integration run \
  --tests ${TEST_FILES:-"./tests/**/*.json"} \
  --environment ${TEST_ENVIRONMENT:-"docker"} \
  ${TEST_PARALLEL:+--parallel} \
  --max-concurrency ${MAX_CONCURRENCY} \
  --timeout ${TEST_TIMEOUT:-300000} \
  --output-dir ${OUTPUT_DIR:-"artifacts/integration/test-results"} \
  --report-format html

# 結果の後処理
if [ -n "${POST_PROCESS_SCRIPT}" ]; then
  bash ${POST_PROCESS_SCRIPT}
fi
```

### ローカル開発での使用

```text
# 開発用環境でのテスト実行セット
#!/bin/bash
# scripts/run-integration-tests.sh

# 1. テスト環境の起動
echo "Starting test environment..."
pnpm run start:server &
TEST_SERVER_PID=$!

# 健全性チェック
npx wait-on http://localhost:3000 --timeout 60000

# 2. テストの発見
echo "Discovering tests..."
ae-framework integration discover \
  --patterns "./tests/integration/**/*.json" \
  --type all \
  --output ./discovered-tests.json

# 3. スモークテストの実行
echo "Running smoke tests..."
ae-framework integration run \
  --tests ./discovered-tests.json \
  --tags smoke \
  --environment local \
  --output-dir artifacts/integration/test-results/smoke

# 4. フル統合テストの実行
echo "Running full integration tests..."
ae-framework integration run \
  --suites ./tests/integration/suites/*.json \
  --environment local \
  --parallel \
  --max-concurrency 2 \
  --output-dir artifacts/integration/test-results/full \
  --report-format html

# 5. レポートを開く
echo "Opening test report..."
open ./artifacts/integration/test-results/full/test-report-*.html

# 6. クリーンアップ
cleanup() {
  echo "Cleaning up..."
  kill $TEST_SERVER_PID 2>/dev/null || true
}
trap cleanup EXIT
```

## パフォーマンス最適化

### 並列実行の最適化

```text
// 最適な並行数の計算
const optimalConcurrency = Math.min(
  os.cpus().length,
  Math.floor(process.env.CI ? 4 : 8), // CI環境では控えめに
  testSuite.configuration.maxConcurrency || 4
);

// 実行時間に基づく動的調整
const executionConfig = {
  parallel: testSuite.tests.length > 5,
  maxConcurrency: optimalConcurrency,
  timeout: calculateOptimalTimeout(testSuite),
  retries: process.env.CI ? 2 : 1 // CI環境ではリトライ増加
};
```

### リソース使用量の最適化

```text
// メモリ使用量の監視と制御
const memoryUsage = process.memoryUsage();
if (memoryUsage.heapUsed > 1024 * 1024 * 1024) { // 1GB
  console.warn('High memory usage detected, forcing garbage collection');
  if (global.gc) {
    global.gc();
  }
}

// アーティファクトサイズの制限
const artifactConfig = {
  maxScreenshotSize: 5 * 1024 * 1024, // 5MB
  maxLogSize: 10 * 1024 * 1024,       // 10MB
  maxVideoSize: 50 * 1024 * 1024,     // 50MB
  compressionEnabled: true,
  cleanupAfterDays: 7
};
```

## トラブルシューティング

### よくある問題と解決方法

#### 1. ブラウザの起動失敗

```text
# Dockerコンテナ内での権限問題
ERROR: Browser launch failed: Failed to launch chromium

# 解決方法
# 推奨: Playwright公式イメージの利用、または依存関係の導入
# 例（隔離を保ったまま /dev/shm を拡張）
docker run --rm --ipc=host --shm-size=1g mcr.microsoft.com/playwright:v1.40.0-jammy

# 追加の権限（SYS_ADMIN / seccomp=unconfined）は避ける
# ヘッドレス設定はランナー側で調整（CLIフラグは現行未提供）
```

#### 2. タイムアウトエラー

```text
# ネットワーク遅延による問題
ERROR: Test timeout after 30000ms

# 解決方法：タイムアウトの調整
ae-framework integration run --tests tests.json --timeout 60000

# または、環境別のタイムアウト設定
{
  "name": "slow-network",
  "timeouts": {
    "default": 60000,
    "api": 30000,
    "ui": 45000
  }
}
```

#### 3. 並列実行での競合

```text
# データベース競合エラー
ERROR: Database connection conflict in parallel execution

# 解決方法：トランザクション分離
ae-framework integration run --tests tests.json --max-concurrency 1

# または、テスト間の依存関係の明示
{
  "configuration": {
    "parallel": false,
    "testIsolation": "database_transaction"
  }
}
```

#### 4. メモリリーク

```text
# メモリ使用量の監視
DEBUG=integration:memory ae-framework integration run --tests tests.json

# ガベージコレクションの強制実行
node --expose-gc node_modules/.bin/ae-framework integration run --tests tests.json
```

## セキュリティ考慮事項

### テストデータの保護

```text
// 機密情報のマスキング
const sanitizeTestData = (data: any): any => {
  const sensitiveFields = ['password', 'token', 'apiKey', 'secret'];
  
  return JSON.parse(JSON.stringify(data, (key, value) => {
    if (sensitiveFields.includes(key.toLowerCase())) {
      return '***MASKED***';
    }
    return value;
  }));
};

// ログとレポートでの自動マスキング
orchestrator.on('test_completed', (result) => {
  result.logs = result.logs.map(log => sanitizeLogMessage(log));
  result.screenshots = result.screenshots.filter(screenshot => 
    !containsSensitiveContent(screenshot)
  );
});
```

### アクセス制御

```text
# テスト実行権限の制限
chmod 700 ./scripts/run-integration-tests.sh

# 設定ファイルの保護
chmod 600 ./test-environments/*.json

# Docker実行時の最小権限
docker run --user $(id -u):$(id -g) --read-only ae-framework-tests
```

## 次のステップ

Phase 2.3の実装が完了したら、以下のフェーズに進めます：

- **Phase 2.2との統合**: [Runtime Conformance System](./PHASE-2-2-RUNTIME-CONFORMANCE.md) との連携
- **Phase 2.1との統合**: [CEGIS Auto-Fix System](../architecture/CEGIS-DESIGN.md) との統合
- **Phase 6**: [UI/UX & Frontend Delivery](./phase-6-uiux.md) での E2E テスト活用

## 関連ドキュメント

- [Runtime Conformance Architecture](../architecture/RUNTIME-CONFORMANCE-DESIGN.md)
- [CEGIS Design Document](../architecture/CEGIS-DESIGN.md)
- [CLI Commands Reference](../reference/CLI-COMMANDS-REFERENCE.md)
- [TDD Framework Architecture](../architecture/TDD-FRAMEWORK-ARCHITECTURE.md)
- [Phase 6: UI/UX & Frontend Delivery](./phase-6-uiux.md)

---

**Phase 2.3 Integration Testing System** - 包括的テストオーケストレーションによる品質保証 🧪
