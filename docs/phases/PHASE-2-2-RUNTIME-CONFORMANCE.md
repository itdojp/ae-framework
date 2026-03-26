---
docRole: ssot
lastVerified: 2026-03-26
owner: phase-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Phase 2.2: Runtime Conformance Verification System

> 🌍 Language / 言語: English | 日本語

---

## English

> Real-time monitoring and verification system for application conformance

### Overview

Phase 2.2 provides a runtime conformance verification system that monitors whether an application continues to satisfy declared specifications and quality thresholds while it is running. The phase is designed to work with the CEGIS auto-remediation flow from Phase 2.1: once a violation is detected, the result can be converted into a failure artifact and passed to `ae-framework fix` or an equivalent follow-up workflow.

### Contract terminology

- In this document, "runtime contract" means a Design by Contract (DbC) style rule such as a precondition, postcondition, or invariant checked against runtime data.
- API contract verification with Pact belongs to CI-side API / integration contract testing and is documented separately.
- Required vs optional report rules are governed by the artifacts contract and Verify Lite policies, not by the runtime verifier itself.

### Key capabilities

#### 1. Rule-based verification engine

- Configurable execution policy: sampling, cache usage, timeout, and concurrency are all part of the runtime configuration.
- Pattern-oriented analysis: violations are grouped and surfaced so recurring issues can be prioritized.
- Severity-driven triage: `minor`, `major`, and `critical` rules can be handled differently downstream.
- Performance-aware execution: the engine exposes timeout and concurrency controls so the monitor can run in production-like paths.

#### 2. Real-time monitoring system

- Event-driven architecture for asynchronous detection and notification.
- Multiple monitors can run together under one engine.
- Metrics are collected continuously and exported through CLI or programmatic APIs.
- Detailed reports can be integrated into quality evidence or operator dashboards.

#### 3. Specialized monitors

- Data validation monitor: schema-based runtime validation.
- API contract monitor: HTTP response and endpoint behavior checks.
- Custom monitors: additional domain-specific rules can be registered when the default surfaces are not enough.

#### 4. CLI integration

- Operational commands cover verification, rules, config, metrics, status, sample generation, and aggregated reporting.
- The same command surface supports both local debugging and CI-side evidence generation.

### Architecture

#### System layout

```text
┌─────────────────────┐    ┌─────────────────────┐
│ Verification Engine │ ←→ │   Rule Engine      │
│ (Event-driven)      │    │ (Configurable)     │
└─────────┬───────────┘    └─────────────────────┘
          │
          ├── Data Validation Monitor
          ├── API Contract Monitor
          └── Custom Monitors
```

### Technology stack

- TypeScript for typed engine and CLI implementation.
- Zod and JSON-schema style validation for runtime payload checks.
- `EventEmitter` for asynchronous monitoring hooks.
- Commander.js for CLI composition.
- Vitest for regression coverage.

### Installation and setup

#### Basic setup

```text
# Install ae-framework
pnpm add ae-framework

# Check CLI surface
ae-framework conformance --help
```

#### Generate starter files

```text
# Generate a sample configuration
ae-framework conformance sample --config conformance-config.json

# Edit the generated file
# conformance-config.json will be created
```

### Basic usage

#### 1. Initialize the verification system

```text
# Check current status
ae-framework conformance status

# Generate sample rules
ae-framework conformance sample --rules rules.json
```

#### 2. Define rules

Example rule definition file (JSON array):

```text
[
  {
    "id": "7488a940-9fd6-492b-9160-82c3c2ba0a60",
    "name": "Required Email Field",
    "description": "Ensures email field is present and valid",
    "category": "data_validation",
    "severity": "major",
    "enabled": true,
    "condition": {
      "expression": "required && email",
      "variables": ["data.email"],
      "constraints": {}
    },
    "actions": ["log_violation"],
    "metadata": {
      "createdAt": "2025-08-20T23:50:46.701Z",
      "updatedAt": "2025-08-20T23:50:46.701Z",
      "version": "1.0.0",
      "tags": ["email", "required", "sample"]
    }
  },
  {
    "id": "8d989667-6eb7-40ac-81b0-34902cf5070f",
    "name": "API Response Time",
    "description": "Ensures API responses are within acceptable time limits",
    "category": "api_contract",
    "severity": "minor",
    "enabled": true,
    "condition": {
      "expression": "timeout",
      "variables": ["data.response.time"],
      "constraints": {"maxMs": 1000}
    },
    "actions": ["log_violation", "metric_increment"],
    "metadata": {
      "createdAt": "2025-08-20T23:50:46.701Z",
      "updatedAt": "2025-08-20T23:50:46.701Z",
      "version": "1.0.0",
      "tags": ["performance", "api", "sample"]
    }
  }
]
```

#### 3. Run verification

```text
# Basic verification run
ae-framework conformance verify --input data.json --rules rules.json

# JSON output with runtime context
ae-framework conformance verify --input data.json --rules rules.json \
  --context-file context.json --format json \
  --output artifacts/conformance/conformance-results.json
```

#### 4. Check metrics

```text
# Show runtime metrics
ae-framework conformance metrics

# Export detailed metrics as JSON
ae-framework conformance metrics --format json --export metrics.json
```

### Programmatic usage

The API examples below are valid only when you reference repository `src/` files directly. They are not exposed as a stable npm package import surface, so adjust the import paths to your working tree.

#### Basic API usage

```text
import { ConformanceVerificationEngine } from '<repo>/src/conformance/verification-engine.js';
import { DataValidationMonitor } from '<repo>/src/conformance/monitors/data-validation-monitor.js';

// Initialize the verification engine
const engine = new ConformanceVerificationEngine({
  enabled: true,
  mode: 'permissive',
  sampling: { enabled: false, rate: 1.0, strategy: 'random' },
  performance: {
    timeoutMs: 5000,
    maxConcurrentChecks: 10,
    cacheResults: true,
    cacheTtlMs: 300000
  },
  reporting: { destinations: ['console'], batchSize: 100, flushIntervalMs: 30000 },
  alerting: { enabled: false, thresholds: {}, channels: [] },
  rules: []
});

// Add a data validation monitor
const dataMonitor = new DataValidationMonitor();
engine.addMonitor(dataMonitor);

// Start the engine
await engine.start();

// Register a violation handler
engine.on('violation_detected', (violation) => {
  console.log(`Violation detected: ${violation.message}`);
  // send alerts or trigger follow-up remediation here
});

// Execute verification
const context = {
  timestamp: new Date().toISOString(),
  executionId: '550e8400-e29b-41d4-a716-446655440000',
  environment: 'development',
  metadata: {
    source: 'api-endpoint',
    data: { username: 'test', email: 'test@example.com' }
  }
};

const result = await engine.verify({ username: 'test', email: 'test@example.com' }, context);
```

#### Advanced configuration

```text
import { ConformanceVerificationEngine } from '<repo>/src/conformance/verification-engine.js';
import { APIContractMonitor } from '<repo>/src/conformance/monitors/api-contract-monitor.js';

// Engine configuration (current implementation shape)
const engine = new ConformanceVerificationEngine({
  enabled: true,
  mode: 'permissive',
  sampling: { enabled: false, rate: 1.0, strategy: 'random' },
  performance: {
    timeoutMs: 30000,
    maxConcurrentChecks: 10,
    cacheResults: true,
    cacheTtlMs: 300000
  },
  reporting: {
    destinations: ['console'],
    batchSize: 100,
    flushIntervalMs: 30000
  },
  alerting: { enabled: false, thresholds: {}, channels: [] },
  rules: []
});

// API contract monitor (current implementation exposes no extra options)
const apiMonitor = new APIContractMonitor();
engine.addMonitor(apiMonitor);
```

### Monitoring and metrics

#### Available metrics

1. Execution metrics
   - Number of rule executions
   - Success / failure rate
   - Average execution time
   - Concurrency statistics

2. Violation metrics
   - Violation count
   - Distribution by severity
   - Pattern-analysis results
   - Trend analysis

3. Performance metrics
   - Response time (aggregated in `ConformanceMetrics`)
   - Optional, per-check-only fields exposed by some monitors:
     - CPU usage
     - Memory usage
     - Network I/O

#### Metrics collection example

```text
// Real-time metrics
engine.on('metrics_collected', (metrics) => {
  console.log('Counts:', metrics.counts);
  console.log('Performance:', metrics.performance);
  console.log('Top violations:', metrics.topViolations);
});

// Periodic metrics collection
setInterval(() => {
  const metrics = engine.getMetrics();
  // persist or visualize metrics here
}, 60000);
```

### CEGIS integration

The Runtime Conformance System is intended to convert detected violations into failure artifacts and hand them off to the CEGIS (Phase 2.1) `fix` flow. The current implementation does not ship an automatic bridge class, so the handoff is done through CLI commands or a repository-specific wrapper.

#### Auto-remediation flow

```text
# Example: convert a conformance result into a failure artifact and pass it to fix
ae-framework fix create-artifact \
  --type contract \
  --message "Conformance violation" \
  --file src/app.ts \
  --line 42 \
  --output failure.json

ae-framework fix apply --input failure.json --output .ae/auto-fix --dry-run
```

### CLI command reference

#### `ae-framework conformance verify`

Run runtime conformance verification.

```text
ae-framework conformance verify [options]

Options:
  --input <file>           Input data JSON file (required unless --trace-bundle is used)
  --trace-bundle <file>    Trace bundle JSON file (ae-trace-bundle/v1)
  --rules <file>           Rules definition file
  --output <file>          Output file (default: artifacts/conformance/conformance-results.json)
  --rule-ids <ids>         Rule IDs to execute (comma-separated)
  --skip-categories <cats> Categories to skip (comma-separated)
  --context-file <file>    Runtime context JSON file
  --format <format>        Output format (json|markdown)
  --verbose                Verbose output
```

#### `ae-framework conformance rules`

Manage rules.

```text
ae-framework conformance rules [options]

Options:
  --list                   List all rules
  --category <category>    Filter by category
  --add <file>             Add rules from a JSON file
  --remove <id>            Remove a rule by ID
  --export <file>          Export rules
  --import <file>          Import rules
```

#### `ae-framework conformance config`

Manage engine configuration.

```text
ae-framework conformance config [options]

Options:
  --show                   Show current configuration
  --update <file>          Update configuration from JSON
  --set <key=value>        Update a configuration value
  --export <file>          Export configuration
  --reset                  Reset to the default configuration
```

#### `ae-framework conformance metrics`

Show metrics.

```text
ae-framework conformance metrics [options]

Options:
  --format <format>        Output format (table|json)
  --export <file>          Output file path
  --reset                  Reset metrics
```

#### `ae-framework conformance status`

Show system status.

```text
ae-framework conformance status [options]

Options:
  --monitors               Show monitor information
  --handlers               Show violation handler information
```

#### `ae-framework conformance sample`

Generate sample files.

```text
ae-framework conformance sample [options]

Options:
  --rules <file>           Generate a sample rules file
  --config <file>          Generate a sample config file
  --data <file>            Generate a sample input data file
  --context <file>         Generate a sample runtime context file
```

#### `ae-framework conformance report`

Generate an aggregated conformance report.

```text
ae-framework conformance report [options]

Options:
  --inputs <files...>      Result files to include explicitly
  --glob <patterns...>     Glob pattern(s) for result discovery
  --directory <dir>        Search directory (default: artifacts/hermetic-reports/conformance)
  --pattern <glob>         Glob pattern when using --directory (default: *.json)
  --format <format>        Output format (json|markdown|both)
  --output <file>          JSON output path (default: reports/conformance/conformance-summary.json)
  --markdown-output <file> Markdown output path (default: reports/conformance/conformance-summary.md)
  --no-default-discovery   Disable default discovery locations
```

### Practical usage examples

#### Web application monitoring

```text
// Example integration in an Express.js application
import express from 'express';
import { ConformanceVerificationEngine } from '<repo>/src/conformance/verification-engine.js';
import { APIContractMonitor } from '<repo>/src/conformance/monitors/api-contract-monitor.js';

const app = express();
const engine = new ConformanceVerificationEngine({
  enabled: true,
  mode: 'permissive',
  sampling: { enabled: false, rate: 1.0, strategy: 'random' },
  performance: { timeoutMs: 5000, maxConcurrentChecks: 10, cacheResults: true, cacheTtlMs: 300000 },
  reporting: { destinations: ['console'], batchSize: 100, flushIntervalMs: 30000 },
  alerting: { enabled: false, thresholds: {}, channels: [] },
  rules: []
});

// Configure API monitoring
engine.addMonitor(new APIContractMonitor());
await engine.start();

// Integrate as middleware
app.use(async (req, res, next) => {
  const context = {
    timestamp: new Date().toISOString(),
    executionId: '550e8400-e29b-41d4-a716-446655440002',
    environment: 'development',
    metadata: {
      source: `${req.method} ${req.path}`,
      request: { method: req.method, path: req.path, headers: req.headers },
      data: req.body
    }
  };

  const apiCall = {
    method: req.method,
    url: req.originalUrl ?? req.url,
    path: req.path,
    headers: req.headers,
    body: req.body,
    timestamp: new Date().toISOString()
  };
  const result = await engine.verify(apiCall, context);
  if (result.violations.length > 0) {
    return res.status(400).json({ error: 'Conformance violation', violations: result.violations });
  }

  next();
});
```

#### Data pipeline monitoring

```text
// Example integration in a data processing pipeline
import { ConformanceVerificationEngine } from '<repo>/src/conformance/verification-engine.js';
import { DataValidationMonitor } from '<repo>/src/conformance/monitors/data-validation-monitor.js';

const engine = new ConformanceVerificationEngine({
  enabled: true,
  mode: 'permissive',
  sampling: { enabled: false, rate: 1.0, strategy: 'random' },
  performance: { timeoutMs: 5000, maxConcurrentChecks: 10, cacheResults: true, cacheTtlMs: 300000 },
  reporting: { destinations: ['console'], batchSize: 100, flushIntervalMs: 30000 },
  alerting: { enabled: false, thresholds: {}, channels: [] },
  rules: []
});

engine.addMonitor(new DataValidationMonitor());
await engine.start();

async function processData(data) {
  for (const record of data) {
    const context = {
      timestamp: new Date().toISOString(),
      executionId: '550e8400-e29b-41d4-a716-446655440001',
      environment: 'development',
      metadata: {
        source: 'data-pipeline',
        data: record
      }
    };

    const validation = await engine.verify(record, context);

    if (validation.violations.length > 0) {
      console.log(`Data validation failed: ${validation.violations.length}`);
      await quarantineData(record, validation.violations);
      continue;
    }

    await processRecord(record);
  }
}

await engine.stop();
```

### Troubleshooting

#### Common issues and resolutions

##### 1. Performance issues

```text
# Lower the sampling rate
ae-framework conformance config --set sampling.enabled=true
ae-framework conformance config --set sampling.rate=0.05

# Reduce concurrency
ae-framework conformance config --set performance.maxConcurrentChecks=5
```

##### 2. Memory growth

```text
# Disable caching or shorten the TTL
ae-framework conformance config --set performance.cacheResults=false
ae-framework conformance config --set performance.cacheTtlMs=60000
```

##### 3. Rule execution failures

```text
# List rules
ae-framework conformance rules --list

# Re-run with verbose output
ae-framework conformance verify --input data.json --rules rules.json --verbose
```

### Optimization guidelines

#### Performance tuning

1. Use an appropriate sampling rate.
   - Development: `0.1-0.2` (10-20%)
   - Staging: `0.05-0.1` (5-10%)
   - Production: `0.01-0.05` (1-5%)

2. Apply a cache strategy that matches rule cost and data volatility.
   - Cache frequently executed rules.
   - Keep TTL aligned with data freshness.
   - Monitor memory growth while cache is enabled.

3. Adjust concurrency to the runtime environment.
   - Size concurrency by CPU capacity.
   - Separate I/O-heavy rules from CPU-heavy rules when needed.

#### Scalability

1. Horizontal scaling
   - Distribute monitoring load across multiple instances.
   - Aggregate metrics into a shared observability surface.

2. Vertical scaling
   - Allocate CPU and memory deliberately.
   - Tune the runtime when Node.js process limits become relevant.

### Security considerations

1. Protect sensitive data.
   - Mask secrets in logs and metrics.
   - Exclude sensitive fields from rule definitions where possible.

2. Enforce access control.
   - Restrict CLI execution permissions.
   - Control access to configuration files and artifacts.

3. Preserve auditability.
   - Record operational changes.
   - Track rule updates and investigation steps.

### Next steps

After Phase 2.2 is in place, continue with:

- Phase 2.3: [Integration Testing](./PHASE-2-3-INTEGRATION-TESTING.md)
- Stronger coordination with Phase 2.1: [CEGIS Auto-Fix System](../architecture/CEGIS-DESIGN.md)

### Related documents

- [CEGIS Design Document](../architecture/CEGIS-DESIGN.md)
- [Runtime Conformance Architecture](../architecture/RUNTIME-CONFORMANCE-DESIGN.md)
- [CLI Commands Reference](../reference/CLI-COMMANDS-REFERENCE.md)
- [TDD Framework Architecture](../architecture/TDD-FRAMEWORK-ARCHITECTURE.md)

## 日本語

> リアルタイムでアプリケーションの適合性を監視・検証するシステム

### 概要

Phase 2.2では、アプリケーションが実行時に定義された仕様や品質基準に適合しているかをリアルタイムで監視・検証するシステムを提供します。このシステムは、CEGIS自動修復システム（Phase 2.1）と連携し、違反を検出した際の自動修正フローを実現します。

#### 用語注記（contract）
- 本ドキュメントの「ランタイム契約」は **Design contract（DbC）**（pre/post/invariant）を指します。
- Pact などの API 契約検証は **API/Integration contract test** として CI で扱います。
- 成果物の必須/任意ルールは **Artifacts contract** として別管理します。

### 主要機能

#### 1. 規則ベース検証エンジン
- **設定可能な規則実行**: サンプリング率、キャッシュ、並行実行制御
- **パターン分析**: 違反パターンの自動検出
- **リスク評価**: 重要度に基づく優先度付け
- **パフォーマンス最適化**: タイムアウト処理と並行実行

#### 2. リアルタイム監視システム
- **イベント駆動アーキテクチャ**: 非同期での違反検出・通知
- **複数モニター統合**: データ検証、API契約監視の統合管理
- **メトリクス収集**: パフォーマンス指標と品質メトリクスの収集
- **包括的レポート**: 違反状況とシステム状態の詳細レポート

#### 3. 特殊化されたモニター
- **データ検証モニター**: Zodスキーマによる型安全性と検証
- **API契約モニター**: HTTP契約、レート制限、タイムアウト監視
- **カスタムモニター**: 独自の業務ルール監視

#### 4. CLI統合
- **包括的コマンド**: verify、rules、config、metrics、status、sample
- **ワークフロー管理**: 検証から設定まで完全な管理機能

### アーキテクチャ

#### システム構成

```
┌─────────────────────┐    ┌─────────────────────┐
│ Verification Engine │ ←→ │   Rule Engine      │
│ (Event-driven)      │    │ (Configurable)     │
└─────────┬───────────┘    └─────────────────────┘
          │
          ├── Data Validation Monitor
          ├── API Contract Monitor
          └── Custom Monitors
```

#### 技術スタック
- **TypeScript**: 型安全性とコード品質
- **Zod**: スキーマ検証とデータ型安全性
- **EventEmitter**: 非同期イベント処理
- **Commander.js**: CLI インターフェース
- **Vitest**: 包括的テストカバレッジ

### インストールと設定

#### 基本セットアップ

```text
# ae-frameworkのインストール
pnpm add ae-framework

# CLI確認
ae-framework conformance --help
```

#### 設定ファイル作成

```text
# サンプル設定の生成
ae-framework conformance sample --config conformance-config.json

# 設定ファイルの編集
# conformance-config.json が生成されます
```

### 基本使用方法

#### 1. 検証システムの初期化

```text
# システム状態確認
ae-framework conformance status

# サンプル規則の作成
ae-framework conformance sample --rules rules.json
```

#### 2. 規則定義

規則定義ファイル（JSON配列）の例：

```text
[
    {
      "id": "7488a940-9fd6-492b-9160-82c3c2ba0a60",
      "name": "Required Email Field",
      "description": "Ensures email field is present and valid",
      "category": "data_validation",
      "severity": "major",
      "enabled": true,
      "condition": {
        "expression": "required && email",
        "variables": ["data.email"],
        "constraints": {}
      },
      "actions": ["log_violation"],
      "metadata": {
        "createdAt": "2025-08-20T23:50:46.701Z",
        "updatedAt": "2025-08-20T23:50:46.701Z",
        "version": "1.0.0",
        "tags": ["email", "required", "sample"]
      }
    },
    {
      "id": "8d989667-6eb7-40ac-81b0-34902cf5070f",
      "name": "API Response Time",
      "description": "Ensures API responses are within acceptable time limits",
      "category": "api_contract",
      "severity": "minor",
      "enabled": true,
      "condition": {
        "expression": "timeout",
        "variables": ["data.response.time"],
        "constraints": {"maxMs": 1000}
      },
      "actions": ["log_violation", "metric_increment"],
      "metadata": {
        "createdAt": "2025-08-20T23:50:46.701Z",
        "updatedAt": "2025-08-20T23:50:46.701Z",
        "version": "1.0.0",
        "tags": ["performance", "api", "sample"]
      }
    }
]
```

#### 3. 検証実行

```text
# 基本検証の実行
ae-framework conformance verify --input data.json --rules rules.json

# 出力ファイル指定（JSON）
ae-framework conformance verify --input data.json --rules rules.json \
  --context-file context.json --format json --output artifacts/conformance/conformance-results.json
```

#### 4. メトリクス確認

```text
# システムメトリクス表示
ae-framework conformance metrics

# 詳細メトリクス（JSON出力）
ae-framework conformance metrics --format json --export metrics.json
```

### プログラマティック使用

※ 以下のAPI例はリポジトリ内の `src/` を直接参照する場合のみ有効です（npm公開版では未提供）。import パスは利用環境に合わせて調整してください。

#### 基本的なAPI使用

```text
import { ConformanceVerificationEngine } from '<repo>/src/conformance/verification-engine.js';
import { DataValidationMonitor } from '<repo>/src/conformance/monitors/data-validation-monitor.js';

// 検証エンジンの初期化
const engine = new ConformanceVerificationEngine({
  enabled: true,
  mode: 'permissive',
  sampling: { enabled: false, rate: 1.0, strategy: 'random' },
  performance: {
    timeoutMs: 5000,
    maxConcurrentChecks: 10,
    cacheResults: true,
    cacheTtlMs: 300000
  },
  reporting: { destinations: ['console'], batchSize: 100, flushIntervalMs: 30000 },
  alerting: { enabled: false, thresholds: {}, channels: [] },
  rules: []
});

// データ検証モニターの追加
const dataMonitor = new DataValidationMonitor();
engine.addMonitor(dataMonitor);

// 検証エンジンの開始
await engine.start();

// 違反ハンドラーの設定
engine.on('violation_detected', (violation) => {
  console.log(`Violation detected: ${violation.message}`);
  // 自動修正やアラート送信などの処理
});

// 規則の実行
const context = {
  timestamp: new Date().toISOString(),
  executionId: '550e8400-e29b-41d4-a716-446655440000',
  environment: 'development',
  metadata: {
    source: 'api-endpoint',
    data: { username: 'test', email: 'test@example.com' }
  }
};

const result = await engine.verify({ username: 'test', email: 'test@example.com' }, context);
```

#### 高度な設定

```text
import { ConformanceVerificationEngine } from '<repo>/src/conformance/verification-engine.js';
import { APIContractMonitor } from '<repo>/src/conformance/monitors/api-contract-monitor.js';

// エンジン設定（現行実装の構造）
const engine = new ConformanceVerificationEngine({
  enabled: true,
  mode: 'permissive',
  sampling: { enabled: false, rate: 1.0, strategy: 'random' },
  performance: {
    timeoutMs: 30000,
    maxConcurrentChecks: 10,
    cacheResults: true,
    cacheTtlMs: 300000
  },
  reporting: {
    destinations: ['console'],
    batchSize: 100,
    flushIntervalMs: 30000
  },
  alerting: { enabled: false, thresholds: {}, channels: [] }
});

// API契約監視の設定（現行実装ではオプションなし）
const apiMonitor = new APIContractMonitor();
engine.addMonitor(apiMonitor);
```

### 監視とメトリクス

#### 利用可能なメトリクス

1. **実行メトリクス**
   - 規則実行回数
   - 成功/失敗率
   - 平均実行時間
   - 並行実行統計

2. **違反メトリクス**
   - 違反検出数
   - 重要度別分布
   - パターン分析結果
   - トレンド分析

3. **パフォーマンスメトリクス**
   - レスポンス時間（`ConformanceMetrics` に集約）
   - モニターによっては per-check の補助フィールドとして以下を持つ場合があります:
     - CPU使用率
     - メモリ使用量
     - ネットワーク I/O

#### メトリクス取得例

```text
// リアルタイムメトリクス
engine.on('metrics_collected', (metrics) => {
  console.log('Counts:', metrics.counts);
  console.log('Performance:', metrics.performance);
  console.log('Top violations:', metrics.topViolations);
});

// 定期メトリクス取得
setInterval(() => {
  const metrics = engine.getMetrics();
  // メトリクスの保存や可視化処理
}, 60000);
```

### CEGIS連携

Runtime Conformance Systemは違反検出結果を failure artifact に落とし込み、CEGIS（Phase 2.1）の `fix` フローへ引き渡す運用を想定します。現行実装では自動連携クラスは提供されていないため、CLIまたは独自連携で対応します。

#### 自動修正フロー

```text
# 例: 違反情報を failure artifact に整形して fix へ渡す
ae-framework fix create-artifact \
  --type contract \
  --message "Conformance violation" \
  --file src/app.ts \
  --line 42 \
  --output failure.json

ae-framework fix apply --input failure.json --output .ae/auto-fix --dry-run
```

### CLI コマンドリファレンス

#### `ae-framework conformance verify`
システム適合性の検証を実行

```text
ae-framework conformance verify [options]

Options:
  --input <file>          入力データ(JSON)ファイル（必須）
  --rules <file>          規則定義ファイル
  --output <file>         出力ファイル（default: artifacts/conformance/conformance-results.json）
  --rule-ids <ids>         実行する規則ID（カンマ区切り）
  --skip-categories <cats> スキップするカテゴリ（カンマ区切り）
  --context-file <file>   ランタイムコンテキスト(JSON)
  --format <format>       出力形式 (json|markdown)
  --verbose               詳細出力
```

#### `ae-framework conformance rules`
規則の管理

```text
ae-framework conformance rules [options]

Options:
  --list                  規則一覧の表示
  --category <category>   カテゴリでフィルタ
  --add <file>            規則ファイルの追加
  --remove <id>           規則の削除
  --export <file>         規則のエクスポート
  --import <file>         規則のインポート
```

#### `ae-framework conformance config`
設定管理

```text
ae-framework conformance config [options]

Options:
  --show                  現在の設定表示
  --update <file>         設定の更新(JSON)
  --set <key=value>       設定値の更新
  --export <file>         設定のエクスポート
  --reset                 デフォルト設定へ戻す
```

#### `ae-framework conformance metrics`
メトリクス表示

```text
ae-framework conformance metrics [options]

Options:
  --format <format>       出力形式 (table|json)
  --export <file>         出力ファイル
  --reset                 メトリクスのリセット
```

#### `ae-framework conformance status`
システム状態確認

```text
ae-framework conformance status [options]

Options:
  --monitors              モニター情報を表示
  --handlers              違反ハンドラ情報を表示
```

#### `ae-framework conformance sample`
サンプルファイル生成

```text
ae-framework conformance sample [options]

Options:
  --rules <file>          規則サンプル生成（出力ファイル指定）
  --config <file>         設定サンプル生成（出力ファイル指定）
  --data <file>           入力データサンプル生成
  --context <file>        ランタイムコンテキスト生成
```

### 実践的な使用例

#### Webアプリケーション監視

```text
// Express.js アプリケーションでの使用例
import express from 'express';
import { ConformanceVerificationEngine } from '<repo>/src/conformance/verification-engine.js';
import { APIContractMonitor } from '<repo>/src/conformance/monitors/api-contract-monitor.js';

const app = express();
const engine = new ConformanceVerificationEngine({
  enabled: true,
  mode: 'permissive',
  sampling: { enabled: false, rate: 1.0, strategy: 'random' },
  performance: { timeoutMs: 5000, maxConcurrentChecks: 10, cacheResults: true, cacheTtlMs: 300000 },
  reporting: { destinations: ['console'], batchSize: 100, flushIntervalMs: 30000 },
  alerting: { enabled: false, thresholds: {}, channels: [] },
  rules: []
});

// API監視の設定
engine.addMonitor(new APIContractMonitor());
await engine.start();

// ミドルウェアとして統合
app.use(async (req, res, next) => {
  const context = {
    timestamp: new Date().toISOString(),
    executionId: '550e8400-e29b-41d4-a716-446655440002',
    environment: 'development',
    metadata: {
      source: `${req.method} ${req.path}`,
      request: { method: req.method, path: req.path, headers: req.headers },
      data: req.body
    }
  };

  // リクエスト検証
  const apiCall = {
    method: req.method,
    url: req.originalUrl ?? req.url,
    path: req.path,
    headers: req.headers as Record<string, string>,
    body: req.body,
    timestamp: new Date().toISOString()
  };
  const result = await engine.verify(apiCall, context);
  if (result.violations.length > 0) {
    return res.status(400).json({ error: 'Conformance violation', violations: result.violations });
  }

  next();
});
```

#### データパイプライン監視

```text
// データ処理パイプラインでの使用例
import { ConformanceVerificationEngine } from '<repo>/src/conformance/verification-engine.js';
import { DataValidationMonitor } from '<repo>/src/conformance/monitors/data-validation-monitor.js';

const engine = new ConformanceVerificationEngine({
  enabled: true,
  mode: 'permissive',
  sampling: { enabled: false, rate: 1.0, strategy: 'random' },
  performance: { timeoutMs: 5000, maxConcurrentChecks: 10, cacheResults: true, cacheTtlMs: 300000 },
  reporting: { destinations: ['console'], batchSize: 100, flushIntervalMs: 30000 },
  alerting: { enabled: false, thresholds: {}, channels: [] },
  rules: []
});

engine.addMonitor(new DataValidationMonitor());
await engine.start();

// データ処理関数
async function processData(data: unknown[]) {
  for (const record of data) {
    const context = {
      timestamp: new Date().toISOString(),
      executionId: '550e8400-e29b-41d4-a716-446655440001',
      environment: 'development',
      metadata: {
        source: 'data-pipeline',
        data: record
      }
    };

    // データ適合性検証
    const validation = await engine.verify(record, context);
    
    if (validation.violations.length > 0) {
      console.log(`Data validation failed: ${validation.violations.length}`);
      
      // 不正データの隔離
      await quarantineData(record, validation.violations);
      continue;
    }

    // 正常データの処理
    await processRecord(record);
  }
}

await engine.stop();
```

### トラブルシューティング

#### よくある問題と解決方法

##### 1. パフォーマンス問題
```text
# サンプリング率を下げる（設定更新）
ae-framework conformance config --set sampling.enabled=true
ae-framework conformance config --set sampling.rate=0.05

# 並行実行数を調整
ae-framework conformance config --set performance.maxConcurrentChecks=5
```

##### 2. メモリ使用量の増加
```text
# キャッシュの無効化/TTL短縮
ae-framework conformance config --set performance.cacheResults=false
ae-framework conformance config --set performance.cacheTtlMs=60000
```

##### 3. 規則実行の失敗
```text
# 規則の一覧表示
ae-framework conformance rules --list

# 詳細出力での実行
ae-framework conformance verify --input data.json --rules rules.json --verbose
```

### 最適化のガイドライン

#### パフォーマンス最適化

1. **適切なサンプリング率の設定**
   - 開発環境: 0.1-0.2 (10-20%)
   - ステージング環境: 0.05-0.1 (5-10%)
   - 本番環境: 0.01-0.05 (1-5%)

2. **キャッシュ戦略**
   - 頻繁に実行される規則のキャッシュ
   - TTL（Time To Live）の適切な設定
   - メモリ使用量の監視

3. **並行実行の調整**
   - CPUコア数に基づく並行数設定
   - I/O集約的規則の識別と最適化

#### スケーラビリティ

1. **水平スケーリング**
   - 複数インスタンスでの負荷分散
   - メトリクス集約システムの構築

2. **垂直スケーリング**
   - メモリとCPUリソースの適切な割り当て
   - JVM調整（Node.jsの場合）

### セキュリティ考慮事項

1. **機密データの保護**
   - ログとメトリクスでの機密情報のマスキング
   - 規則定義での機密データの除外

2. **アクセス制御**
   - CLI実行権限の制限
   - 設定ファイルへのアクセス管理

3. **監査ログ**
   - 全操作のログ記録
   - 規則変更の追跡

### 次のステップ

Phase 2.2の実装が完了したら、次のフェーズに進めます：

- **Phase 2.3**: [Integration Testing](./PHASE-2-3-INTEGRATION-TESTING.md) - 統合テストとエンドツーエンドテスト
- **Phase 2.1との統合**: [CEGIS Auto-Fix System](../architecture/CEGIS-DESIGN.md) との連携強化

### 関連ドキュメント

- [CEGIS Design Document](../architecture/CEGIS-DESIGN.md)
- [Runtime Conformance Architecture](../architecture/RUNTIME-CONFORMANCE-DESIGN.md)
- [CLI Commands Reference](../reference/CLI-COMMANDS-REFERENCE.md)
- [TDD Framework Architecture](../architecture/TDD-FRAMEWORK-ARCHITECTURE.md)

---

**Phase 2.2 Runtime Conformance System** - リアルタイム品質保証による堅牢なシステム構築 🛡️
