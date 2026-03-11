---
docRole: ssot
lastVerified: 2026-03-11
owner: phase-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Phase 2.2: Runtime Conformance Verification System

> 🌍 Language / 言語: 日本語 | English

---

## English (Overview)

Phase 2.2 provides a real-time system to verify that running applications conform to defined specifications and quality bars. It integrates with Phase 2.1 (CEGIS auto-fix) to enable an automated remediation flow when violations are detected.

Highlights
- Rule-based verification engine (sampling, caching, concurrency)
- Real-time event-driven monitoring with multi-monitor integration
- Metrics collection and comprehensive reports
- Full CLI integration for verification/rules/config/metrics/status

See the Japanese sections for the full architecture and CLI details.

## English (Detailed)

### Goals
- Continuous validation of runtime behavior against specifications (pre/post/invariants)
- Early violation detection → optional auto-remediation via Phase 2.1 (CEGIS)
- Evidence collection for quality gates and PR summaries

### Contract terminology note
- In this document, "runtime contract" means **Design contract (DbC)** such as pre/postconditions and invariants.
- API contract verification with Pact belongs to **API/Integration contract tests** in CI workflows.
- Required/optional report rules are tracked separately as **Artifacts contract**.

### Key Components
- Verification Engine: configurable rules (sampling, cache, concurrency)
- Monitors: data validation, API contract, custom business rules
- Metrics & Reports: a11y/perf/test coverage linkage, JSON/Markdown outputs

### CLI (high level)
```text
ae conformance verify --input data.json --rules rules.json   # run runtime checks
ae conformance rules --list                                  # list/manage rules
ae conformance config --show                                 # show/edit configuration
ae conformance metrics --format table                        # show metrics
ae conformance status                                        # current status
ae conformance sample --rules rules.json --data data.json    # generate samples
ae conformance report --format both                          # aggregate reports
```

### Artifacts
- `artifacts/conformance/conformance-results.json` — verification result (default output)
- `reports/conformance/conformance-summary.{json,md}` — aggregated reports
- PR summary integration when enabled

### Minimal YAML (CI example)
```text
name: Conformance Verify
on: [pull_request]
jobs:
  conformance:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: pnpm install --frozen-lockfile
      - run: pnpm run ae-framework -- conformance sample --rules rules.json --data data.json --context context.json
      - run: pnpm run ae-framework -- conformance verify --input data.json --context-file context.json --rules rules.json --output artifacts/conformance/conformance-results.json
      - uses: actions/upload-artifact@v4
        if: always()
        with: { name: conformance, path: artifacts/conformance/** }
```

### Integration
- With Phase 2.1 (CEGIS): violations → counterexamples → repair candidates
- With Phase 6: surface UI-related metrics and guard budgets

> リアルタイムでアプリケーションの適合性を監視・検証するシステム

## 概要

Phase 2.2では、アプリケーションが実行時に定義された仕様や品質基準に適合しているかをリアルタイムで監視・検証するシステムを提供します。このシステムは、CEGIS自動修復システム（Phase 2.1）と連携し、違反を検出した際の自動修正フローを実現します。

### 用語注記（contract）
- 本ドキュメントの「ランタイム契約」は **Design contract（DbC）**（pre/post/invariant）を指します。
- Pact などの API 契約検証は **API/Integration contract test** として CI で扱います。
- 成果物の必須/任意ルールは **Artifacts contract** として別管理します。

## 主要機能

### 1. 規則ベース検証エンジン
- **設定可能な規則実行**: サンプリング率、キャッシュ、並行実行制御
- **パターン分析**: 違反パターンの自動検出
- **リスク評価**: 重要度に基づく優先度付け
- **パフォーマンス最適化**: タイムアウト処理と並行実行

### 2. リアルタイム監視システム
- **イベント駆動アーキテクチャ**: 非同期での違反検出・通知
- **複数モニター統合**: データ検証、API契約監視の統合管理
- **メトリクス収集**: パフォーマンス指標と品質メトリクスの収集
- **包括的レポート**: 違反状況とシステム状態の詳細レポート

### 3. 特殊化されたモニター
- **データ検証モニター**: Zodスキーマによる型安全性と検証
- **API契約モニター**: HTTP契約、レート制限、タイムアウト監視
- **カスタムモニター**: 独自の業務ルール監視

### 4. CLI統合
- **包括的コマンド**: verify、rules、config、metrics、status、sample
- **ワークフロー管理**: 検証から設定まで完全な管理機能

## アーキテクチャ

### システム構成

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

### 技術スタック
- **TypeScript**: 型安全性とコード品質
- **Zod**: スキーマ検証とデータ型安全性
- **EventEmitter**: 非同期イベント処理
- **Commander.js**: CLI インターフェース
- **Vitest**: 包括的テストカバレッジ

## インストールと設定

### 基本セットアップ

```text
# ae-frameworkのインストール
pnpm add ae-framework

# CLI確認
ae-framework conformance --help
```

### 設定ファイル作成

```text
# サンプル設定の生成
ae-framework conformance sample --config conformance-config.json

# 設定ファイルの編集
# conformance-config.json が生成されます
```

## 基本使用方法

### 1. 検証システムの初期化

```text
# システム状態確認
ae-framework conformance status

# サンプル規則の作成
ae-framework conformance sample --rules rules.json
```

### 2. 規則定義

規則定義ファイル（JSON形式）の例：

```text
{
  "rules": [
    {
      "id": "data-validation-rule",
      "name": "Data Validation Rule",
      "description": "Validate user input data",
      "type": "data_validation",
      "enabled": true,
      "severity": "major",
      "category": "validation",
      "configuration": {
        "schema": {
          "type": "object",
          "properties": {
            "username": {"type": "string", "minLength": 3},
            "email": {"type": "string", "format": "email"}
          },
          "required": ["username", "email"]
        }
      },
      "metadata": {
        "tags": ["user", "validation"]
      }
    },
    {
      "id": "api-contract-rule",
      "name": "API Contract Rule", 
      "description": "Validate API responses",
      "type": "api_contract",
      "enabled": true,
      "severity": "critical",
      "category": "api",
      "configuration": {
        "endpoint": "/api/users",
        "method": "GET",
        "expectedStatus": [200, 404],
        "responseSchema": {
          "type": "object",
          "properties": {
            "data": {"type": "array"},
            "total": {"type": "number"}
          }
        }
      }
    }
  ]
}
```

### 3. 検証実行

```text
# 基本検証の実行
ae-framework conformance verify --input data.json --rules rules.json

# 出力ファイル指定（JSON）
ae-framework conformance verify --input data.json --rules rules.json \
  --context-file context.json --format json --output artifacts/conformance/conformance-results.json
```

### 4. メトリクス確認

```text
# システムメトリクス表示
ae-framework conformance metrics

# 詳細メトリクス（JSON出力）
ae-framework conformance metrics --format json --export metrics.json
```

## プログラマティック使用

※ 以下のAPI例はリポジトリ内の `src/` を直接参照する場合のみ有効です（npm公開版では未提供）。import パスは利用環境に合わせて調整してください。

### 基本的なAPI使用

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
  alerting: { enabled: false, thresholds: {}, channels: [] }
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
  source: 'api-endpoint',
  data: { username: 'test', email: 'test@example.com' }
};

const result = await engine.verify({ username: 'test', email: 'test@example.com' }, context);
```

### 高度な設定

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

## 監視とメトリクス

### 利用可能なメトリクス

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
   - CPU使用率
   - メモリ使用量
   - ネットワーク I/O
   - レスポンス時間

### メトリクス取得例

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

## CEGIS連携

Runtime Conformance Systemは違反検出結果を failure artifact に落とし込み、CEGIS（Phase 2.1）の `fix` フローへ引き渡す運用を想定します。現行実装では自動連携クラスは提供されていないため、CLIまたは独自連携で対応します。

### 自動修正フロー

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

## CLI コマンドリファレンス

### `ae-framework conformance verify`
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

### `ae-framework conformance rules`
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

### `ae-framework conformance config`
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

### `ae-framework conformance metrics`
メトリクス表示

```text
ae-framework conformance metrics [options]

Options:
  --format <format>       出力形式 (table|json)
  --export <file>         出力ファイル
  --reset                 メトリクスのリセット
```

### `ae-framework conformance status`
システム状態確認

```text
ae-framework conformance status [options]

Options:
  --monitors              モニター情報を表示
  --handlers              違反ハンドラ情報を表示
```

### `ae-framework conformance sample`
サンプルファイル生成

```text
ae-framework conformance sample [options]

Options:
  --rules <file>          規則サンプル生成（出力ファイル指定）
  --config <file>         設定サンプル生成（出力ファイル指定）
  --data <file>           入力データサンプル生成
  --context <file>        ランタイムコンテキスト生成
```

## 実践的な使用例

### Webアプリケーション監視

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
  alerting: { enabled: false, thresholds: {}, channels: [] }
});

// API監視の設定
engine.addMonitor(new APIContractMonitor());
await engine.start();

// ミドルウェアとして統合
app.use(async (req, res, next) => {
  const context = {
    timestamp: new Date().toISOString(),
    source: `${req.method} ${req.path}`,
    request: { method: req.method, path: req.path, headers: req.headers },
    data: req.body
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

### データパイプライン監視

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
  alerting: { enabled: false, thresholds: {}, channels: [] }
});

engine.addMonitor(new DataValidationMonitor());

// データ処理関数
async function processData(data: unknown[]) {
  for (const record of data) {
    const context = {
      timestamp: new Date().toISOString(),
      source: 'data-pipeline',
      data: record
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
```

## トラブルシューティング

### よくある問題と解決方法

#### 1. パフォーマンス問題
```text
# サンプリング率を下げる（設定更新）
ae-framework conformance config --set sampling.enabled=true
ae-framework conformance config --set sampling.rate=0.05

# 並行実行数を調整
ae-framework conformance config --set performance.maxConcurrentChecks=5
```

#### 2. メモリ使用量の増加
```text
# キャッシュの無効化/TTL短縮
ae-framework conformance config --set performance.cacheResults=false
ae-framework conformance config --set performance.cacheTtlMs=60000
```

#### 3. 規則実行の失敗
```text
# 規則の一覧表示
ae-framework conformance rules --list

# 詳細出力での実行
ae-framework conformance verify --input data.json --rules rules.json --verbose
```

## 最適化のガイドライン

### パフォーマンス最適化

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

### スケーラビリティ

1. **水平スケーリング**
   - 複数インスタンスでの負荷分散
   - メトリクス集約システムの構築

2. **垂直スケーリング**
   - メモリとCPUリソースの適切な割り当て
   - JVM調整（Node.jsの場合）

## セキュリティ考慮事項

1. **機密データの保護**
   - ログとメトリクスでの機密情報のマスキング
   - 規則定義での機密データの除外

2. **アクセス制御**
   - CLI実行権限の制限
   - 設定ファイルへのアクセス管理

3. **監査ログ**
   - 全操作のログ記録
   - 規則変更の追跡

## 次のステップ

Phase 2.2の実装が完了したら、次のフェーズに進めます：

- **Phase 2.3**: [Integration Testing](./PHASE-2-3-INTEGRATION-TESTING.md) - 統合テストとエンドツーエンドテスト
- **Phase 2.1との統合**: [CEGIS Auto-Fix System](../architecture/CEGIS-DESIGN.md) との連携強化

## 関連ドキュメント

- [CEGIS Design Document](../architecture/CEGIS-DESIGN.md)
- [Runtime Conformance Architecture](../architecture/RUNTIME-CONFORMANCE-DESIGN.md)
- [CLI Commands Reference](../reference/CLI-COMMANDS-REFERENCE.md)
- [TDD Framework Architecture](../architecture/TDD-FRAMEWORK-ARCHITECTURE.md)

---

**Phase 2.2 Runtime Conformance System** - リアルタイム品質保証による堅牢なシステム構築 🛡️
