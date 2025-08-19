# Phase 2.2: Runtime Conformance Verification System

> リアルタイムでアプリケーションの適合性を監視・検証するシステム

## 概要

Phase 2.2では、アプリケーションが実行時に定義された仕様や品質基準に適合しているかをリアルタイムで監視・検証するシステムを提供します。このシステムは、CEGIS自動修復システム（Phase 2.1）と連携し、違反を検出した際の自動修正フローを実現します。

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

```bash
# ae-frameworkのインストール
npm install ae-framework

# CLI確認
ae-framework conformance --help
```

### 設定ファイル作成

```bash
# サンプル設定の生成
ae-framework conformance config --create-sample

# 設定ファイルの編集
# conformance-config.json が生成されます
```

## 基本使用方法

### 1. 検証システムの初期化

```bash
# システム状態確認
ae-framework conformance status

# サンプル規則の作成
ae-framework conformance sample --rules --output rules.json
```

### 2. 規則定義

規則定義ファイル（JSON形式）の例：

```json
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

```bash
# 基本検証の実行
ae-framework conformance verify --rules rules.json

# メトリクス付き検証
ae-framework conformance verify --rules rules.json --collect-metrics

# 出力ディレクトリ指定
ae-framework conformance verify --rules rules.json --output-dir ./results
```

### 4. メトリクス確認

```bash
# システムメトリクス表示
ae-framework conformance metrics

# 詳細メトリクス（JSON出力）
ae-framework conformance metrics --format json --output metrics.json
```

## プログラマティック使用

### 基本的なAPI使用

```typescript
import { VerificationEngine } from 'ae-framework/conformance';
import { DataValidationMonitor } from 'ae-framework/conformance/monitors';

// 検証エンジンの初期化
const engine = new VerificationEngine({
  samplingRate: 0.1,
  cacheEnabled: true,
  performanceOptimization: true,
  concurrentExecution: true
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

const result = await engine.executeRule(rule, context);
```

### 高度な設定

```typescript
import { 
  VerificationEngine, 
  RuleEngine, 
  APIContractMonitor 
} from 'ae-framework/conformance';

// 高度なルールエンジン設定
const ruleEngine = new RuleEngine({
  executionTimeout: 30000,
  maxConcurrentRules: 10,
  patternAnalysis: {
    enabled: true,
    windowSize: 100,
    threshold: 0.8
  },
  riskAssessment: {
    enabled: true,
    factors: ['frequency', 'severity', 'impact']
  }
});

// API契約監視の設定
const apiMonitor = new APIContractMonitor({
  endpoints: ['/api/users', '/api/orders'],
  validateHeaders: true,
  validatePayload: true,
  rateLimitChecks: true
});

// 検証エンジンに統合
const engine = new VerificationEngine({
  ruleEngine,
  monitors: [apiMonitor],
  realTimeMetrics: true,
  eventDriven: true
});
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

```typescript
// リアルタイムメトリクス
engine.on('metrics_updated', (metrics) => {
  console.log('Execution metrics:', metrics.execution);
  console.log('Violation metrics:', metrics.violations);
  console.log('Performance metrics:', metrics.performance);
});

// 定期メトリクス取得
setInterval(async () => {
  const metrics = await engine.getMetrics();
  // メトリクスの保存や可視化処理
}, 60000);
```

## CEGIS連携

Runtime Conformance SystemはCEGIS自動修復システム（Phase 2.1）と連携し、違反検出時の自動修正を実現します。

### 自動修正フロー

```typescript
// CEGIS連携の設定
import { CEGISAutoFixer } from 'ae-framework/cegis';

const autoFixer = new CEGISAutoFixer();

engine.on('violation_detected', async (violation) => {
  console.log(`Violation detected: ${violation.type}`);
  
  // CEGIS修正の試行
  const fixResult = await autoFixer.attemptFix(violation);
  
  if (fixResult.success) {
    console.log('Auto-fix applied successfully');
    
    // 修正後の再検証
    const revalidationResult = await engine.revalidate(violation.ruleId);
    console.log('Revalidation result:', revalidationResult);
  } else {
    console.log('Auto-fix failed, manual intervention required');
    // 手動対応のアラート送信
  }
});
```

## CLI コマンドリファレンス

### `ae-framework conformance verify`
システム適合性の検証を実行

```bash
ae-framework conformance verify [options]

Options:
  --rules <file>           規則定義ファイル
  --config <file>         設定ファイル
  --output-dir <dir>      出力ディレクトリ
  --collect-metrics       メトリクス収集を有効化
  --sample-rate <rate>    サンプリング率 (0.0-1.0)
  --timeout <ms>          実行タイムアウト
```

### `ae-framework conformance rules`
規則の管理

```bash
ae-framework conformance rules [options]

Options:
  --list                  規則一覧の表示
  --validate <file>       規則ファイルの検証
  --enable <id>           規則の有効化
  --disable <id>          規則の無効化
  --info <id>             規則の詳細表示
```

### `ae-framework conformance config`
設定管理

```bash
ae-framework conformance config [options]

Options:
  --show                  現在の設定表示
  --validate              設定の検証
  --create-sample         サンプル設定の作成
  --export <file>         設定のエクスポート
  --import <file>         設定のインポート
```

### `ae-framework conformance metrics`
メトリクス表示

```bash
ae-framework conformance metrics [options]

Options:
  --format <format>       出力形式 (table|json)
  --output <file>         出力ファイル
  --live                  リアルタイム監視
  --refresh <seconds>     更新間隔
  --filter <type>         メトリクスタイプのフィルター
```

### `ae-framework conformance status`
システム状態確認

```bash
ae-framework conformance status [options]

Options:
  --detailed              詳細状態表示
  --json                  JSON形式出力
  --check-health          ヘルスチェック実行
```

### `ae-framework conformance sample`
サンプルファイル生成

```bash
ae-framework conformance sample [options]

Options:
  --rules                 規則サンプル生成
  --config                設定サンプル生成
  --output <file>         出力ファイル指定
  --template <type>       テンプレートタイプ
```

## 実践的な使用例

### Webアプリケーション監視

```typescript
// Express.js アプリケーションでの使用例
import express from 'express';
import { VerificationEngine, APIContractMonitor } from 'ae-framework/conformance';

const app = express();
const engine = new VerificationEngine({
  realTimeMetrics: true,
  eventDriven: true
});

// API監視の設定
const apiMonitor = new APIContractMonitor({
  validateResponses: true,
  checkRateLimits: true,
  monitorPerformance: true
});

engine.addMonitor(apiMonitor);
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
  const validationResult = await engine.validateRequest(context);
  
  if (!validationResult.valid) {
    return res.status(400).json({ error: 'Validation failed' });
  }

  next();
});
```

### データパイプライン監視

```typescript
// データ処理パイプラインでの使用例
import { VerificationEngine, DataValidationMonitor } from 'ae-framework/conformance';

const engine = new VerificationEngine();
const dataMonitor = new DataValidationMonitor({
  schemaValidation: true,
  dataQualityChecks: true,
  anomalyDetection: true
});

engine.addMonitor(dataMonitor);

// データ処理関数
async function processData(data: unknown[]) {
  for (const record of data) {
    const context = {
      timestamp: new Date().toISOString(),
      source: 'data-pipeline',
      data: record
    };

    // データ適合性検証
    const validation = await engine.validateData(context);
    
    if (!validation.valid) {
      console.log(`Data validation failed: ${validation.violations}`);
      
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
```bash
# サンプリング率を下げる
ae-framework conformance verify --sample-rate 0.05

# 並行実行数を調整
ae-framework conformance config --set maxConcurrentRules=5
```

#### 2. メモリ使用量の増加
```bash
# キャッシュサイズを制限
ae-framework conformance config --set cacheMaxSize=1000

# ガベージコレクションの強制実行
ae-framework conformance config --set forceGC=true
```

#### 3. 規則実行の失敗
```bash
# 規則の妥当性チェック
ae-framework conformance rules --validate rules.json

# デバッグモードでの実行
DEBUG=conformance:* ae-framework conformance verify --rules rules.json
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