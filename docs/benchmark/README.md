---
docRole: narrative
lastVerified: '2026-03-12'
---

# AE Framework Benchmark Integration

## 🌍 Language / 言語
[English](#english) | [日本語](#japanese)

---

## English

### Overview

The AE Framework Benchmark Integration provides comprehensive performance evaluation against the [Req2Run-Benchmark](https://github.com/itdojp/req2run-benchmark) dataset. This system measures the framework's ability to transform requirements into executable applications across multiple dimensions.

### Features

- **Comprehensive Evaluation**: Tests functional coverage, performance, code quality, and security
- **35+ Problems**: Covers 16+ categories from web APIs to distributed systems
- **4 Difficulty Levels**: Basic → Intermediate → Advanced → Expert
- **Automated Scoring**: Weighted metrics with customizable thresholds
- **Parallel Execution**: Configurable concurrency for faster benchmarking
- **Rich Reporting**: JSON, HTML, Markdown outputs with dashboard visualization

### Quick Start

#### Installation

The benchmark system is integrated into AE Framework:

```bash no-doctest
# Install AE Framework with benchmark capabilities
pnpm add ae-framework

# Or build from source
pnpm run build:cli
```

#### Basic Usage

```bash no-doctest
# List available benchmark problems
ae-benchmark list

# Run basic difficulty problems
ae-benchmark run --difficulty basic

# Run specific problems
ae-benchmark run --problems web-api-basic-001 cli-tool-basic-001

# Generate configuration template
ae-benchmark init --output configs/benchmark-config.json

# Run with custom configuration
ae-benchmark run --config configs/benchmark-config.json
```

#### Scripts

```bash no-doctest
# Quick benchmark execution
pnpm run benchmark:basic

# CI-optimized run
pnpm run benchmark:ci

# List problems
pnpm run benchmark:list

# Generate config
pnpm run benchmark:init
```

#### Environment Setup

For repository location and CI preparation of the Req2Run benchmark, see `req2run-environment-setup.md`.

### Configuration

#### Default Configuration

The system provides sensible defaults for different use cases:

```typescript no-doctest
import { 
  DEFAULT_BENCHMARK_CONFIG,
  getConfigForDifficulty,
  getCIConfig 
} from './src/benchmark/req2run/config/default.js';

// Basic configuration
const basicConfig = getConfigForDifficulty(DifficultyLevel.BASIC);

// CI configuration
const ciConfig = getCIConfig();
```

#### Custom Configuration

Create a `configs/benchmark-config.json` file:

```json no-doctest
{
  "problems": [
    {
      "id": "web-api-basic-001",
      "enabled": true,
      "timeoutMs": 300000,
      "retries": 1,
      "category": "web-api",
      "difficulty": "basic"
    }
  ],
  "execution": {
    "parallel": false,
    "maxConcurrency": 2,
    "resourceLimits": {
      "maxMemoryMB": 4096,
      "maxCpuPercent": 80,
      "maxExecutionTimeMs": 3600000
    }
  },
  "evaluation": {
    "weights": {
      "functional": 0.35,
      "performance": 0.15,
      "quality": 0.20,
      "security": 0.15,
      "testing": 0.15
    },
    "thresholds": {
      "minOverallScore": 60,
      "minFunctionalCoverage": 70,
      "maxResponseTime": 2000
    }
  }
}
```

### Architecture

#### AE Framework Pipeline Integration

The benchmark system integrates with all 6 AE Framework phases:

```typescript no-doctest
class Req2RunBenchmarkRunner {
  async runBenchmark(problemId: string): Promise<BenchmarkResult> {
    // Phase 1: Intent Analysis
    const intent = await this.intentAgent.analyze(spec);
    
    // Phase 2: Requirements Processing
    const requirements = await this.nlpAgent.process(intent);
    
    // Phase 3: User Stories Generation
    const userStories = await this.storiesAgent.generate(requirements);
    
    // Phase 4: Validation
    const validation = await this.validationAgent.verify(userStories);
    
    // Phase 5: Domain Modeling
    const domainModel = await this.domainAgent.model(validation);
    
    // Phase 6: UI/UX Generation
    const application = await this.uiAgent.generate(domainModel);
    
    return await this.evaluateResult(application, spec);
  }
}
```

#### Metrics Collection

The system collects comprehensive metrics:

```typescript no-doctest
interface BenchmarkMetrics {
  overallScore: number;              // 0-100 total score
  functionalCoverage: number;        // % of requirements met
  testPassRate: number;              // % of tests passing
  performance: PerformanceMetrics;   // Response time, throughput
  codeQuality: QualityMetrics;       // Complexity, maintainability
  security: SecurityMetrics;         // Vulnerabilities, compliance
  timeToCompletion: number;          // Total execution time
  resourceUsage: ResourceMetrics;    // Memory, CPU usage
  phaseMetrics: PhaseMetrics[];      // Per-phase performance
}
```

### Problem Categories

The benchmark covers diverse problem types:

- **Web APIs**: REST services, GraphQL endpoints
- **CLI Tools**: Command-line utilities, data processors
- **Data Processing**: ETL pipelines, transformations
- **Cryptography**: Encryption, hashing, digital signatures
- **Network Protocols**: Custom protocols, servers
- **Authentication**: OAuth, JWT, session management
- **Databases**: Schema design, query optimization
- **Machine Learning**: Model training, inference pipelines
- **Distributed Systems**: Microservices, message queues
- **Real-time Systems**: WebSocket, streaming data

### Scoring Algorithm

The weighted scoring system considers multiple factors:

```
Overall Score = (
  Functional Coverage × 0.35 +
  Performance Score × 0.15 +
  Code Quality Score × 0.20 +
  Security Score × 0.15 +
  Testing Score × 0.15
) × Penalty Adjustments + Bonuses
```

#### Penalty System
- **Timeout Penalty**: 50% reduction for timeouts
- **Error Penalty**: 30% reduction for runtime errors
- **Quality Penalty**: 20% reduction for quality issues

#### Bonus System
- **Performance Bonus**: +10% for exceptional performance
- **Quality Bonus**: +10% for excellent code quality
- **Security Bonus**: +5% for perfect security compliance

### Reporting and Visualization

#### Available Formats
- **JSON**: Machine-readable results for CI/CD
- **HTML**: Rich interactive reports
- **Markdown**: Documentation-friendly summaries
- **CSV**: Spreadsheet analysis

#### Dashboard Features
- Real-time execution monitoring
- Historical trend analysis
- Category performance breakdown
- Resource usage visualization
- Comparison with baseline metrics

### CI/CD Integration

#### GitHub Actions

```yaml no-doctest
name: Benchmark Evaluation
on:
  push:
    branches: [main]
  schedule:
    - cron: '0 2 * * *'  # Daily at 2 AM

jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
      - run: pnpm install --frozen-lockfile
      - run: pnpm run benchmark:ci
      - uses: actions/upload-artifact@v4
        with:
          name: benchmark-results
          path: reports/benchmark/
```

#### Performance Regression Detection

The system automatically detects performance regressions:

```bash no-doctest
# Compare with baseline
ae-benchmark run --baseline ./baseline-results.json

# Set failure thresholds
ae-benchmark run --fail-on-regression 10%
```

### Troubleshooting

#### Common Issues

1. **Timeout Errors**
   ```bash no-doctest
   # Increase timeout for complex problems
   ae-benchmark run --timeout 600000  # 10 minutes
   ```

2. **Memory Limitations**
   ```bash no-doctest
   # Adjust memory limits
   ae-benchmark run --config config-high-memory.json
   ```

3. **コンテナ実行 (Podman/Docker) の問題**
   ```bash no-doctest
   # Podman が起動しているか確認
   podman ps --filter "name=ae-framework"
   # コンテナ隔離 (Podman/Docker) を無効化してデバッグ
   ae-benchmark run --no-docker  # disables container isolation for both Podman and Docker backends
   ```

#### Debug Mode

```bash no-doctest
# Enable verbose logging
DEBUG=ae-framework:benchmark ae-benchmark run

# Save intermediate artifacts
ae-benchmark run --save-artifacts ./debug-artifacts/
```

### Performance Optimization

#### Best Practices

1. **Start with Basic Problems**: Validate setup with simple cases
2. **Use Parallel Execution**: Enable for multiple problems
3. **Resource Monitoring**: Watch memory/CPU usage
4. **Incremental Testing**: Add complexity gradually

#### Resource Management

```typescript no-doctest
// Configure resource limits
const config = {
  execution: {
    resourceLimits: {
      maxMemoryMB: 4096,      // 4GB limit
      maxCpuPercent: 80,      // 80% CPU limit
      maxExecutionTimeMs: 3600000  // 1 hour timeout
    }
  }
};
```

### Contributing

#### Adding New Problems

1. Fork the [req2run-benchmark](https://github.com/itdojp/req2run-benchmark) repository
2. Add problem specification following the schema
3. Update problem registry in AE Framework
4. Submit pull request with test results

#### Extending Evaluation Metrics

```typescript no-doctest
// Custom metric evaluator
class CustomEvaluator implements MetricEvaluator {
  async evaluate(application: any, spec: RequirementSpec): Promise<number> {
    // Custom evaluation logic
    return score;
  }
}
```

---

## 日本語

### 概要

AE Frameworkベンチマーク統合は、[Req2Run-Benchmark](https://github.com/itdojp/req2run-benchmark)データセットに対する包括的な性能評価を提供します。このシステムは、要求仕様から実行可能なアプリケーションへの変換能力を多角的に測定します。

### 特徴

- **包括的評価**: 機能カバレッジ、性能、コード品質、セキュリティをテスト
- **35+問題**: Web APIから分散システムまで16+カテゴリをカバー
- **4難易度レベル**: Basic → Intermediate → Advanced → Expert
- **自動スコアリング**: カスタマイズ可能な閾値を持つ重み付きメトリクス
- **並列実行**: 高速ベンチマークのための設定可能な並行性
- **豊富なレポート**: ダッシュボード可視化付きのJSON、HTML、Markdown出力

### クイックスタート

#### インストール

ベンチマークシステムはAE Frameworkに統合されています：

```bash no-doctest
# ベンチマーク機能付きAE Frameworkをインストール
pnpm add ae-framework

# またはソースからビルド
pnpm run build:cli
```

#### 基本的な使用方法

```bash no-doctest
# 利用可能なベンチマーク問題をリスト
ae-benchmark list

# 基本難易度問題を実行
ae-benchmark run --difficulty basic

# 特定の問題を実行
ae-benchmark run --problems web-api-basic-001 cli-tool-basic-001

# 設定テンプレートを生成
ae-benchmark init --output configs/benchmark-config.json

# カスタム設定で実行
ae-benchmark run --config configs/benchmark-config.json
```

#### NPMスクリプト

```bash no-doctest
# クイックベンチマーク実行
pnpm run benchmark:basic

# CI最適化実行
pnpm run benchmark:ci

# 問題リスト
pnpm run benchmark:list

# 設定生成
pnpm run benchmark:init
```

### 設定

#### デフォルト設定

システムは様々な用途に対応する適切なデフォルトを提供します：

```typescript no-doctest
import { 
  DEFAULT_BENCHMARK_CONFIG,
  getConfigForDifficulty,
  getCIConfig 
} from './src/benchmark/req2run/config/default.js';

// 基本設定
const basicConfig = getConfigForDifficulty(DifficultyLevel.BASIC);

// CI設定
const ciConfig = getCIConfig();
```

#### カスタム設定

`configs/benchmark-config.json`ファイルを作成：

```json no-doctest
{
  "problems": [
    {
      "id": "web-api-basic-001",
      "enabled": true,
      "timeoutMs": 300000,
      "retries": 1,
      "category": "web-api",
      "difficulty": "basic"
    }
  ],
  "execution": {
    "parallel": false,
    "maxConcurrency": 2,
    "resourceLimits": {
      "maxMemoryMB": 4096,
      "maxCpuPercent": 80,
      "maxExecutionTimeMs": 3600000
    }
  }
}
```

### アーキテクチャ

#### AE Frameworkパイプライン統合

ベンチマークシステムはAE Frameworkの全6フェーズと統合されます：

```typescript no-doctest
class Req2RunBenchmarkRunner {
  async runBenchmark(problemId: string): Promise<BenchmarkResult> {
    // フェーズ1: 意図分析
    const intent = await this.intentAgent.analyze(spec);
    
    // フェーズ2: 要求処理
    const requirements = await this.nlpAgent.process(intent);
    
    // フェーズ3: ユーザーストーリー生成
    const userStories = await this.storiesAgent.generate(requirements);
    
    // フェーズ4: 検証
    const validation = await this.validationAgent.verify(userStories);
    
    // フェーズ5: ドメインモデリング
    const domainModel = await this.domainAgent.model(validation);
    
    // フェーズ6: UI/UX生成
    const application = await this.uiAgent.generate(domainModel);
    
    return await this.evaluateResult(application, spec);
  }
}
```

### 問題カテゴリ

ベンチマークは多様な問題タイプをカバーします：

- **Web API**: RESTサービス、GraphQLエンドポイント
- **CLIツール**: コマンドラインユーティリティ、データ処理
- **データ処理**: ETLパイプライン、変換処理
- **暗号化**: 暗号化、ハッシュ化、デジタル署名
- **ネットワークプロトコル**: カスタムプロトコル、サーバー
- **認証**: OAuth、JWT、セッション管理
- **データベース**: スキーマ設計、クエリ最適化
- **機械学習**: モデル訓練、推論パイプライン
- **分散システム**: マイクロサービス、メッセージキュー
- **リアルタイムシステム**: WebSocket、ストリーミングデータ

### スコアリングアルゴリズム

重み付きスコアリングシステムは複数の要因を考慮します：

```
総合スコア = (
  機能カバレッジ × 0.35 +
  性能スコア × 0.15 +
  コード品質スコア × 0.20 +
  セキュリティスコア × 0.15 +
  テストスコア × 0.15
) × ペナルティ調整 + ボーナス
```

### トラブルシューティング

#### よくある問題

1. **タイムアウトエラー**
   ```bash no-doctest
   # 複雑な問題のタイムアウトを増加
   ae-benchmark run --timeout 600000  # 10分
   ```

2. **メモリ制限**
   ```bash no-doctest
   # メモリ制限を調整
   ae-benchmark run --config config-high-memory.json
   ```

#### デバッグモード

```bash no-doctest
# 詳細ログを有効化
DEBUG=ae-framework:benchmark ae-benchmark run

# 中間成果物を保存
ae-benchmark run --save-artifacts ./debug-artifacts/
```

### コントリビューション

#### 新しい問題の追加

1. [req2run-benchmark](https://github.com/itdojp/req2run-benchmark)リポジトリをフォーク
2. スキーマに従って問題仕様を追加
3. AE Frameworkの問題レジストリを更新
4. テスト結果付きのプルリクエストを提出

---

**関連リンク / Related Links:**
- [Req2Run-Benchmark Repository](https://github.com/itdojp/req2run-benchmark)
- [Issue #155: Benchmark Integration](https://github.com/itdojp/ae-framework/issues/155)
- [AE Framework Documentation](../README.md)
