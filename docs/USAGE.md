# AE Framework 使い方ガイド

ae-frameworkの全6フェーズエージェントの使用方法と実践例を詳しく説明します。

## 🎯 概要

ae-frameworkは以下の6フェーズでソフトウェア開発を支援します：

1. **Intent Agent** (Phase 1): 要件定義・分析
2. **Formal Agent** (Phase 2): 形式仕様・設計
3. **Test Agent** (Phase 3): テスト設計・生成
   - **Phase 3.1**: Sequential推論エンジン・依存関係分析
   - **Phase 3.2**: E2E自動化・視覚回帰テスト・AI選択 ✨ **NEW**
   - **Phase 3.3**: 統合最適化・パフォーマンス監視 ✨ **NEW**
4. **Code Agent** (Phase 4): コード実装・生成
5. **Verify Agent** (Phase 5): 品質検証・監査
6. **Operate Agent** (Phase 6): 運用・監視

## 🔄 基本的な開発フロー

### 完全なプロジェクト例

新しいWebアプリケーションを開発する場合のフロー：

```bash
# 1. 要件分析
npm run intent-agent

# 2. 形式仕様生成
npm run formal-agent

# 3. テスト生成 (Phase 3.1 & 3.2)
npm run mcp:test

# 3a. E2E自動テスト生成 (Phase 3.2)
npm run e2e:demo

# 3b. 視覚回帰テスト (Phase 3.2)  
npm run visual:demo

# 3c. インテリジェントテスト選択 (Phase 3.2) ✨ **NEW**
npm test -- tests/testing/intelligent-test-selection.test.ts

# 3d. 統合最適化システム (Phase 3.3) ✨ **NEW**
npm test -- tests/optimization/system-integration.test.ts

# 4. コード生成
npm run mcp:code

# 5. 品質検証
npm run verify:all

# 6. デプロイ・運用
npm run operate:server
```

---

## 📝 Phase 1: Intent Agent（要件定義）

### 基本的な使い方

#### MCPサーバーとして使用
```bash
npm run intent-agent
```

#### 直接実行（開発・テスト用）
```typescript
import { IntentAgent } from './src/agents/intent-agent.js';

const agent = new IntentAgent();

const request = {
  sources: [
    {
      type: 'text',
      content: `
        ユーザーはログインできる必要がある。
        商品を検索して購入できる。
        管理者は在庫を管理できる。
      `
    }
  ],
  context: {
    domain: 'e-commerce',
    constraints: [
      {
        type: 'technical',
        description: 'レスポンス時間は1秒以内',
        impact: 'high'
      }
    ]
  }
};

const result = await agent.analyzeIntent(request);
console.log('生成された要件:', result.requirements);
console.log('ユーザーストーリー:', result.userStories);
```

### 主要機能

#### 1. 自然言語からの要件抽出
```typescript
const requirements = await agent.extractFromNaturalLanguage(`
  システムは以下の機能を提供する必要がある：
  - ユーザー認証（JWT方式）
  - 商品検索（フィルタリング機能付き）
  - ショッピングカート
  - 決済処理（Stripe連携）
`);
```

#### 2. 曖昧性の検出
```typescript
const ambiguities = await agent.detectAmbiguities([
  {
    type: 'text',
    content: 'システムは高速で安全である必要がある'
  }
]);
// → 「高速」「安全」の具体的定義が必要と判定
```

#### 3. ドメインモデルの生成
```typescript
const domainModel = await agent.buildDomainModelFromRequirements(
  requirements,
  { domain: 'e-commerce' }
);
console.log('エンティティ:', domainModel.entities);
console.log('関係性:', domainModel.relationships);
```

---

## 🔬 Phase 2: Formal Agent（形式仕様）

### 基本的な使い方

#### MCPサーバーとして使用
```bash
npm run formal-agent
```

#### TLA+仕様の生成
```bash
npm run generate-tla
```

#### 仕様の検証
```bash
npm run validate-specs
```

#### モデルチェック
```bash
npm run model-check
```

### 実践例

#### 1. TLA+仕様の自動生成
```typescript
import { FormalAgent } from './src/agents/formal-agent.js';

const agent = new FormalAgent();

const spec = await agent.generateTLAPlus(`
  ショッピングカートシステム:
  - 商品をカートに追加できる
  - カートから商品を削除できる  
  - カートの合計金額を計算する
  - 同時アクセス時の整合性を保つ
`);

console.log('TLA+仕様:', spec.content);
```

#### 2. 状態遷移図の生成
```typescript
const stateDiagram = await agent.generateStateDiagram([
  'idle', 'loading', 'success', 'error'
], [
  { from: 'idle', to: 'loading', trigger: 'submit' },
  { from: 'loading', to: 'success', trigger: 'response_ok' },
  { from: 'loading', to: 'error', trigger: 'response_error' }
]);
```

#### 3. 形式検証の実行
```typescript
const verification = await agent.verifySpecification(spec, {
  checkDeadlock: true,
  checkLiveness: true,
  maxStates: 1000000
});

if (!verification.valid) {
  console.log('検証エラー:', verification.errors);
}
```

---

## 🧪 Phase 3: Test Agent（テスト生成）

Phase 3は2つのサブフェーズから構成されます：

### 📋 Phase 3.1: Sequential推論エンジン・依存関係分析

高度な推論エンジンによる複雑問題解決とコンポーネント間依存関係の解析

#### 基本的な使い方
```bash
# Sequential推論エンジンデモ
npm run analyze:demo

# 依存関係分析
npm run dependency:analyze
```

### 🎭 Phase 3.2: E2E自動化・視覚回帰テスト ✨ **NEW**

AI駆動の包括的テスト自動化システム

#### 基本的な使い方

##### MCPサーバーとして使用
```bash
npm run mcp:test
```

##### E2Eテスト自動生成
```bash
npm run e2e:demo
npm run test:playwright
```

##### 視覚回帰テスト
```bash
npm run visual:demo
npm run test:visual
```

##### 高速テスト実行（CI最適化版）
```bash
npm run test:fast
npm run test:phase3.2:core
```

#### 直接エージェント実行
```bash
npm run agent:test
```

### 実践例

#### 1. Phase 3.1: Sequential推論エンジンの使用

```typescript
import { SequentialInferenceEngine } from './src/engines/sequential-inference-engine.js';
import { DependencyAnalyzer } from './src/analysis/dependency-analyzer.js';

const engine = new SequentialInferenceEngine();
const analyzer = new DependencyAnalyzer(engine);

// 複雑な推論クエリ
const complexQuery = {
  id: 'complex-analysis-1',
  description: 'マイクロサービス間の影響分析',
  context: {
    services: ['api', 'database', 'cache'],
    changeRequest: 'API認証方式の変更',
    constraints: ['ダウンタイム最小化', 'データ整合性維持']
  },
  priority: 'high' as const
};

const inferenceResult = await engine.processComplexQuery(complexQuery);
const dependencyResult = await analyzer.analyzeSystemDependencies({
  targetPath: './src',
  analysisType: 'full',
  includeExternal: true
});

console.log('推論結果:', inferenceResult.reasoning);
console.log('影響範囲:', dependencyResult.impactAnalysis);
```

#### 2. Phase 3.2: Playwright E2Eテスト自動生成

```typescript
import { PlaywrightIntegration } from './src/testing/playwright-integration.js';

const playwright = new PlaywrightIntegration(engine);

// E2Eテスト自動生成
const testRequest = {
  id: 'e2e-test-gen-1',
  targetComponents: ['user-auth', 'product-catalog', 'shopping-cart'],
  dependencyAnalysis: dependencyResult,
  testTypes: ['critical-path', 'error-scenarios', 'performance'],
  browsers: ['chromium', 'firefox', 'webkit'],
  constraints: {
    maxExecutionTime: 300000, // 5分
    priority: 'high'
  }
};

const e2eTests = await playwright.generateE2ETests(testRequest);

console.log(`生成されたテスト: ${e2eTests.tests.length}件`);
console.log('実行時間予測:', e2eTests.estimatedExecutionTime);

// テスト実行
const executionResult = await playwright.executeTests(e2eTests.tests);
console.log('テスト結果:', executionResult.summary);
```

#### 3. Phase 3.2: 視覚回帰テスト

```typescript
import { VisualRegressionTesting } from './src/testing/visual-regression.js';

const visualTesting = new VisualRegressionTesting(playwright);

// 視覚回帰テスト生成
const visualRequest = {
  id: 'visual-test-1',
  components: [
    { path: '/login', name: 'ログインページ' },
    { path: '/dashboard', name: 'ダッシュボード' },
    { path: '/product/:id', name: '商品詳細' }
  ],
  viewports: [
    { width: 1280, height: 720, name: 'Desktop' },
    { width: 768, height: 1024, name: 'Tablet' },
    { width: 375, height: 667, name: 'Mobile' }
  ],
  browsers: ['chromium', 'firefox'],
  options: {
    threshold: 0.2, // 20%の差分を許容
    includeAnimations: false,
    generateBaseline: true
  }
};

const visualTests = await visualTesting.generateVisualTests(visualRequest);

// ベースライン生成
const baselineResult = await visualTesting.captureBaselines(visualTests.tests);
console.log('ベースライン生成:', baselineResult.captured);

// 視覚回帰検証実行
const visualResult = await visualTesting.executeVisualTests(visualTests.tests);
console.log('視覚差分検出:', visualResult.differences);
```

#### 4. Phase 3.2: インテリジェントテスト選択

```typescript
import { IntelligentTestSelection } from './src/testing/intelligent-test-selection.js';

const testSelection = new IntelligentTestSelection(engine);

// コード変更に基づく最適テスト選択
const selectionRequest = {
  id: 'smart-selection-1',
  changes: [
    {
      id: 'change-1',
      type: 'modification',
      filePath: 'src/auth/login.ts',
      componentId: 'user-auth',
      impact: 'medium',
      changeType: 'logic',
      linesChanged: 15,
      riskScore: 0.6,
      description: 'ログイン認証ロジックの改修'
    }
  ],
  testInventory: {
    id: 'inventory-1',
    timestamp: new Date(),
    totalTests: 247,
    testSuites: [...] // 利用可能なテストスイート
  },
  constraints: {
    maxExecutionTime: 120000, // 2分以内
    maxTestCount: 50,
    requiredCoverage: 80,
    priorityLevels: ['critical', 'high'],
    testTypes: ['unit', 'integration', 'e2e']
  },
  strategy: {
    mode: 'hybrid',
    riskWeighting: {
      changeImpact: 0.4,
      componentCriticality: 0.3,
      historicalFailures: 0.2,
      dependencyComplexity: 0.1
    }
  }
};

const selectedTests = await testSelection.selectTests(selectionRequest);

console.log(`選択されたテスト: ${selectedTests.selectedTests.totalTests}件`);
console.log('予想実行時間:', selectedTests.selectedTests.estimatedExecutionTime);
console.log('信頼度スコア:', selectedTests.analysis.confidenceScore);
```

#### 5. Phase 3.3: 統合最適化システム ✨ **NEW**

```typescript
import { 
  OptimizationSystem, 
  createOptimizationSystem 
} from './src/optimization/index.js';

// 統合最適化システムの初期化
const optimizationSystem = createOptimizationSystem({
  monitoring: {
    performanceMonitor: {
      interval: 1000, // 1秒間隔での監視
      thresholds: {
        cpu: { warning: 70, critical: 90 },
        memory: { warning: 80, critical: 95 },
        responseTime: { warning: 1000, critical: 2000 },
        errorRate: { warning: 5, critical: 10 }
      }
    },
    metricsCollector: {
      aggregationInterval: 5000,
      retention: 300000 // 5分間データ保持
    }
  },
  parallelOptimization: {
    optimizer: {
      maxConcurrency: 8,
      loadBalancing: 'resource_aware'
    },
    scheduler: {
      algorithm: 'resource_aware'
    },
    resourcePool: {
      sizing: {
        initialSize: 10,
        minSize: 5,
        maxSize: 50
      }
    }
  },
  integration: {
    adaptiveOptimization: true,
    performanceBasedScaling: true,
    crossSystemIntegration: true
  }
});

// システム開始
await optimizationSystem.start();

// 操作の追跡
optimizationSystem.trackOperation('user-login', Date.now());
optimizationSystem.trackOperation('data-processing', Date.now());

// メトリクス取得
const metrics = optimizationSystem.getSystemMetrics();
console.log('システムメトリクス:', {
  monitoring: metrics.monitoring,
  performance: metrics.performance,
  integration: metrics.integration
});

// システム終了
await optimizationSystem.stop();
```

#### 6. Phase 3.3: パフォーマンス監視システム ✨ **NEW**

```typescript
import { 
  PerformanceMonitor,
  MetricsCollector,
  AlertManager 
} from './src/optimization/monitoring/index.js';

// 高度なパフォーマンス監視システム
const monitor = new PerformanceMonitor({
  interval: 500,
  enableAdvancedMetrics: true,
  customMetrics: ['api_response_time', 'database_connections']
});

const metricsCollector = new MetricsCollector({
  aggregationInterval: 2000,
  retention: 600000, // 10分間
  enableHistoricalAnalysis: true
});

const alertManager = new AlertManager();

// カスタムアラートルール設定
alertManager.addRule({
  id: 'high-error-rate',
  name: 'High Error Rate Alert',
  condition: (metrics) => metrics.errorRate > 0.05,
  severity: 'high',
  actions: ['email', 'webhook']
});

// システム開始
await monitor.start();
await metricsCollector.start();
await alertManager.start();

// メトリクス収集開始
monitor.on('metricsCollected', (metrics) => {
  metricsCollector.collect(metrics);
});

// アラート処理
alertManager.on('alertTriggered', (alert) => {
  console.log('アラート発生:', alert.message);
});

// パフォーマンス分析
const analysis = await monitor.analyzePerformance({
  timeRange: { start: Date.now() - 300000, end: Date.now() },
  includeRegression: true,
  generateRecommendations: true
});

console.log('パフォーマンス分析:', analysis.summary);
console.log('改善提案:', analysis.recommendations);
```

#### 7. Phase 3.3: 並列最適化システム ✨ **NEW**

```typescript
import { 
  ParallelOptimizer,
  TaskScheduler,
  ResourcePool
} from './src/optimization/parallel/index.js';

// リソースプール設定
const resourcePool = new ResourcePool('default-pool', {
  sizing: {
    initialSize: 15,
    minSize: 5,
    maxSize: 100,
    scalingFactor: 1.5
  },
  resources: {
    cpu: { capacity: 8, allocated: 0 },
    memory: { capacity: 16384, allocated: 0 }, // 16GB
    io: { capacity: 1000, allocated: 0 },
    network: { capacity: 1000, allocated: 0 }
  }
});

// タスクスケジューラ設定
const scheduler = new TaskScheduler(resourcePool, {
  algorithm: 'resource_aware',
  enableLoadBalancing: true,
  priorityWeights: {
    high: 3.0,
    medium: 2.0,
    low: 1.0
  }
});

// 並列オプティマイザ設定
const optimizer = new ParallelOptimizer({
  maxConcurrency: 12,
  loadBalancing: 'adaptive',
  optimizationStrategy: 'throughput'
});

// システム開始
await resourcePool.start();
await scheduler.start();
await optimizer.start();

// タスク実行
const task = {
  id: 'data-analysis-task',
  type: 'cpu_intensive',
  priority: 'high',
  resourceRequirements: {
    cpu: 2,
    memory: 1024,
    estimatedDuration: 30000
  },
  payload: {
    dataSet: 'large_dataset.json',
    operation: 'statistical_analysis'
  }
};

const result = await optimizer.executeTask(task);
console.log('タスク実行結果:', result);

// パフォーマンス最適化
const optimizationResult = await optimizer.optimizePerformance({
  target: 'throughput',
  constraints: {
    maxCpuUsage: 0.8,
    maxMemoryUsage: 0.85
  }
});

console.log('最適化結果:', optimizationResult.improvements);
```

#### 8. SuperClaude Framework統合 ✨ **NEW**

```typescript
import { TokenOptimizer } from './src/utils/token-optimizer.js';
import { EvidenceValidator } from './src/utils/evidence-validator.js';
import { 
  UnifiedAnalyzeCommand,
  UnifiedDocumentCommand,
  UnifiedImproveCommand 
} from './src/commands/extended/index.js';

// Token最適化システム
const tokenOptimizer = new TokenOptimizer();

// ステアリング文書の最適化
const steeringDocs = {
  product: '製品仕様に関する詳細な文書...',
  architecture: 'システム設計に関する文書...',
  standards: 'コーディング規約と品質基準...'
};

const { compressed, stats } = await tokenOptimizer.compressSteeringDocuments(
  steeringDocs,
  {
    maxTokens: 3000,
    preservePriority: ['product', 'architecture'],
    compressionLevel: 'high'
  }
);

console.log('Token削減:', `${stats.reductionPercentage}% (${stats.original} → ${stats.compressed})`);

// Evidence-based validation
const evidenceValidator = new EvidenceValidator();

const validationResult = await evidenceValidator.validateSolution(
  'ユーザー認証システムの実装',
  `
  JWT ベースの認証システムを実装する：
  \`\`\`typescript
  import jwt from 'jsonwebtoken';
  
  export class AuthService {
    generateToken(userId: string): string {
      return jwt.sign({ userId }, process.env.JWT_SECRET, { expiresIn: '24h' });
    }
  }
  \`\`\`
  `,
  {
    requireDocumentation: true,
    requireTests: true,
    minConfidence: 0.8
  }
);

console.log('検証結果:', validationResult.isValid ? '合格' : '要改善');
console.log('信頼度:', validationResult.confidence);
console.log('証拠サマリー:', validationResult.evidence.length);

// Extended Commands
const analyzeCommand = new UnifiedAnalyzeCommand();
const documentCommand = new UnifiedDocumentCommand();
const improveCommand = new UnifiedImproveCommand();

// 統合分析コマンド
const analysisResult = await analyzeCommand.execute([
  'src/auth/',
  '--depth=deep',
  '--security',
  '--performance'
]);

console.log('分析結果:', analysisResult.data);
```

#### 9. 従来の包括的テストの生成
```typescript
import { TestGenerationAgent } from './src/agents/test-generation-agent.js';

const agent = new TestGenerationAgent();

const testSuite = await agent.generateComprehensiveTests({
  requirements: requirements,
  codeFiles: ['src/user.ts', 'src/cart.ts'],
  testTypes: ['unit', 'integration', 'e2e'],
  coverage: {
    target: 95,
    excludePatterns: ['**/node_modules/**']
  }
});

console.log('生成されたテスト:', testSuite.tests);
```

#### 2. BDDシナリオの生成
```typescript
const bddScenarios = await agent.generateBDDScenarios([
  {
    id: 'REQ-001',
    description: 'ユーザーはログインできる',
    type: 'functional'
  }
]);

// 出力例:
// Feature: ユーザー認証
//   Scenario: 正常なログイン
//     Given ユーザーが登録済みである
//     When 正しいメール・パスワードを入力する
//     Then ログインに成功する
```

#### 3. プロパティベーステストの生成
```typescript
const propertyTests = await agent.generatePropertyTests({
  targetFunction: 'calculateTotal',
  properties: [
    'total >= 0',
    'total === sum(items.map(i => i.price * i.quantity))',
    'calculateTotal([]) === 0'
  ]
});
```

---

## 💻 Phase 4: Code Agent（コード生成）

### 基本的な使い方

#### MCPサーバーとして使用
```bash
npm run mcp:code
```

#### 直接エージェント実行
```bash
npm run agent:code
```

### 実践例

#### 1. TDDベースのコード生成
```typescript
import { CodeGenerationAgent } from './src/agents/code-generation-agent.ts';

const agent = new CodeGenerationAgent();

const code = await agent.generateCodeFromTests({
  tests: [
    {
      path: 'tests/user.test.ts',
      content: `
        describe('User', () => {
          it('should create user with valid data', () => {
            const user = new User('john@example.com', 'John');
            expect(user.email).toBe('john@example.com');
            expect(user.name).toBe('John');
          });
        });
      `,
      type: 'unit'
    }
  ],
  language: 'typescript'
});

console.log('生成されたコード:', code.files);
```

#### 2. OpenAPI仕様からのコード生成
```typescript
const apiCode = await agent.generateFromOpenAPI(
  openApiSpec,
  {
    framework: 'fastify',
    database: 'postgres',
    includeValidation: true,
    includeAuth: true
  }
);
```

#### 3. デザインパターンの適用
```typescript
const improvedCode = await agent.applyDesignPatterns(
  originalCode,
  ['singleton', 'factory', 'repository']
);
```

#### 4. セキュリティ機能の追加
```typescript
const secureCode = await agent.addSecurityFeatures(code, {
  authentication: 'jwt',
  authorization: 'rbac',
  encryption: true,
  rateLimit: true,
  cors: true
});
```

---

## ✅ Phase 5: Verify Agent（品質検証）

### 基本的な使い方

#### 包括的検証の実行
```bash
npm run verify:all
```

#### 各種検証の個別実行
```bash
# テスト実行
npm run verify:tests

# コード品質チェック
npm run verify:quality

# セキュリティ監査
npm run verify:security

# MCPサーバーとして起動
npm run verify:server
```

### 実践例

#### 1. 全自動品質検証
```typescript
import { VerifyAgent } from './src/agents/verify-agent.js';

const agent = new VerifyAgent();

const result = await agent.runFullVerification({
  projectPath: '/path/to/project',
  verificationTypes: [
    'tests', 'coverage', 'linting', 'typechecking', 
    'security', 'performance', 'mutations'
  ],
  strictMode: true
});

console.log('検証結果:', result);
```

#### 2. トレーサビリティマトリクスの生成
```typescript
const matrix = await agent.buildTraceabilityMatrix({
  projectPath: '/path/to/project'
});

console.log('要件カバレッジ:', matrix.coverage);
console.log('リンクされていない要件:', matrix.unlinkedRequirements);
```

#### 3. 品質メトリクスの算出
```typescript
const metrics = await agent.calculateQualityMetrics({
  projectPath: '/path/to/project'
});

console.log('品質スコア:', metrics.overallScore);
console.log('技術負債:', metrics.technicalDebt);
```

---

## 🚀 Phase 6: Operate Agent（運用・監視）

### 基本的な使い方

#### MCPサーバーとして使用
```bash
npm run operate:server
```

#### 開発モード（自動リロード）
```bash
npm run operate:dev
```

### 実践例

#### 1. 自動デプロイメント
```typescript
import { OperateAgent } from './src/agents/operate-agent.js';

const agent = new OperateAgent({
  deploymentStrategy: 'blue-green',
  healthCheckEndpoint: '/health',
  rollbackOnFailure: true
});

const deployment = await agent.deployApplication({
  version: '1.2.3',
  environment: 'production',
  dockerImage: 'myapp:1.2.3',
  replicas: 3
});

console.log('デプロイID:', deployment.id);
console.log('ステータス:', deployment.status);
```

#### 2. ヘルスモニタリング
```typescript
const health = await agent.monitorHealth({
  services: ['api', 'database', 'cache'],
  checkInterval: 30000, // 30秒
  alertThresholds: {
    responseTime: 1000,
    errorRate: 0.01,
    cpuUsage: 0.8
  }
});
```

#### 3. インシデント対応
```typescript
const incident = await agent.handleIncident({
  type: 'service_down',
  service: 'api',
  severity: 'high',
  autoResolve: true
});

console.log('インシデントID:', incident.id);
console.log('対応ステータス:', incident.status);
```

#### 4. カオスエンジニアリング
```typescript
const chaosTest = await agent.runChaosTest({
  type: 'pod-failure',
  target: 'api-service',
  duration: 300000, // 5分
  observationWindow: 600000 // 10分
});
```

---

## 🔧 統合的な使用例

### フルサイクル開発フロー

```typescript
// 1. 要件分析
const intentAgent = new IntentAgent();
const requirements = await intentAgent.analyzeIntent(userInput);

// 2. 形式仕様生成
const formalAgent = new FormalAgent();
const specification = await formalAgent.generateTLAPlus(
  requirements.requirements.map(r => r.description).join('\n')
);

// 3. テスト生成
const testAgent = new TestGenerationAgent();
const tests = await testAgent.generateComprehensiveTests({
  requirements: requirements.requirements,
  specifications: [specification]
});

// 4. コード生成
const codeAgent = new CodeGenerationAgent();
const code = await codeAgent.generateCodeFromTests({
  tests: tests.tests,
  language: 'typescript'
});

// 5. 品質検証
const verifyAgent = new VerifyAgent();
const verification = await verifyAgent.runFullVerification({
  projectPath: './generated-project',
  verificationTypes: ['tests', 'coverage', 'linting', 'security']
});

// 6. デプロイ・運用
if (verification.passed) {
  const operateAgent = new OperateAgent();
  const deployment = await operateAgent.deployApplication({
    version: '1.0.0',
    environment: 'production'
  });
}
```

## 🎨 Claude Code での使用

### MCP サーバー設定

Claude Code の設定ファイルに以下を追加：

```json
{
  "mcpServers": {
    "ae-framework": {
      "command": "npx",
      "args": ["tsx", "src/mcp-server/intent-server.ts"],
      "cwd": "/path/to/ae-framework"
    }
  }
}
```

### Claude Code での対話例

```
ユーザー: 「ECサイトの要件を分析してください」

Claude: ae-frameworkのIntent Agentを使用して要件を分析します。

[Intent Agentを呼び出し]

分析結果：
- 機能要件: 15項目
- 非機能要件: 8項目  
- 検出された曖昧性: 3箇所
- 生成されたユーザーストーリー: 12個

次にFormal Agentで形式仕様を生成しますか？
```

## 📊 メトリクス・監視

### TDD コンプライアンス監視

```bash
# TDDガードを有効化
npm run validate-tdd

# メトリクスの確認
cat metrics/project-metrics.json
```

### Phase 3.2 テスト自動化メトリクス

```bash
# E2Eテスト実行統計
npm run test:playwright -- --reporter=json > metrics/e2e-results.json

# 視覚回帰テスト結果
npm run test:visual -- --reporter=json > metrics/visual-results.json

# Phase 3.2 専用テストスイート
npm run test:phase3.2:core
```

### CI/CD パフォーマンス監視

```bash
# 高速CI実行時間 (目標: 2分以内)
npm run test:fast

# CI実行ログの確認
cat .github/workflows/ci-fast.yml

# フルCI統計 (週次実行)
gh run list --workflow="Full CI"
```

### 品質メトリクスの監視

```bash
# 継続的品質監視
npm run verify:all

# カバレッジレポート
npm run coverage

# 変異テスト (週次自動実行)
npm run mutation
```

### テスト選択効率性メトリクス

```bash
# インテリジェントテスト選択の効果測定
# - 実行時間短縮率
# - カバレッジ維持率  
# - リスク検出精度
npm run analyze:test-selection-metrics
```

## 🆘 トラブルシューティング

### よくある問題

#### 1. メモリ不足エラー
```bash
# Node.jsのメモリ制限を増加
export NODE_OPTIONS="--max-old-space-size=4096"
npm run mcp:code
```

#### 2. タイムアウトエラー
```typescript
// タイムアウト設定を調整
const agent = new CodeGenerationAgent();
agent.timeout = 300000; // 5分
```

#### 3. Phase 3.2 Playwrightエラー
```bash
# Playwrightブラウザのインストール
npx playwright install

# E2Eテストタイムアウト
npm run test:playwright -- --timeout=60000

# ヘッドレスモード無効化（デバッグ用）
npm run test:playwright -- --headed
```

#### 4. 視覚回帰テストエラー
```bash
# ベースライン画像生成
npm run visual:baseline

# 差分しきい値調整
npm run test:visual -- --threshold=0.3

# 特定ビューポートのみテスト
npm run test:visual -- --viewport=desktop
```

#### 5. CI実行時間問題
```bash
# 高速CI使用（開発時）
npm run test:fast

# テスト並列実行数調整
npm run test -- --maxWorkers=4

# 特定テストのスキップ
npm run test -- --exclude="**/slow.test.ts"
```

#### 6. 依存関係エラー
```bash
# 依存関係の再インストール
npm ci
npm run build
```

## 🔄 アップグレードガイド

新しいバージョンへの更新：

```bash
git pull origin main
npm install
npm run build

# 設定の確認
npm test
npm run lint
```

## 📚 参考資料

- [エージェント別詳細ドキュメント](./agents/)
- [API リファレンス](./api/)
- [設定リファレンス](./configuration/)
- [トラブルシューティング](./troubleshooting/)

## 💡 ベストプラクティス

### 🎯 Phase 3.2 & 3.3 導入のベストプラクティス

#### Phase 3.2 (AI駆動テスト自動化)
1. **段階的導入**: Phase 3.1 → 3.2 の順序で導入
2. **E2Eテスト戦略**: クリティカルパスから始めて段階的に拡張
3. **視覚回帰テスト**: ベースライン品質を確立してから運用開始
4. **インテリジェントテスト選択**: AIによる最適化で実行時間最小化
5. **CI最適化**: 開発時は高速CI、リリース前はフルCIを活用

#### Phase 3.3 (統合最適化システム) ✨ **NEW**
1. **監視システム**: パフォーマンス監視を段階的に導入
2. **並列最適化**: リソース使用量を監視しながら並列度を調整
3. **統合最適化**: システム間連携を確認してから本格運用
4. **アラート設定**: 適切なしきい値設定で誤検知を防止
5. **メトリクス分析**: 継続的なパフォーマンス改善サイクル確立

#### SuperClaude Framework統合 ✨ **NEW**
1. **Token最適化**: ステアリング文書の圧縮率を段階的に向上
2. **Evidence-based検証**: 信頼度しきい値を適切に設定
3. **Extended Commands**: 統合分析・文書化・改善コマンドの活用
4. **品質保証**: 検証システムと組み合わせた品質管理

### 📋 一般的なベストプラクティス

1. **段階的導入**: 1つのフェーズから始めて徐々に拡張
2. **継続的監視**: verify:allを定期実行
3. **メトリクス追跡**: 品質改善の効果測定
4. **チーム共有**: 生成された仕様・テストをチーム全体で共有
5. **カスタマイズ**: プロジェクト特有の要件に応じた設定調整

### ⚡ パフォーマンス最適化

#### 従来の最適化
1. **CI実行時間**: 開発時2分、フルテスト30分を目標
2. **並列実行**: E2Eテストとビジュアルテストの並列化
3. **キャッシュ活用**: Playwrightブラウザとテスト結果のキャッシュ
4. **選択的実行**: 変更影響範囲に基づくスマートテスト選択

#### Phase 3.3 統合最適化 ✨ **NEW**
1. **システム監視**: リアルタイムパフォーマンス監視とアラート
2. **リソース最適化**: CPU・メモリ・I/O・ネットワークの最適配分
3. **並列処理最適化**: 動的負荷分散とリソースプール管理
4. **予測的スケーリング**: 過去データに基づく自動リソース調整
5. **統合メトリクス**: システム全体の包括的パフォーマンス分析

#### SuperClaude Framework最適化 ✨ **NEW**
1. **Token効率化**: 最大70%のtoken削減による高速処理
2. **コンテキスト最適化**: 関連度ベースの情報選択
3. **証拠ベース検証**: 信頼性の高い解決案の迅速な特定
4. **統合コマンド**: 分析・文書化・改善の一元化による効率向上

---

このガイドを参考に、ae-frameworkを活用した効率的な開発を始めてください！