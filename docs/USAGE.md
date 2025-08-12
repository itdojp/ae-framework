# AE Framework 使い方ガイド

ae-frameworkの全6フェーズエージェントの使用方法と実践例を詳しく説明します。

## 🎯 概要

ae-frameworkは以下の6フェーズでソフトウェア開発を支援します：

1. **Intent Agent** (Phase 1): 要件定義・分析
2. **Formal Agent** (Phase 2): 形式仕様・設計
3. **Test Agent** (Phase 3): テスト設計・生成
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

# 3. テスト生成
npm run mcp:test

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

### 基本的な使い方

#### MCPサーバーとして使用
```bash
npm run mcp:test
```

#### 直接エージェント実行
```bash
npm run agent:test
```

### 実践例

#### 1. 包括的テストの生成
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

### 品質メトリクスの監視

```bash
# 継続的品質監視
npm run verify:all

# カバレッジレポート
npm run coverage

# 変異テスト
npm run mutation
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

#### 3. 依存関係エラー
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

1. **段階的導入**: 1つのフェーズから始めて徐々に拡張
2. **継続的監視**: verify:allを定期実行
3. **メトリクス追跡**: 品質改善の効果測定
4. **チーム共有**: 生成された仕様・テストをチーム全体で共有
5. **カスタマイズ**: プロジェクト特有の要件に応じた設定調整

---

このガイドを参考に、ae-frameworkを活用した効率的な開発を始めてください！