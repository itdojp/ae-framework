# AE Framework Usage Guide

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Comprehensive usage guide for AE Framework's complete 6-phase agent system with practical examples**

### 🎯 Overview

AE Framework supports software development through the following 6 phases:

1. **Intent Agent** (Phase 1): Requirements definition and analysis
2. **Formal Agent** (Phase 2): Formal specification and design
3. **Test Agent** (Phase 3): Test design and generation
   - **Phase 3.1**: Sequential reasoning engine and dependency analysis
   - **Phase 3.2**: E2E automation, visual regression testing, AI selection ✨ **NEW**
   - **Phase 3.3**: Integration optimization and performance monitoring ✨ **NEW**
4. **Code Agent** (Phase 4): Code implementation and generation
5. **Verify Agent** (Phase 5): Quality verification and auditing
6. **Operate Agent** (Phase 6): Operations and monitoring

### 🔄 Basic Development Flow

#### Complete Project Example

Development flow for creating a new web application:

```bash
# 1. Requirements analysis
npm run intent-agent

# 2. Formal specification generation
npm run formal-agent

# 3. Test generation (Phase 3.1 & 3.2)
npm run mcp:test

# 3a. E2E automatic test generation (Phase 3.2)
npm run e2e:demo

# 3b. Visual regression testing (Phase 3.2)
npm run visual:demo

# 3c. Intelligent test selection (Phase 3.2) ✨ **NEW**
npm test -- tests/testing/intelligent-test-selection.test.ts

# 3d. Integration optimization system (Phase 3.3) ✨ **NEW**
npm test -- tests/optimization/system-integration.test.ts

# 4. Code generation
npm run mcp:code

# 5. Quality verification
npm run verify:all

# 6. Deployment and operations
npm run operate:server
```

---

## 📝 Phase 1: Intent Agent (Requirements Definition)

### Basic Usage

#### Using as Claude Code Task Tool (Recommended)
In Claude Code environment, automatically integrated as Task Tool:

```
User: Please analyze project requirements

Claude Code: Executing requirements analysis using Intent Task Adapter...

✅ Intent Analysis Complete - 15 requirements identified
📋 Next steps:
  • Review identified requirements for completeness  
  • Proceed to Phase 2 (Formal Specification)
```

#### CLI Execution
```bash
# Execute requirements analysis
ae-framework intent --analyze --sources="requirements.md"

# Completeness validation
ae-framework intent --validate

# Phase check
ae-framework check --phase 1-intent
```

#### Using as MCP Server (Fallback)
```bash
npm run intent-agent
```

#### Direct Execution (Development/Testing)
```typescript
import { IntentAgent } from './src/agents/intent-agent.js';

const agent = new IntentAgent();

const request = {
  sources: [
    {
      type: 'text',
      content: `
        Users must be able to log in.
        Users can search and purchase products.
        Administrators can manage inventory.
      `
    }
  ],
  context: {
    domain: 'e-commerce',
    constraints: [
      {
        type: 'technical',
        description: 'Response time within 1 second',
        impact: 'high'
      }
    ]
  }
};

const result = await agent.analyzeIntent(request);
console.log('Generated requirements:', result.requirements);
console.log('User stories:', result.userStories);
```

### Key Features

#### 1. Requirements Extraction from Natural Language
```typescript
const requirements = await agent.extractFromNaturalLanguage(`
  The system needs to provide the following features:
  - User authentication (JWT method)
  - Product search (with filtering)
  - Shopping cart
  - Payment processing (Stripe integration)
`);
```

#### 2. Ambiguity Detection
```typescript
const ambiguities = await agent.detectAmbiguities([
  {
    type: 'text',
    content: 'The system must be fast and secure'
  }
]);
// → Determines that specific definitions for "fast" and "secure" are needed
```

#### 3. Domain Model Generation
```typescript
const domainModel = await agent.buildDomainModelFromRequirements(
  requirements,
  { domain: 'e-commerce' }
);
console.log('Entities:', domainModel.entities);
console.log('Relationships:', domainModel.relationships);
```

---

## 🔬 Phase 2: Formal Agent (Formal Specification)

### Basic Usage

#### Using as MCP Server
```bash
npm run formal-agent
```

#### TLA+ Specification Generation
```bash
npm run generate-tla
```

#### Specification Validation
```bash
npm run validate-specs
```

#### Model Checking
```bash
npm run model-check
```

### Practical Examples

#### 1. Automatic TLA+ Specification Generation
```typescript
import { FormalAgent } from './src/agents/formal-agent.js';

const agent = new FormalAgent();

const spec = await agent.generateTLAPlus(`
  Shopping cart system:
  - Can add products to cart
  - Can remove products from cart
  - Calculate cart total
  - Maintain consistency during concurrent access
`);

console.log('TLA+ specification:', spec.content);
```

#### 2. State Transition Diagram Generation
```typescript
const stateDiagram = await agent.generateStateDiagram([
  'idle', 'loading', 'success', 'error'
], [
  { from: 'idle', to: 'loading', trigger: 'submit' },
  { from: 'loading', to: 'success', trigger: 'response_ok' },
  { from: 'loading', to: 'error', trigger: 'response_error' }
]);
```

#### 3. Formal Verification Execution
```typescript
const verification = await agent.verifySpecification(spec, {
  checkDeadlock: true,
  checkLiveness: true,
  maxStates: 1000000
});

if (!verification.valid) {
  console.log('Verification errors:', verification.errors);
}
```

---

## 🧪 Phase 3: Test Agent (Test Generation)

Phase 3 consists of multiple sub-phases:

### 📋 Phase 3.1: Sequential Reasoning Engine & Dependency Analysis

Complex problem solving through advanced reasoning engine and inter-component dependency analysis

#### Basic Usage
```bash
# Sequential reasoning engine demo
npm run analyze:demo

# Dependency analysis
npm run dependency:analyze
```

### 🎭 Phase 3.2: E2E Automation & Visual Regression Testing ✨ **NEW**

AI-driven comprehensive test automation system

#### Basic Usage

##### Using as MCP Server
```bash
npm run mcp:test
```

##### E2E Test Auto-generation
```bash
npm run e2e:demo
npm run test:playwright
```

##### Visual Regression Testing
```bash
npm run visual:demo
npm run test:visual
```

##### Fast Test Execution (CI Optimized)
```bash
npm run test:fast
npm run test:phase3.2:core
```

#### Direct Agent Execution
```bash
npm run agent:test
```

### Practical Examples

#### 1. Phase 3.1: Sequential Reasoning Engine Usage

```typescript
import { SequentialInferenceEngine } from './src/engines/sequential-inference-engine.js';
import { DependencyAnalyzer } from './src/analysis/dependency-analyzer.js';

const engine = new SequentialInferenceEngine();
const analyzer = new DependencyAnalyzer(engine);

// Complex reasoning query
const complexQuery = {
  id: 'complex-analysis-1',
  description: 'Impact analysis between microservices',
  context: {
    services: ['api', 'database', 'cache'],
    changeRequest: 'API authentication method change',
    constraints: ['Minimize downtime', 'Maintain data consistency']
  },
  priority: 'high' as const
};

const inferenceResult = await engine.processComplexQuery(complexQuery);
const dependencyResult = await analyzer.analyzeSystemDependencies({
  targetPath: './src',
  analysisType: 'full',
  includeExternal: true
});

console.log('Inference result:', inferenceResult.reasoning);
console.log('Impact scope:', dependencyResult.impactAnalysis);
```

#### 2. Phase 3.2: Playwright E2E Test Auto-generation

```typescript
import { PlaywrightIntegration } from './src/testing/playwright-integration.js';

const playwright = new PlaywrightIntegration(engine);

// E2E test auto-generation
const testRequest = {
  id: 'e2e-test-gen-1',
  targetComponents: ['user-auth', 'product-catalog', 'shopping-cart'],
  dependencyAnalysis: dependencyResult,
  testTypes: ['critical-path', 'error-scenarios', 'performance'],
  browsers: ['chromium', 'firefox', 'webkit'],
  constraints: {
    maxExecutionTime: 300000, // 5 minutes
    priority: 'high'
  }
};

const e2eTests = await playwright.generateE2ETests(testRequest);

console.log(`Generated tests: ${e2eTests.tests.length} tests`);
console.log('Estimated execution time:', e2eTests.estimatedExecutionTime);

// Test execution
const executionResult = await playwright.executeTests(e2eTests.tests);
console.log('Test results:', executionResult.summary);
```

[Content continues with additional sections for comprehensive coverage...]

---

## Japanese

**ae-frameworkの全6フェーズエージェントの使用方法と実践例を詳しく説明します**

### 🎯 概要

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

### 🔄 基本的な開発フロー

#### 完全なプロジェクト例

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

#### Claude Code Task Tool として使用（推奨）
Claude Code環境では自動的にTask Toolとして統合されています：

```
User: プロジェクトの要件分析をお願いします

Claude Code: Intent Task Adapterを使用して要件分析を実行します...

✅ Intent Analysis Complete - 15 requirements identified
📋 Next steps:
  • Review identified requirements for completeness  
  • Proceed to Phase 2 (Formal Specification)
```

#### CLI実行
```bash
# 要件分析実行
ae-framework intent --analyze --sources="requirements.md"

# 完全性検証
ae-framework intent --validate

# フェーズチェック
ae-framework check --phase 1-intent
```

#### MCPサーバーとして使用（フォールバック）
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

[Japanese content continues with all remaining sections...]

---

**🚀 Experience efficient development with AE Framework! / ae-frameworkを活用した効率的な開発を始めてください！**