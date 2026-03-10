---
docRole: derived
canonicalSource:
- README.md
- docs/getting-started/QUICK-START-GUIDE.md
lastVerified: '2026-03-10'
---
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

Default after intent: run `ae tests:suggest` to generate tests-first prompts before proceeding to later phases.

### CLI Reference
- Canonical command list: `docs/reference/CLI-COMMANDS-REFERENCE.md`
- Entry migration guide: `docs/guides/CLI-MIGRATION.md`

### 🔄 Basic Development Flow

#### Complete Project Example

Development flow for creating a new web application:

```bash
# 1. Requirements analysis
pnpm run intent-agent

# 1a. Tests-first prompt (default after intent)
ae tests:suggest --template http-api --intent "Build a minimal todo API"

# 2. Formal specification generation (optional)
pnpm run formal-agent

# 3. Test generation (Phase 3.1 & 3.2)
pnpm run mcp:test

# 3a. E2E automatic test generation (Phase 3.2)
pnpm run e2e:demo

# 3b. Visual regression testing (Phase 3.2)
pnpm run visual:demo

# 3c. Intelligent test selection (Phase 3.2) ✨ **NEW**
pnpm test -- tests/testing/intelligent-test-selection.test.ts

# 3d. Integration optimization system (Phase 3.3) ✨ **NEW**
pnpm test -- tests/optimization/system-integration.test.ts

# 4. Code generation
pnpm run mcp:code

# 5. Quality verification
pnpm run verify:all

# 6. Deployment and operations
pnpm run operate:server
```

### 🔎 Minimal Output Samples (English)
- Intent (JSON excerpt):
```
{ "requirements": 15, "stories": 12, "next": ["Phase 2", "Domain model"] }
```
- Verify (console one-liner):
```
• CI: ✅ tests 124/124, coverage 84% (≥80), typecov 66% (baseline 65); a11y 96 (≥95), perf 78 (≥75)
```

### 🔁 Quick CLI Samples（現行実装）

以下は現在のCLI実装に基づく、最短経路の確認用コマンドです。

```bash
# 1) Runtime Conformance（サンプル生成→検証）
pnpm run ae-framework -- conformance sample \
  --rules configs/samples/sample-rules.json \
  --config configs/samples/sample-config.json \
  --data configs/samples/sample-data.json \
  --context configs/samples/sample-context.json

pnpm run ae-framework -- conformance verify \
  --input configs/samples/sample-data.json \
  --context-file configs/samples/sample-context.json \
  --rules configs/samples/sample-rules.json --format json \
  --output artifacts/conformance/conformance-results.json

# 2) SBOM 生成
pnpm run ae-framework -- sbom generate --format json --output sbom.json --verbose

# 3) UI スキャフォールド（標準 CLI）
pnpm run ae-framework -- ui-scaffold --components

# 4) ベンチマーク（一覧とドライラン）
ae-benchmark list --enabled-only
ae-benchmark run --ci --dry-run

# 5) セキュリティ設定の表示
pnpm run ae-framework -- security show-config --env development
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
pnpm run intent-agent
```

#### Direct Execution (Development/Testing)
```text
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
```text
const requirements = await agent.extractFromNaturalLanguage(`
  The system needs to provide the following features:
  - User authentication (JWT method)
  - Product search (with filtering)
  - Shopping cart
  - Payment processing (Stripe integration)
`);
```

#### 2. Ambiguity Detection
```text
const ambiguities = await agent.detectAmbiguities([
  {
    type: 'text',
    content: 'The system must be fast and secure'
  }
]);
// → Determines that specific definitions for "fast" and "secure" are needed
```

#### 3. Domain Model Generation
```text
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
pnpm run formal-agent
```

#### TLA+ Specification Generation
```bash
pnpm run generate-tla
```

#### Specification Validation
```bash
pnpm run validate-specs
```

#### Model Checking
```bash
pnpm run model-check
```

### Practical Examples

#### 1. Automatic TLA+ Specification Generation
```text
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
```text
const stateDiagram = await agent.generateStateDiagram([
  'idle', 'loading', 'success', 'error'
], [
  { from: 'idle', to: 'loading', trigger: 'submit' },
  { from: 'loading', to: 'success', trigger: 'response_ok' },
  { from: 'loading', to: 'error', trigger: 'response_error' }
]);
```

#### 3. Formal Verification Execution
```text
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
pnpm run analyze:demo

# Dependency analysis
pnpm run dependency:analyze
```

### 🎭 Phase 3.2: E2E Automation & Visual Regression Testing ✨ **NEW**

AI-driven comprehensive test automation system

#### Basic Usage

##### Using as MCP Server
```bash
pnpm run mcp:test
```

##### E2E Test Auto-generation
```bash
pnpm run e2e:demo
pnpm run test:playwright
```

##### Visual Regression Testing
```bash
pnpm run visual:demo
pnpm run test:visual
```

##### Fast Test Execution (CI Optimized)
```bash
pnpm run test:fast
pnpm run test:phase3.2:core
```

#### Direct Agent Execution
```bash
pnpm run agent:test
```

### Practical Examples

#### 1. Phase 3.1: Sequential Reasoning Engine Usage

```text
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

```text
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

### CLI リファレンス
- コマンド一覧: `docs/reference/CLI-COMMANDS-REFERENCE.md`
- 統一 entry の移行ガイド: `docs/guides/CLI-MIGRATION.md`

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

Intent 直後の既定ステップ: `ae tests:suggest` で tests-first プロンプトを生成します。

### 🔄 基本的な開発フロー

#### 完全なプロジェクト例

新しいWebアプリケーションを開発する場合のフロー：

```bash
# 1. 要件分析
pnpm run intent-agent

# 1a. tests-first プロンプト（Intent直後の既定）
ae tests:suggest --template http-api --intent "最低限のTodo APIを作る"

# 2. 形式仕様生成（任意）
pnpm run formal-agent

# 3. テスト生成 (Phase 3.1 & 3.2)
pnpm run mcp:test

# 3a. E2E自動テスト生成 (Phase 3.2)
pnpm run e2e:demo

# 3b. 視覚回帰テスト (Phase 3.2)  
pnpm run visual:demo

# 3c. インテリジェントテスト選択 (Phase 3.2) ✨ **NEW**
pnpm test -- tests/testing/intelligent-test-selection.test.ts

# 3d. 統合最適化システム (Phase 3.3) ✨ **NEW**
pnpm test -- tests/optimization/system-integration.test.ts

# 4. コード生成
pnpm run mcp:code

# 5. 品質検証
pnpm run verify:all

# 6. デプロイ・運用
pnpm run operate:server
```

### 最小出力サンプル（日本語）
- Intent（JSON抜粋）
```
{ "requirements": 15, "stories": 12, "next": ["Phase 2", "Domain model"] }
```
- Verify（CI 1行要約）
```
• CI: ✅ tests 124/124, coverage 84% (≥80), typecov 66% (baseline 65); a11y 96 (≥95), perf 78 (≥75)
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
pnpm run intent-agent
```

#### 直接実行（開発・テスト用）
```text
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
```text
const requirements = await agent.extractFromNaturalLanguage(`
  システムは以下の機能を提供する必要がある：
  - ユーザー認証（JWT方式）
  - 商品検索（フィルタリング機能付き）
  - ショッピングカート
  - 決済処理（Stripe連携）
`);
```

#### 2. 曖昧性の検出
```text
const ambiguities = await agent.detectAmbiguities([
  {
    type: 'text',
    content: 'システムは高速で安全である必要がある'
  }
]);
// → 「高速」「安全」の具体的定義が必要と判定
```

#### 3. ドメインモデルの生成
```text
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
