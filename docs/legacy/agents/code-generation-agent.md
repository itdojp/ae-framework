---
docRole: narrative
lastVerified: '2026-03-12'
---

# Code Generation Agent

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

## Overview

The Code Generation Agent is a Phase 4 component of the ae-framework that automatically generates implementation code from tests and specifications. It follows the TDD principle of writing minimal code to make tests pass, then refactoring for quality.

## Features

### Core Capabilities

1. **Test-Driven Code Generation**
   - Analyzes test files to understand requirements
   - Generates minimal implementation to pass tests
   - Supports multiple languages (TypeScript, JavaScript, Python, Go, Rust)

2. **API Generation from OpenAPI**
   - Creates complete API implementations from OpenAPI specs
   - Generates route handlers, models, and middleware
   - Supports multiple frameworks (Fastify, Express, Koa)

3. **Design Pattern Application**
   - Applies common design patterns (Singleton, Factory, Observer, etc.)
   - Refactors existing code to use patterns
   - Maintains code consistency

4. **Performance Optimization**
   - Identifies performance bottlenecks
   - Applies optimizations automatically
   - Provides before/after benchmarks

5. **Security Enhancement**
   - Adds authentication (JWT, OAuth, Basic)
   - Implements authorization (RBAC, ABAC)
   - Includes encryption and rate limiting

6. **Database Layer Generation**
   - Creates entities and repositories
   - Generates migrations
   - Supports multiple ORMs (TypeORM, Prisma, Sequelize)

## Usage

### As a Standalone Agent

```typescript no-doctest
import { CodeGenerationAgent } from './src/agents/code-generation-agent';

const agent = new CodeGenerationAgent();

// Generate code from tests
const result = await agent.generateCodeFromTests({
  tests: [
    {
      path: 'tests/calculator.test.ts',
      content: '...',
      type: 'unit'
    }
  ],
  language: 'typescript',
  architecture: {
    pattern: 'hexagonal'
  }
});

console.log('Generated files:', result.files);
console.log('Test coverage:', result.coverage);
```

### As an MCP Server

```bash no-doctest
# Start the MCP server
npm run mcp:code

# The server will be available on port 3004
```

### MCP Tools Available

1. **generate_code_from_tests** - Generate implementation from test files
2. **generate_api_from_openapi** - Create API from OpenAPI specification
3. **apply_design_patterns** - Apply patterns to existing code
4. **optimize_performance** - Optimize code for performance
5. **add_security_features** - Add security layers to code
6. **generate_error_handling** - Add comprehensive error handling
7. **generate_data_access_layer** - Create database access layer
8. **refactor_code** - Improve code quality through refactoring
9. **validate_code_against_tests** - Ensure code passes all tests
10. **suggest_code_improvements** - Get improvement suggestions

## Integration with ae-framework

### Phase 4: Code Generation

The Code Generation Agent operates in Phase 4 of the ae-framework workflow:

```
Phase 1: Intent → Phase 2: Formal → Phase 3: Tests → **Phase 4: Code** → Phase 5: Verify → Phase 6: Operate
```

### Workflow Example

```bash no-doctest
# 1. Generate tests from requirements (Phase 3)
npm run agent:test

# 2. Generate code from tests (Phase 4)
npm run agent:code

# 3. Verify implementation (Phase 5)
npm test
```

## Architecture Patterns Supported

- **MVC** - Model-View-Controller
- **Hexagonal** - Ports and Adapters
- **Clean Architecture** - Uncle Bob's Clean Architecture
- **DDD** - Domain-Driven Design
- **Microservice** - Microservice architecture

## Best Practices

1. **Start with Tests**: Always generate or write tests before generating code
2. **Iterative Refinement**: Generate minimal code first, then refactor
3. **Pattern Selection**: Choose architecture patterns based on project complexity
4. **Security First**: Always include security features in generated code
5. **Performance Monitoring**: Use benchmarks to validate optimizations

## Configuration

### Code Generation Options

```typescript no-doctest
{
  language: 'typescript',        // Target language
  framework: 'fastify',          // Framework for API generation
  architecture: {
    pattern: 'hexagonal',        // Architecture pattern
    layers: [...]                // Custom layers
  },
  style: {
    naming: 'camelCase',         // Naming convention
    indentation: 'spaces',       // Indentation style
    indentSize: 2                // Indent size
  }
}
```

### Performance Metrics

```typescript no-doctest
{
  targetResponseTime: 100,       // Target response time in ms
  targetMemoryUsage: 512,        // Target memory in MB
  targetCPUUsage: 80            // Target CPU usage percentage
}
```

## Examples

### Generate API from OpenAPI

```typescript no-doctest
const openApiSpec = fs.readFileSync('api.yaml', 'utf-8');

const result = await agent.generateFromOpenAPI(openApiSpec, {
  framework: 'fastify',
  database: 'postgres',
  includeValidation: true,
  includeAuth: true
});

// Write generated files
for (const file of result.files) {
  fs.writeFileSync(file.path, file.content);
}
```

### Refactor Existing Code

```typescript no-doctest
const code = fs.readFileSync('src/legacy.ts', 'utf-8');

const result = await agent.refactorCode(code, {
  reduceComplexity: true,
  improveDRY: true,
  improveNaming: true,
  extractMethods: true,
  introducePatterns: ['repository', 'factory']
});

console.log('Refactored code:', result.refactoredCode);
console.log('Changes made:', result.changes);
console.log('Metrics:', result.metrics);
```

## Troubleshooting

### Common Issues

1. **Tests Not Passing**: Ensure test files follow standard testing patterns
2. **Pattern Conflicts**: Some patterns may conflict; apply them sequentially
3. **Performance Regression**: Review optimizations and benchmark results
4. **ORM Compatibility**: Ensure database schema matches ORM requirements

## Future Enhancements

- Support for more programming languages
- AI-powered code optimization
- Integration with CI/CD pipelines
- Real-time collaboration features
- Visual code generation interface

---

## Japanese

**コード生成エージェント**

## 概要

コード生成エージェントは、テストと仕様から実装コードを自動生成するae-frameworkのフェーズ4コンポーネントです。テストを通すための最小限のコードを書き、その後品質のためにリファクタリングするTDDの原則に従います。

## 機能

### 中核機能

1. **テスト駆動コード生成**
   - テストファイルを分析して要件を理解
   - テストを通す最小限の実装を生成
   - 複数言語をサポート（TypeScript、JavaScript、Python、Go、Rust）

2. **OpenAPIからのAPI生成**
   - OpenAPI仕様から完全なAPI実装を作成
   - ルートハンドラー、モデル、ミドルウェアを生成
   - 複数フレームワークをサポート（Fastify、Express、Koa）

3. **デザインパターンの適用**
   - 一般的なデザインパターンを適用（Singleton、Factory、Observer等）
   - 既存コードをパターンを使用するようリファクタリング
   - コードの一貫性を維持

4. **パフォーマンス最適化**
   - パフォーマンスボトルネックを特定
   - 最適化を自動適用
   - 最適化前後のベンチマークを提供

### 対応技術

#### フロントエンド
- React、Vue、Angular
- TypeScript、JavaScript
- CSS、SCSS、Styled Components

#### バックエンド
- Node.js（Express、Fastify、Koa）
- Python（FastAPI、Django、Flask）
- Go（Gin、Echo、Chi）
- Rust（Actix、Warp、Axum）

#### データベース
- PostgreSQL、MySQL、SQLite
- MongoDB、Redis
- Prisma、TypeORM、Sequelize

## 使用方法

### MCPサーバーとして実行

```bash no-doctest
npm run code-generation-agent
```

### 直接統合

```typescript no-doctest
import { CodeGenerationAgent } from './src/agents/code-generation-agent.js';

const agent = new CodeGenerationAgent();

// テストから実装を生成
const testFile = 'src/tests/user.test.ts';
const implementation = await agent.generateFromTests(testFile, {
  language: 'typescript',
  framework: 'fastify',
  includeValidation: true
});

console.log('生成されたコード:', implementation);
```

## 生成例

### API生成例

```typescript no-doctest
// OpenAPI仕様から生成されたFastifyルート
export async function createUser(
  request: FastifyRequest<{ Body: CreateUserRequest }>,
  reply: FastifyReply
) {
  const { name, email } = request.body;
  
  // バリデーション
  if (!name || !email) {
    return reply.status(400).send({ error: 'nameとemailは必須です' });
  }
  
  try {
    const user = await userService.create({ name, email });
    return reply.status(201).send(user);
  } catch (error) {
    return reply.status(500).send({ error: 'ユーザー作成に失敗しました' });
  }
}
```

### デザインパターン適用例

```typescript no-doctest
// Factoryパターンを適用
export class DatabaseConnectionFactory {
  private static instance: DatabaseConnectionFactory;
  
  private constructor() {}
  
  public static getInstance(): DatabaseConnectionFactory {
    if (!DatabaseConnectionFactory.instance) {
      DatabaseConnectionFactory.instance = new DatabaseConnectionFactory();
    }
    return DatabaseConnectionFactory.instance;
  }
  
  public createConnection(type: 'postgres' | 'mysql' | 'sqlite'): Connection {
    switch (type) {
      case 'postgres':
        return new PostgresConnection();
      case 'mysql':
        return new MySQLConnection();
      case 'sqlite':
        return new SQLiteConnection();
      default:
        throw new Error(`サポートされていないデータベースタイプ: ${type}`);
    }
  }
}
```

## 設定オプション

### 基本設定

```typescript no-doctest
interface CodeGenerationConfig {
  language: 'typescript' | 'javascript' | 'python' | 'go' | 'rust';
  framework?: string;
  database?: 'postgres' | 'mysql' | 'sqlite' | 'mongodb';
  includeValidation: boolean;
  includeAuth: boolean;
  codeStyle: {
    quotes: 'single' | 'double';
    semicolons: boolean;
    indentation: 'tabs' | 'spaces';
    indentSize: number;
  };
}
```

### パフォーマンス指標

```typescript no-doctest
{
  targetResponseTime: 100,       // ターゲット応答時間（ms）
  targetMemoryUsage: 512,        // ターゲットメモリ（MB）
  targetCPUUsage: 80            // ターゲットCPU使用率（%）
}
```

## 実用例

### OpenAPIからのAPI生成

```typescript no-doctest
const openApiSpec = fs.readFileSync('api.yaml', 'utf-8');

const result = await agent.generateFromOpenAPI(openApiSpec, {
  framework: 'fastify',
  database: 'postgres',
  includeValidation: true,
  includeAuth: true
});

// 生成されたファイルを書き込み
for (const file of result.files) {
  fs.writeFileSync(file.path, file.content);
}
```

### 既存コードのリファクタリング

```typescript no-doctest
const code = fs.readFileSync('src/legacy.ts', 'utf-8');

const result = await agent.refactorCode(code, {
  reduceComplexity: true,
  improveDRY: true,
  improveNaming: true,
  extractMethods: true,
  introducePatterns: ['repository', 'factory']
});

console.log('リファクタリング済みコード:', result.refactoredCode);
console.log('行った変更:', result.changes);
console.log('指標:', result.metrics);
```

## トラブルシューティング

### よくある問題

1. **テストが通らない**: テストファイルが標準的なテストパターンに従っていることを確認
2. **パターンの競合**: 一部のパターンが競合する可能性があるため、順次適用
3. **パフォーマンス低下**: 最適化をレビューし、ベンチマーク結果を確認
4. **ORM互換性**: データベーススキーマがORM要件と一致することを確認

## 将来の拡張

- より多くのプログラミング言語のサポート
- AI駆動のコード最適化
- CI/CDパイプラインとの統合
- リアルタイムコラボレーション機能
- ビジュアルコード生成インターフェース