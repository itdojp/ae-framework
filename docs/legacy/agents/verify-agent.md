---
docRole: narrative
lastVerified: '2026-03-12'
---

# Verify Agent Documentation

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

## Overview

The Verify Agent is a comprehensive verification and quality assurance system for Phase 5 of the ae-framework. It provides automated verification capabilities including testing, coverage analysis, code quality checks, security scanning, and compliance validation.

## Architecture

The Verify Agent consists of two main components:

1. **Core Agent (`VerifyAgent`)**: Located at `src/agents/verify-agent.ts`
2. **MCP Server Wrapper (`VerifyMCPServer`)**: Located at `src/mcp-server/verify-server.ts`

The MCP server exposes the agent's capabilities as tools that can be used by AI assistants and other systems.

## Features

### Core Verification Types

- **Tests**: Unit, integration, e2e, property-based, and contract tests
- **Coverage**: Line, branch, function, and statement coverage analysis
- **Linting**: Code style and quality checks using ESLint
- **Type Checking**: TypeScript type validation
- **Security**: Vulnerability scanning and dependency auditing
- **Performance**: Benchmarking and load testing
- **Accessibility**: API accessibility compliance checks
- **Contracts**: API contract verification (PACT)
- **Specifications**: OpenAPI, AsyncAPI, GraphQL, TLA+ validation
- **Mutations**: Mutation testing for test quality assessment

### Quality Metrics

- Cyclomatic complexity
- Maintainability index
- Reliability rating
- Security rating
- Performance rating
- Testability rating

### Traceability

- Requirements to code traceability
- Test coverage mapping
- Specification compliance tracking
- Gap analysis and recommendations

## Usage

### Command Line Scripts

The following npm scripts are available:

```bash no-doctest
# Start MCP server
npm run verify:server

# Run all tests
npm run verify:tests

# Run quality checks (lint + build)
npm run verify:quality

# Run security audit
npm run verify:security

# Run complete verification suite
npm run verify:all

# Initialize verify agent
npm run verify:full
```

### MCP Tools

When running as an MCP server, the following tools are available:

#### `run_full_verification`
Run comprehensive verification suite including all test types, coverage, linting, security, and quality checks.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `verificationTypes` (required): Array of verification types to run
- `strictMode` (optional): Stop verification on first failure (default: false)

**Example:**
```json no-doctest
{
  "projectPath": "/path/to/project",
  "verificationTypes": ["tests", "coverage", "linting", "security"],
  "strictMode": true
}
```

#### `run_tests`
Run all types of tests (unit, integration, e2e, property, contract).

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `testTypes` (optional): Types of tests to run (default: ["unit", "integration", "e2e"])

#### `check_coverage`
Analyze code coverage and generate detailed coverage report.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `threshold` (optional): Minimum coverage threshold percentage (default: 80)

#### `run_linting`
Run ESLint and other linting tools for code quality checks.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `fix` (optional): Automatically fix fixable issues (default: false)

#### `run_type_checking`
Run TypeScript type checking.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `strict` (optional): Enable strict type checking (default: true)

#### `run_security_scan`
Run security vulnerability scanning including dependency checks.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `includeDevDeps` (optional): Include development dependencies in scan (default: true)

#### `run_performance_tests`
Run performance benchmarks and load tests.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `duration` (optional): Test duration in seconds (default: 30)

#### `check_accessibility`
Run accessibility checks for APIs and interfaces.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `standards` (optional): Accessibility standards to check against (default: ["WCAG2.1"])

#### `verify_contracts`
Verify API contracts and consumer compatibility.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `contractPath` (optional): Path to contract files

#### `verify_specifications`
Validate specifications (OpenAPI, AsyncAPI, GraphQL, TLA+).

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `specPaths` (optional): Paths to specification files

#### `run_mutation_tests`
Run mutation testing to assess test quality.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `threshold` (optional): Minimum mutation score threshold (default: 80)

#### `generate_traceability_matrix`
Generate traceability matrix linking requirements to tests and code.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `outputFormat` (optional): Output format for the matrix ("json", "html", "csv", default: "json")

#### `get_quality_metrics`
Calculate comprehensive quality metrics.

**Parameters:**
- `projectPath` (required): Path to the project root directory
- `includeHistory` (optional): Include historical trend data (default: false)

## Configuration

### File Discovery

The Verify Agent automatically discovers files in the following locations:

**Source Files:**
- `src/**/*.ts`
- `src/**/*.js`
- `src/**/*.tsx`
- `src/**/*.jsx`

**Test Files:**
- `tests/**/*.(test|spec).ts`
- `test/**/*.(test|spec).ts`
- `__tests__/**/*.(test|spec).ts`
- `src/**/*.(test|spec).ts`
- `tests/**/*.pbt.test.ts` (property-based tests)

**Specifications:**
- `spec/openapi/api.yaml`
- `spec/openapi/api.json`
- `spec/asyncapi/events.yaml`
- `spec/formal/tla+/*.tla`
- `spec/graphql/schema.graphql`

### Test Type Detection

Tests are automatically categorized based on file naming patterns:

- **Unit Tests**: Default for `*.test.ts` and `*.spec.ts`
- **Integration Tests**: Files containing `integration` or `int.`
- **E2E Tests**: Files containing `e2e` or `end-to-end`
- **Property Tests**: Files containing `pbt` or `property`
- **Contract Tests**: Files containing `contract` or `pact`

## Integration

### CI/CD Pipeline

Add verification steps to your CI/CD pipeline:

```yaml no-doctest
# GitHub Actions example
- name: Run Verification Suite
  run: npm run verify:all

# Or run specific checks
- name: Run Tests
  run: npm run verify:tests

- name: Check Security
  run: npm run verify:security

- name: Quality Gates
  run: npm run verify:quality
```

### Pre-commit Hooks

Configure pre-commit hooks to run verification:

```json no-doctest
{
  "husky": {
    "hooks": {
      "pre-commit": "npm run verify:quality",
      "pre-push": "npm run verify:tests"
    }
  }
}
```

### IDE Integration

The MCP server can be integrated with Claude Desktop and other MCP-compatible clients:

```json no-doctest
{
  "mcpServers": {
    "ae-framework-verify": {
      "command": "node",
      "args": ["dist/mcp-server/verify-server.js"],
      "cwd": "/path/to/ae-framework"
    }
  }
}
```

## Output Formats

### Verification Results

All verification operations return structured results:

```typescript no-doctest
interface VerificationResult {
  passed: boolean;
  results: VerificationCheck[];
  coverage: CoverageReport;
  metrics: QualityMetrics;
  issues: Issue[];
  suggestions: string[];
  traceability: TraceabilityMatrix;
}
```

### Coverage Report

```typescript no-doctest
interface CoverageReport {
  line: number;        // Line coverage percentage
  branch: number;      // Branch coverage percentage
  function: number;    // Function coverage percentage
  statement: number;   // Statement coverage percentage
  uncoveredFiles: string[];
}
```

### Quality Metrics

```typescript no-doctest
interface QualityMetrics {
  complexity: number;      // Cyclomatic complexity
  maintainability: number; // Maintainability index
  reliability: number;     // Reliability rating
  security: number;        // Security rating
  performance: number;     // Performance rating
  testability: number;     // Testability rating
}
```

### Traceability Matrix

The traceability matrix can be exported in multiple formats:

- **JSON**: Structured data for programmatic use
- **HTML**: Visual report with styling and filtering
- **CSV**: Spreadsheet-compatible format

## Best Practices

### Verification Strategy

1. **Incremental Verification**: Run fast checks first (linting, type checking)
2. **Parallel Execution**: Run independent checks concurrently
3. **Fail Fast**: Use strict mode for critical pipelines
4. **Comprehensive Coverage**: Include all verification types for releases

### Quality Gates

Set up quality gates with appropriate thresholds:

- **Coverage**: Minimum 80% line and branch coverage
- **Security**: Zero critical and high-severity vulnerabilities
- **Type Safety**: Zero type errors in strict mode
- **Code Quality**: Maximum cyclomatic complexity of 10
- **Mutation Score**: Minimum 80% mutation kill rate

### Monitoring

Track verification metrics over time:

- Coverage trends
- Security vulnerability counts
- Code quality scores
- Test execution times
- Mutation testing results

## Troubleshooting

### Common Issues

**MCP Server Connection Issues:**
- Ensure Node.js and npm dependencies are installed
- Check that the server process has proper permissions
- Verify the MCP client configuration

**Test Discovery Problems:**
- Check file naming patterns match expected conventions
- Ensure test files are in recognized directories
- Verify file extensions are supported

**Coverage Reporting:**
- Ensure test files import the code being tested
- Check that source files are in the expected locations
- Verify coverage tools are properly configured

**Performance Issues:**
- Use selective verification types for faster feedback
- Enable parallel test execution
- Consider test splitting for large suites

### Debugging

Enable debug logging:

```bash no-doctest
DEBUG=verify-agent npm run verify:server
```

Use verbose output for detailed information:

```bash no-doctest
npm run verify:all -- --verbose
```

## Contributing

### Adding New Verification Types

1. Extend the `VerificationType` union type
2. Add handler method to `VerifyAgent` class
3. Update the `runVerification` method switch statement
4. Add corresponding MCP tool in `VerifyMCPServer`
5. Update documentation and tests

### Extending File Discovery

Modify the `loadCodeFiles`, `loadTestFiles`, or `loadSpecifications` methods in the MCP server to support additional file types or locations.

### Custom Quality Metrics

Implement custom metrics by extending the `calculateQualityMetrics` method with additional analysis tools and frameworks.

## Dependencies

- **Core Dependencies**: TypeScript, Node.js
- **Testing**: Vitest, Cucumber, Fast-check, Stryker
- **Quality**: ESLint, TypeScript compiler
- **MCP**: @modelcontextprotocol/sdk
- **Security**: npm audit (built-in)

## License

This project is part of the ae-framework and follows the same licensing terms.

---

## Japanese

**検証エージェント ドキュメント**

## 概要

検証エージェントは、ae-frameworkのフェーズ5のための包括的な検証・品質保証システムです。テスト、カバレッジ分析、コード品質チェック、セキュリティスキャン、コンプライアンス検証などの自動検証機能を提供します。

## アーキテクチャ

検証エージェントは2つの主要コンポーネントで構成されます：

1. **コアエージェント (`VerifyAgent`)**: `src/agents/verify-agent.ts` に配置
2. **MCPサーバーラッパー (`VerifyMCPServer`)**: `src/mcp-server/verify-server.ts` に配置

MCPサーバーは、AIアシスタントや他のシステムで使用できるツールとしてエージェントの機能を公開します。

## 機能

### 中核検証タイプ

- **テスト**: ユニット、統合、e2e、プロパティベース、契約テスト
- **カバレッジ**: ライン、ブランチ、関数、ステートメントカバレッジ分析
- **リント**: ESLintを使用したコードスタイルと品質チェック
- **型チェック**: TypeScript型検証
- **セキュリティ**: 脆弱性スキャンと依存関係監査
- **パフォーマンス**: ベンチマークと負荷テスト
- **アクセシビリティ**: APIアクセシビリティコンプライアンスチェック
- **契約**: API契約検証（PACT）
- **仕様**: OpenAPI、AsyncAPI、GraphQL、TLA+検証
- **ミューテーション**: テスト品質評価のためのミューテーションテスト

### 包括的検証サポート

```typescript no-doctest
interface VerificationRequest {
  projectPath: string;
  verificationTypes: VerificationType[];
  options?: VerificationOptions;
}

type VerificationType = 
  | 'tests'
  | 'coverage'
  | 'linting'
  | 'type-checking'
  | 'security'
  | 'performance'
  | 'accessibility'
  | 'contracts'
  | 'specifications'
  | 'mutations';
```

## 使用方法

### MCPサーバーとして実行

```bash no-doctest
npm run verify-agent
```

### 直接統合

```typescript no-doctest
import { VerifyAgent } from './src/agents/verify-agent.js';

const agent = new VerifyAgent();

const result = await agent.verifyProject('./my-project', {
  verificationTypes: ['tests', 'coverage', 'linting', 'security'],
  options: {
    testPattern: '**/*.test.ts',
    coverageThreshold: 80,
    strictLinting: true
  }
});

console.log('検証結果:', result);
```

## 設定オプション

### テスト設定

```typescript no-doctest
interface TestOptions {
  pattern: string;              // テストファイルパターン
  timeout: number;              // テストタイムアウト（ms）
  parallel: boolean;            // 並列実行
  bail: boolean;               // 最初の失敗で停止
  coverage: {
    threshold: number;          // カバレッジ閾値（%）
    includeUntested: boolean;   // 未テストファイルを含める
  };
}
```

### セキュリティ設定

```typescript no-doctest
interface SecurityOptions {
  auditLevel: 'low' | 'moderate' | 'high' | 'critical';
  excludeDevDependencies: boolean;
  ignoreVulnerabilities: string[];  // 無視する脆弱性ID
}
```

## 検証結果例

### 基本検証結果

```typescript no-doctest
interface VerificationResult {
  overall: 'passed' | 'failed' | 'warning';
  timestamp: Date;
  projectPath: string;
  results: {
    tests: TestResult;
    coverage: CoverageResult;
    linting: LintingResult;
    security: SecurityResult;
    // ... その他の検証タイプ
  };
  summary: {
    totalChecks: number;
    passed: number;
    failed: number;
    warnings: number;
  };
}
```

### テスト結果

```json no-doctest
{
  "tests": {
    "status": "passed",
    "summary": {
      "total": 45,
      "passed": 43,
      "failed": 2,
      "skipped": 0,
      "duration": 2341
    },
    "coverage": {
      "lines": 87.5,
      "branches": 82.1,
      "functions": 90.3,
      "statements": 86.8
    }
  }
}
```

### セキュリティ結果

```json no-doctest
{
  "security": {
    "status": "warning",
    "vulnerabilities": {
      "low": 2,
      "moderate": 1,
      "high": 0,
      "critical": 0
    },
    "details": [
      {
        "severity": "moderate",
        "package": "example-lib",
        "version": "1.2.3",
        "vulnerability": "CVE-2023-12345",
        "recommendation": "バージョン1.2.4以上にアップグレード"
      }
    ]
  }
}
```

## MCPツール

### 利用可能なツール

1. **verify_project**: プロジェクト全体の包括的検証
2. **run_tests**: テスト実行
3. **analyze_coverage**: カバレッジ分析
4. **check_quality**: コード品質チェック
5. **security_audit**: セキュリティ監査
6. **validate_specifications**: 仕様検証

### ツール使用例

```typescript no-doctest
// MCPクライアントから使用
const result = await mcpClient.callTool('verify_project', {
  projectPath: '/path/to/project',
  verificationTypes: ['tests', 'coverage', 'security'],
  options: {
    testPattern: '**/*.test.ts',
    coverageThreshold: 80
  }
});
```

## ベストプラクティス

### 段階的検証

1. **開発中**: 基本テストとリント
2. **プルリクエスト**: 全カバレッジと型チェック
3. **リリース前**: セキュリティとパフォーマンステスト
4. **本番**: 契約とコンプライアンステスト

### 継続的統合

```yaml no-doctest
# GitHub Actionsでの使用例
- name: AE Framework検証
  run: |
    npm run verify-agent -- \
      --types tests,coverage,security \
      --coverage-threshold 85 \
      --security-level moderate
```

## トラブルシューティング

### よくある問題

1. **テスト失敗**: テストファイルパターンと設定を確認
2. **カバレッジ不足**: テストカバレッジを向上、閾値を調整
3. **セキュリティ警告**: 依存関係を更新、脆弱性を修正
4. **型エラー**: TypeScript設定とコードを確認

### デバッグ

```bash no-doctest
# 詳細ログで実行
DEBUG=verify-agent npm run verify-agent

# 特定の検証タイプのみ実行
npm run verify-agent -- --types tests --verbose
```

## 拡張

### カスタム検証器の追加

```typescript no-doctest
// カスタム検証器の実装
class CustomSecurityVerifier implements Verifier {
  async verify(options: VerificationOptions): Promise<VerificationResult> {
    // カスタムセキュリティチェックロジック
    return {
      status: 'passed',
      details: '実装されたセキュリティチェック'
    };
  }
}
```

### ファイル検出の拡張

`loadCodeFiles`、`loadTestFiles`、または `loadSpecifications` メソッドを変更して、追加のファイルタイプや場所をサポートします。

### カスタム品質指標

追加の分析ツールとフレームワークで `calculateQualityMetrics` メソッドを拡張して、カスタム指標を実装します。

## 依存関係

- **中核依存関係**: TypeScript、Node.js
- **テスト**: Vitest、Cucumber、Fast-check、Stryker
- **品質**: ESLint、TypeScriptコンパイラ
- **MCP**: @modelcontextprotocol/sdk
- **セキュリティ**: npm audit（ビルトイン）

## ライセンス

このプロジェクトはae-frameworkの一部であり、同じライセンス条項に従います。