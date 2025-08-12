# Verify Agent Documentation

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

```bash
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
```json
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
- `specs/openapi/api.yaml`
- `specs/openapi/api.json`
- `specs/asyncapi/events.yaml`
- `specs/formal/tla+/*.tla`
- `specs/graphql/schema.graphql`

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

```yaml
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

```json
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

```json
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

```typescript
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

```typescript
interface CoverageReport {
  line: number;        // Line coverage percentage
  branch: number;      // Branch coverage percentage
  function: number;    // Function coverage percentage
  statement: number;   // Statement coverage percentage
  uncoveredFiles: string[];
}
```

### Quality Metrics

```typescript
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

```bash
DEBUG=verify-agent npm run verify:server
```

Use verbose output for detailed information:

```bash
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