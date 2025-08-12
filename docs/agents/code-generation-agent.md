# Code Generation Agent

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

```typescript
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

```bash
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

```bash
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

```typescript
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

```typescript
{
  targetResponseTime: 100,       // Target response time in ms
  targetMemoryUsage: 512,        // Target memory in MB
  targetCPUUsage: 80            // Target CPU usage percentage
}
```

## Examples

### Generate API from OpenAPI

```typescript
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

```typescript
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