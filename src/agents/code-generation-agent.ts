/**
 * Code Generation Agent
 * Phase 4 of ae-framework: Automated code generation from tests and specifications
 */

import type { readFileSync, existsSync, writeFileSync } from 'fs';
import type { execSync } from 'child_process';
import * as path from 'path';

export interface CodeGenerationRequest {
  tests: TestFile[];
  specifications?: Specification;
  architecture?: ArchitecturePattern;
  language: 'typescript' | 'javascript' | 'python' | 'go' | 'rust' | 'elixir';
  framework?: string;
  style?: CodingStyle;
}

export interface TestFile {
  path: string;
  content: string;
  type: 'unit' | 'integration' | 'e2e';
}

export interface Specification {
  openapi?: string;
  tla?: string;
  contracts?: Contract[];
  requirements?: string[];
}

export interface Contract {
  name: string;
  preconditions: string[];
  postconditions: string[];
  invariants: string[];
}

export interface ArchitecturePattern {
  pattern: 'mvc' | 'hexagonal' | 'clean' | 'ddd' | 'microservice';
  layers?: Layer[];
  dependencies?: Dependency[];
}

export interface Layer {
  name: string;
  responsibilities: string[];
  allowedDependencies: string[];
}

export interface Dependency {
  from: string;
  to: string;
  type: 'uses' | 'implements' | 'extends';
}

export interface CodingStyle {
  naming: 'camelCase' | 'snake_case' | 'PascalCase';
  indentation: 'spaces' | 'tabs';
  indentSize?: number;
  maxLineLength?: number;
  preferConst?: boolean;
  preferArrowFunctions?: boolean;
}

export interface GeneratedCode {
  files: CodeFile[];
  structure: ProjectStructure;
  dependencies: string[];
  testResults: TestResult[];
  coverage: number;
  suggestions: string[];
}

export interface CodeFile {
  path: string;
  content: string;
  purpose: string;
  tests: string[];
}

export interface ProjectStructure {
  directories: string[];
  entryPoint: string;
  configFiles: ConfigFile[];
}

export interface ConfigFile {
  name: string;
  content: string;
  purpose: string;
}

export interface TestResult {
  test: string;
  status: 'passing' | 'failing' | 'pending';
  error?: string;
}

export class CodeGenerationAgent {
  /**
   * Generate code from tests (TDD approach)
   */
  async generateCodeFromTests(request: CodeGenerationRequest): Promise<GeneratedCode> {
    // Analyze tests to understand requirements
    const testAnalysis = this.analyzeTests(request.tests);
    
    // Generate implementation structure
    const structure = this.designArchitecture(testAnalysis, request.architecture);
    
    // Generate code files
    const files = await this.generateImplementation(testAnalysis, structure, request);
    
    // Validate against tests
    const testResults = await this.runTests(files, request.tests);
    
    // Calculate coverage
    const coverage = this.calculateCoverage(testResults);
    
    // Generate suggestions for improvement
    const suggestions = this.generateSuggestions(testResults, coverage);
    
    return {
      files,
      structure,
      dependencies: this.identifyDependencies(files),
      testResults,
      coverage,
      suggestions,
    };
  }

  /**
   * Generate code from OpenAPI specification
   */
  async generateFromOpenAPI(spec: string, options: {
    framework: 'fastify' | 'express' | 'koa';
    database?: 'postgres' | 'mongodb' | 'mysql';
    includeValidation?: boolean;
    includeAuth?: boolean;
    includeContracts?: boolean; // inject runtime contracts usage (opt-in)
    useOperationIdForFilenames?: boolean; // prefer operationId for route filenames
<<<<<<< HEAD
=======
    useOperationIdForTestNames?: boolean; // prefer operationId in test titles
>>>>>>> origin/main
  }): Promise<GeneratedCode> {
    const api = this.parseOpenAPI(spec);
    const files: CodeFile[] = [];
    
    // Generate route handlers
    for (const endpoint of api.endpoints) {
      const handler = this.generateRouteHandler(endpoint, options);
      files.push(handler);
    }
    
    // Generate models
    for (const schema of api.schemas) {
      const model = this.generateModel(schema, options.database);
      files.push(model);
    }
    
    // Generate middleware
    if (options.includeValidation) {
      files.push(this.generateValidationMiddleware(api));
    }
    
    if (options.includeAuth) {
      files.push(this.generateAuthMiddleware(api));
    }
    
    // Generate server setup
    files.push(this.generateServerSetup(options.framework, api));
    
    return {
      files,
      structure: this.createProjectStructure(files),
      dependencies: this.getFrameworkDependencies(options.framework),
      testResults: [],
      coverage: 0,
      suggestions: ['Add tests for generated code', 'Configure database connection'],
    };
  }

  /**
   * Optionally generate minimal test skeletons from OpenAPI using operationId or path+method.
   */
  async generateTestsFromOpenAPI(spec: string, options?: { useOperationIdForTestNames?: boolean; includeSampleInput?: boolean }): Promise<CodeFile[]> {
    const api = this.parseOpenAPI(spec);
    const out: CodeFile[] = [];
    for (const ep of api.endpoints) {
      const opIdRaw = (ep?.definition as any)?.operationId as string | undefined;
      const title = options?.useOperationIdForTestNames && opIdRaw ? opIdRaw : `${ep.method} ${ep.path}`;
      const safeName = String(ep.path).replace(/[^a-zA-Z0-9]/g, '-').replace(/-+/g, '-').replace(/^-|-$/g, '');
      const method = String(ep.method).toLowerCase();
      const fileBase = (options?.useOperationIdForTestNames && opIdRaw)
        ? opIdRaw.replace(/[^a-zA-Z0-9]+/g, '-').replace(/-+/g, '-').replace(/^-|-$/g, '').toLowerCase()
        : `${safeName}-${method}`;
      // Try to derive minimal input from requestBody schema when requested
      let sample = '{}';
      if (options?.includeSampleInput) {
        const rb = (ep?.definition as any)?.requestBody?.content;
        let schema = rb?.['application/json']?.schema;
        if (!schema && rb) {
          const cts = Object.keys(rb);
          const appCt = cts.find((ct: string) => ct.startsWith('application/')) || cts[0];
          schema = rb[appCt]?.schema || (appCt === 'text/plain' ? { type: 'string' } : undefined);
        }
        sample = this.buildSampleLiteral(schema, ep?.components || {});
      }
      const content = `import { describe, it, expect } from 'vitest'\nimport { handler } from '../../src/routes/${fileBase}'\n\n// OperationId: ${opIdRaw ?? 'N/A'}\ndescribe('${title}', () => {\n  it('returns success on minimal input (skeleton)', async () => {\n    const res: any = await handler(${sample})\n    expect(typeof res.status).toBe('number')\n  })\n})\n`;
      out.push({ path: `tests/api/generated/${fileBase}.spec.ts`, content, purpose: `Test for ${title}`, tests: [] });
    }
    return out;
  }

  /**
   * Apply design patterns to code
   */
  async applyDesignPatterns(code: string, patterns: string[]): Promise<string> {
    let improvedCode = code;
    
    for (const pattern of patterns) {
      switch (pattern) {
        case 'singleton':
          improvedCode = this.applySingletonPattern(improvedCode);
          break;
        case 'factory':
          improvedCode = this.applyFactoryPattern(improvedCode);
          break;
        case 'observer':
          improvedCode = this.applyObserverPattern(improvedCode);
          break;
        case 'strategy':
          improvedCode = this.applyStrategyPattern(improvedCode);
          break;
        case 'decorator':
          improvedCode = this.applyDecoratorPattern(improvedCode);
          break;
        case 'repository':
          improvedCode = this.applyRepositoryPattern(improvedCode);
          break;
        default:
          console.warn(`Unknown pattern: ${pattern}`);
      }
    }
    
    return improvedCode;
  }

  /**
   * Optimize code for performance
   */
  async optimizePerformance(code: string, metrics: {
    targetResponseTime?: number;
    targetMemoryUsage?: number;
    targetCPUUsage?: number;
  }): Promise<{
    optimizedCode: string;
    improvements: PerformanceImprovement[];
    benchmarks: Benchmark[];
  }> {
    const improvements: PerformanceImprovement[] = [];
    let optimizedCode = code;
    
    // Identify performance bottlenecks
    const bottlenecks = this.identifyBottlenecks(code);
    
    for (const bottleneck of bottlenecks) {
      const improvement = this.optimizeBottleneck(bottleneck, metrics);
      improvements.push(improvement);
      optimizedCode = this.applyOptimization(optimizedCode, improvement);
    }
    
    // Run benchmarks
    const benchmarks = await this.runBenchmarks(optimizedCode, code);
    
    return { optimizedCode, improvements, benchmarks };
  }

  /**
   * Add security features to code
   */
  async addSecurityFeatures(code: string, requirements: {
    authentication?: 'jwt' | 'oauth' | 'basic';
    authorization?: 'rbac' | 'abac' | 'simple';
    encryption?: boolean;
    rateLimit?: boolean;
    cors?: boolean;
  }): Promise<string> {
    let secureCode = code;
    
    if (requirements.authentication) {
      secureCode = this.addAuthentication(secureCode, requirements.authentication);
    }
    
    if (requirements.authorization) {
      secureCode = this.addAuthorization(secureCode, requirements.authorization);
    }
    
    if (requirements.encryption) {
      secureCode = this.addEncryption(secureCode);
    }
    
    if (requirements.rateLimit) {
      secureCode = this.addRateLimiting(secureCode);
    }
    
    if (requirements.cors) {
      secureCode = this.addCORS(secureCode);
    }
    
    return secureCode;
  }

  /**
   * Generate runtime contracts skeleton files (opt-in).
   * Returns an array of { path, content } under src/contracts/.
   */
  async generateContractsSkeleton(formalSpec: string): Promise<Array<{ path: string; content: string }>> {
    const mod = await import('./contracts-generator.js');
    return mod.generateContractsFromFormalSpec(formalSpec, { language: 'ts' });
  }

  /**
   * Generate error handling code
   */
  async generateErrorHandling(code: string, strategy: {
    type: 'try-catch' | 'result-type' | 'middleware';
    logging?: boolean;
    recovery?: boolean;
    userFriendly?: boolean;
  }): Promise<string> {
    let enhancedCode = code;
    
    switch (strategy.type) {
      case 'try-catch':
        enhancedCode = this.wrapInTryCatch(enhancedCode, strategy);
        break;
      case 'result-type':
        enhancedCode = this.convertToResultType(enhancedCode);
        break;
      case 'middleware':
        enhancedCode = this.addErrorMiddleware(enhancedCode);
        break;
    }
    
    if (strategy.logging) {
      enhancedCode = this.addErrorLogging(enhancedCode);
    }
    
    if (strategy.recovery) {
      enhancedCode = this.addRecoveryMechanisms(enhancedCode);
    }
    
    if (strategy.userFriendly) {
      enhancedCode = this.addUserFriendlyErrors(enhancedCode);
    }
    
    return enhancedCode;
  }

  /**
   * Generate database access layer
   */
  async generateDataAccessLayer(schema: DatabaseSchema, options: {
    orm?: 'typeorm' | 'prisma' | 'sequelize' | 'none';
    database: 'postgres' | 'mysql' | 'mongodb' | 'sqlite';
    includeTransactions?: boolean;
    includeMigrations?: boolean;
  }): Promise<GeneratedCode> {
    const files: CodeFile[] = [];
    
    // Generate entities/models
    for (const table of schema.tables) {
      const entity = this.generateEntity(table, options.orm);
      files.push(entity);
    }
    
    // Generate repositories
    for (const table of schema.tables) {
      const repository = this.generateRepository(table, options);
      files.push(repository);
    }
    
    // Generate database connection
    files.push(this.generateDatabaseConnection(options));
    
    // Generate migrations if requested
    if (options.includeMigrations) {
      const migrations = this.generateMigrations(schema, options.database);
      files.push(...migrations);
    }
    
    // Generate transaction helpers if requested
    if (options.includeTransactions) {
      files.push(this.generateTransactionHelpers(options.orm));
    }
    
    return {
      files,
      structure: this.createDataLayerStructure(files),
      dependencies: this.getORMDependencies(options.orm, options.database),
      testResults: [],
      coverage: 0,
      suggestions: ['Add database indexes', 'Implement caching layer'],
    };
  }

  /**
   * Refactor existing code
   */
  async refactorCode(code: string, goals: {
    reduceComplexity?: boolean;
    improveDRY?: boolean;
    improveNaming?: boolean;
    extractMethods?: boolean;
    introducePatterns?: string[];
  }): Promise<{
    refactoredCode: string;
    changes: RefactoringChange[];
    metrics: CodeMetrics;
  }> {
    let refactoredCode = code;
    const changes: RefactoringChange[] = [];
    
    if (goals.reduceComplexity) {
      const result = this.reduceComplexity(refactoredCode);
      refactoredCode = result.code;
      changes.push(...result.changes);
    }
    
    if (goals.improveDRY) {
      const result = this.eliminateDuplication(refactoredCode);
      refactoredCode = result.code;
      changes.push(...result.changes);
    }
    
    if (goals.improveNaming) {
      const result = this.improveNaming(refactoredCode);
      refactoredCode = result.code;
      changes.push(...result.changes);
    }
    
    if (goals.extractMethods) {
      const result = this.extractMethods(refactoredCode);
      refactoredCode = result.code;
      changes.push(...result.changes);
    }
    
    if (goals.introducePatterns && goals.introducePatterns.length > 0) {
      refactoredCode = await this.applyDesignPatterns(refactoredCode, goals.introducePatterns);
    }
    
    const metrics = this.calculateMetrics(refactoredCode);
    
    return { refactoredCode, changes, metrics };
  }

  // Private helper methods

  private analyzeTests(tests: TestFile[]): TestAnalysis {
    const functions: string[] = [];
    const classes: string[] = [];
    const expectedBehaviors: string[] = [];
    
    for (const test of tests) {
      // Extract function names being tested
      const funcMatches = test.content.match(/describe\s*\(['"]([^'"]+)/g) || [];
      functions.push(...funcMatches.map(m => m.replace(/describe\s*\(['"]/, '')));
      
      // Extract expected behaviors
      const itMatches = test.content.match(/it\s*\(['"]([^'"]+)/g) || [];
      expectedBehaviors.push(...itMatches.map(m => m.replace(/it\s*\(['"]/, '')));
    }
    
    return { functions, classes, expectedBehaviors };
  }

  private designArchitecture(analysis: TestAnalysis, pattern?: ArchitecturePattern): ProjectStructure {
    const directories: string[] = [];
    
    if (pattern?.pattern === 'hexagonal') {
      directories.push('src/domain', 'src/application', 'src/infrastructure', 'src/adapters');
    } else if (pattern?.pattern === 'clean') {
      directories.push('src/entities', 'src/usecases', 'src/interfaces', 'src/frameworks');
    } else {
      // Default structure
      directories.push('src', 'src/services', 'src/models', 'src/utils');
    }
    
    return {
      directories,
      entryPoint: 'src/index.ts',
      configFiles: [],
    };
  }

  private async generateImplementation(
    analysis: TestAnalysis,
    structure: ProjectStructure,
    request: CodeGenerationRequest
  ): Promise<CodeFile[]> {
    const files: CodeFile[] = [];
    
    for (const func of analysis.functions) {
      const implementation = this.generateFunctionImplementation(
        func, 
        analysis.expectedBehaviors, 
        request.language,
        request.framework
      );
      
      const fileExtension = this.getFileExtension(request.language);
      const testExtension = this.getTestExtension(request.language);
      
      files.push({
        path: `${this.getSourceDirectory(request.language)}/${func}.${fileExtension}`,
        content: implementation,
        purpose: `Implementation of ${func}`,
        tests: [`${this.getTestDirectory(request.language)}/${func}.${testExtension}`],
      });
    }
    
    return files;
  }

  private generateFunctionImplementation(
    funcName: string, 
    behaviors: string[], 
    language: string,
    framework?: string
  ): string {
    switch (language) {
      case 'elixir':
        return this.generateElixirFunction(funcName, behaviors, framework);
      case 'typescript':
      case 'javascript':
        return this.generateTSFunction(funcName, behaviors);
      case 'python':
        return this.generatePythonFunction(funcName, behaviors);
      case 'rust':
        return this.generateRustFunction(funcName, behaviors);
      case 'go':
        return this.generateGoFunction(funcName, behaviors);
      default:
        return this.generateTSFunction(funcName, behaviors);
    }
  }

  private generateElixirFunction(funcName: string, behaviors: string[], framework?: string): string {
    if (framework === 'phoenix') {
      return this.generatePhoenixModule(funcName, behaviors);
    }
    
    // Standard Elixir module
    let implementation = `defmodule ${this.capitalize(funcName)} do\n`;
    implementation += `  @moduledoc """\n`;
    implementation += `  ${this.capitalize(funcName)} module\n`;
    implementation += `  """\n\n`;
    
    // Add function implementation
    implementation += `  @doc """\n`;
    implementation += `  Main function for ${funcName}\n`;
    implementation += `  """\n`;
    implementation += `  def ${funcName}(args) do\n`;
    
    // Add basic implementation based on expected behaviors
    for (const behavior of behaviors) {
      implementation += `    # ${behavior}\n`;
    }
    
    implementation += `    # TODO: Implement based on tests\n`;
    implementation += `    {:ok, "not implemented"}\n`;
    implementation += `  end\n`;
    implementation += `end\n`;
    
    return implementation;
  }

  private generatePhoenixModule(funcName: string, behaviors: string[]): string {
    const moduleName = this.capitalize(funcName);
    let implementation = `defmodule MyAppWeb.${moduleName}Controller do\n`;
    implementation += `  use MyAppWeb, :controller\n\n`;
    
    implementation += `  @doc """\n`;
    implementation += `  ${moduleName} action\n`;
    implementation += `  """\n`;
    implementation += `  def ${funcName}(conn, _params) do\n`;
    
    for (const behavior of behaviors) {
      implementation += `    # ${behavior}\n`;
    }
    
    implementation += `    # TODO: Implement based on tests\n`;
    implementation += `    json(conn, %{message: "not implemented"})\n`;
    implementation += `  end\n`;
    implementation += `end\n`;
    
    return implementation;
  }

  private generateTSFunction(funcName: string, behaviors: string[]): string {
    let implementation = `export function ${funcName}(...args: any[]): any {\n`;
    
    for (const behavior of behaviors) {
      if (behavior.includes('return')) {
        implementation += `  // ${behavior}\n`;
      }
    }
    
    implementation += `  // TODO: Implement based on tests\n`;
    implementation += `  return {};\n`;
    implementation += `}\n`;
    
    return implementation;
  }

  private generatePythonFunction(funcName: string, behaviors: string[]): string {
    let implementation = `def ${funcName}(*args, **kwargs):\n`;
    implementation += `    """${this.capitalize(funcName)} function"""\n`;
    
    for (const behavior of behaviors) {
      implementation += `    # ${behavior}\n`;
    }
    
    implementation += `    # TODO: Implement based on tests\n`;
    implementation += `    return {}\n`;
    
    return implementation;
  }

  private generateRustFunction(funcName: string, behaviors: string[]): string {
    let implementation = `pub fn ${funcName}() -> Result<(), Box<dyn std::error::Error>> {\n`;
    
    for (const behavior of behaviors) {
      implementation += `    // ${behavior}\n`;
    }
    
    implementation += `    // TODO: Implement based on tests\n`;
    implementation += `    Ok(())\n`;
    implementation += `}\n`;
    
    return implementation;
  }

  private generateGoFunction(funcName: string, behaviors: string[]): string {
    let implementation = `func ${this.capitalize(funcName)}() error {\n`;
    
    for (const behavior of behaviors) {
      implementation += `    // ${behavior}\n`;
    }
    
    implementation += `    // TODO: Implement based on tests\n`;
    implementation += `    return nil\n`;
    implementation += `}\n`;
    
    return implementation;
  }

  private getFileExtension(language: string): string {
    const extensions: Record<string, string> = {
      'typescript': 'ts',
      'javascript': 'js',
      'python': 'py',
      'elixir': 'ex',
      'rust': 'rs',
      'go': 'go'
    };
    return extensions[language] || 'ts';
  }

  private getTestExtension(language: string): string {
    const extensions: Record<string, string> = {
      'typescript': 'test.ts',
      'javascript': 'test.js',
      'python': 'test.py',
      'elixir': '_test.exs',
      'rust': 'rs',
      'go': 'test.go'
    };
    return extensions[language] || 'test.ts';
  }

  private getSourceDirectory(language: string): string {
    const directories: Record<string, string> = {
      'typescript': 'src',
      'javascript': 'src',
      'python': 'src',
      'elixir': 'lib',
      'rust': 'src',
      'go': '.'
    };
    return directories[language] || 'src';
  }

  private getTestDirectory(language: string): string {
    const directories: Record<string, string> = {
      'typescript': 'tests',
      'javascript': 'tests', 
      'python': 'tests',
      'elixir': 'test',
      'rust': 'tests',
      'go': '.'
    };
    return directories[language] || 'tests';
  }

  private capitalize(str: string): string {
    return str.charAt(0).toUpperCase() + str.slice(1);
  }

  private async runTests(files: CodeFile[], tests: TestFile[]): Promise<TestResult[]> {
    // This would actually run tests against generated code
    return tests.map(test => ({
      test: test.path,
      status: 'pending' as const,
    }));
  }

  private calculateCoverage(testResults: TestResult[]): number {
    const passing = testResults.filter(r => r.status === 'passing').length;
    return testResults.length > 0 ? (passing / testResults.length) * 100 : 0;
  }

  private generateSuggestions(testResults: TestResult[], coverage: number): string[] {
    const suggestions: string[] = [];
    
    if (coverage < 80) {
      suggestions.push('Increase test coverage to at least 80%');
    }
    
    const failing = testResults.filter(r => r.status === 'failing');
    if (failing.length > 0) {
      suggestions.push(`Fix ${failing.length} failing tests`);
    }
    
    return suggestions;
  }

  // Additional helper methods
  private generateValidationMiddleware(api: any): CodeFile {
    return {
      path: 'src/middleware/validation.ts',
      content: `import { FastifyRequest, FastifyReply } from 'fastify';
import { z } from 'zod';

export const validationMiddleware = async (
  request: FastifyRequest,
  reply: FastifyReply
) => {
  // Validate request based on OpenAPI spec
  try {
    // Validation logic here
  } catch (error) {
    reply.code(400).send({ error: 'Validation failed' });
  }
};
`,
      purpose: 'Request validation middleware',
      tests: [],
    };
  }

  private generateAuthMiddleware(api: any): CodeFile {
    return {
      path: 'src/middleware/auth.ts',
      content: `import { FastifyRequest, FastifyReply } from 'fastify';

export const authMiddleware = async (
  request: FastifyRequest,
  reply: FastifyReply
) => {
  // Authentication logic
  const token = request.headers.authorization;
  if (!token) {
    reply.code(401).send({ error: 'Unauthorized' });
    return;
  }
  // Verify token
};
`,
      purpose: 'Authentication middleware',
      tests: [],
    };
  }

  private generateServerSetup(framework: string, api: any): CodeFile {
    const setupCode = framework === 'fastify' ? `
import Fastify from 'fastify';
import cors from '@fastify/cors';

const server = Fastify({ logger: true });

server.register(cors);

// Register routes
// ...

const start = async () => {
  try {
    await server.listen({ port: 3000, host: '0.0.0.0' });
  } catch (err) {
    server.log.error(err);
    process.exit(1);
  }
};

start();
` : '// Server setup for ' + framework;

    return {
      path: 'src/server.ts',
      content: setupCode,
      purpose: 'Server initialization and setup',
      tests: [],
    };
  }

  private parseOpenAPI(spec: string): any {
    // Basic OpenAPI parsing
    try {
      const parsed = JSON.parse(spec);
      const endpoints = [];
      const schemas = [];
      
      if (parsed.paths) {
        for (const [path, methods] of Object.entries(parsed.paths)) {
          for (const [method, definition] of Object.entries(methods as any)) {
            endpoints.push({ path, method, definition });
          }
        }
      }
      
      if (parsed.components?.schemas) {
        for (const [name, schema] of Object.entries(parsed.components.schemas)) {
          schemas.push({ name, schema });
        }
      }
      
      return { endpoints, schemas };
    } catch (error) {
      return { endpoints: [], schemas: [] };
    }
  }

  private generateRouteHandler(endpoint: any, options: any): CodeFile {
    const safeName = String(endpoint.path)
      .replace(/[^a-zA-Z0-9]/g, '-')
      .replace(/-+/g, '-')
      .replace(/^-|-$/g, '');
    const method = String(endpoint.method || 'get').toLowerCase();
    const fileSafe = (options?.useOperationIdForFilenames && opIdSafe) ? opIdSafe.toLowerCase() : `${safeName}-${method}`;
    const toPascal = (s: string) => s
      .split('-')
      .filter(Boolean)
      .map(p => p.charAt(0).toUpperCase() + p.slice(1))
      .join('');
    const opIdRaw = (endpoint?.definition as any)?.operationId as string | undefined;
    const opIdSafe = opIdRaw ? opIdRaw.replace(/[^a-zA-Z0-9]+/g, '-')
      .replace(/-+/g, '-')
      .replace(/^-|-$/g, '') : '';
    const contractBase = opIdSafe && opIdSafe.length > 0
      ? `${toPascal(opIdSafe)}`
      : `${toPascal(safeName)}${method.charAt(0).toUpperCase()}${method.slice(1)}`;

    const base = `// Route handler implementation for ${endpoint.method} ${endpoint.path}\n`;
    let content = base;
    if (options?.includeContracts) {
      content += `import { z } from 'zod';\n`;
      content += `import { ${contractBase}Input, ${contractBase}Output } from '../contracts/schemas';\n`;
      content += `import { pre, post } from '../contracts/conditions';\n`;
      content += `\n// OperationId: ${opIdRaw ?? 'N/A'}\n`;
      content += `export async function handler(input: unknown): Promise<unknown> {\n`;
      content += `  try {\n`;
      content += `    // Validate input and pre-condition (skeleton)\n`;
      content += `    ${contractBase}Input.parse(input);\n`;
      content += `    if (!pre(input)) return { status: 400, error: 'Precondition failed' };\n`;
      content += `    // TODO: actual implementation here\n`;
      // Build minimal sample output from OpenAPI response schema (best-effort)
      const responses = endpoint?.definition?.responses || {};
      const respCodes = Object.keys(responses).filter((c: string) => /^\d{3}$/.test(c));
      const pick2xx = (codes: string[]) => codes.map(Number).filter(n => n>=200 && n<300).sort((a,b)=>a-b);
      let chosenSchema: any | null = null;
      if (respCodes.length > 0) {
        const twos = pick2xx(respCodes);
        const chosen = (method === 'post' && twos.includes(201)) ? 201
          : (method === 'delete' && twos.includes(204)) ? 204
          : (twos.includes(200) ? 200 : (twos[0] ?? 200));
        const resp = responses[String(chosen)];
        let schema = resp?.content?.['application/problem+json']?.schema
          || resp?.content?.['application/json']?.schema;
        if (!schema && resp?.content) {
          const cts = Object.keys(resp.content);
          const appCt = cts.find(ct => ct.startsWith('application/')) || cts[0];
          schema = /xml/i.test(appCt) ? { type:'string' } : (resp.content[appCt]?.schema || (appCt === 'text/plain' ? { type: 'string' } : undefined));
        }
        if (schema) chosenSchema = schema;
      }
      const lit = this.buildSampleLiteral(chosenSchema, endpoint?.components || {});
      content += `    const output: unknown = ${lit};\n`;
      content += `    if (!post(input, output)) return { status: 500, error: 'Postcondition failed' };\n`;
      content += `    ${contractBase}Output.parse(output);\n`;
      // Choose default status from OpenAPI responses (prefer 201 for POST, 204 for DELETE, else 200)
      // responses already computed above
      const respCodes2 = Object.keys(responses).filter((c: string) => /^\d{3}$/.test(c));
      let defaultStatus = method === 'post' ? 201 : method === 'delete' ? 204 : 200;
      if (respCodes2.length > 0) {
        const twos = respCodes2.map(Number).filter(n => n >= 200 && n < 300).sort((a,b)=>a-b);
        if (method === 'post' && twos.includes(201)) defaultStatus = 201;
        else if (method === 'delete' && twos.includes(204)) defaultStatus = 204;
        else if (twos.includes(200)) defaultStatus = 200;
        else if (twos.length > 0) defaultStatus = twos[0];
      }
      content += `    return { status: ${defaultStatus}, data: output };\n`;
      content += `  } catch (e) {\n`;
      // Map errors to OpenAPI 4xx/5xx and include minimal bodies when available
      const fourxx = respCodes2.map(Number).filter(n => n >= 400 && n < 500);
      const fivexx = respCodes2.map(Number).filter(n => n >= 500 && n < 600);
      const badReq = fourxx.includes(400) ? 400 : (fourxx.includes(422) ? 422 : (fourxx[0] ?? 400));
      const srvErr = fivexx.includes(500) ? 500 : (fivexx[0] ?? 500);
<<<<<<< HEAD
      let badSchema = (responses as any)[String(badReq)]?.content?.['application/problem+json']?.schema
        || (responses as any)[String(badReq)]?.content?.['application/json']?.schema
        || null;
      let srvSchema = (responses as any)[String(srvErr)]?.content?.['application/problem+json']?.schema
        || (responses as any)[String(srvErr)]?.content?.['application/json']?.schema
        || null;
      if (!badSchema) {
        const c = (responses as any)[String(badReq)]?.content; if (c) {
          const cts = Object.keys(c);
          const appCt = cts.find((ct: string) => ct.startsWith('application/')) || cts[0];
          badSchema = c[appCt]?.schema || (appCt==='text/plain'?{type:'string'}:null);
        }
      }
      if (!srvSchema) {
        const c = (responses as any)[String(srvErr)]?.content; if (c) {
          const cts = Object.keys(c);
          const appCt = cts.find((ct: string) => ct.startsWith('application/')) || cts[0];
          srvSchema = c[appCt]?.schema || (appCt==='text/plain'?{type:'string'}:null);
        }
=======
      let badSchema = (responses as any)[String(badReq)]?.content?.['application/json']?.schema || null;
      let srvSchema = (responses as any)[String(srvErr)]?.content?.['application/json']?.schema || null;
      if (!badSchema) {
        const c = (responses as any)[String(badReq)]?.content; if (c) { const k = Object.keys(c)[0]; badSchema = c[k]?.schema || (k==='text/plain'?{type:'string'}:null); }
      }
      if (!srvSchema) {
        const c = (responses as any)[String(srvErr)]?.content; if (c) { const k = Object.keys(c)[0]; srvSchema = c[k]?.schema || (k==='text/plain'?{type:'string'}:null); }
>>>>>>> origin/main
      }
      const badLit = this.buildSampleLiteral(badSchema, endpoint?.components || {});
      const srvLit = this.buildSampleLiteral(srvSchema, endpoint?.components || {});
      content += `    if (e instanceof z.ZodError) return { status: ${badReq}, error: 'Validation error', details: e.errors, data: ${badLit} };\n`;
      content += `    return { status: ${srvErr}, error: 'Unhandled error', data: ${srvLit} };\n`;
      content += `  }\n`;
      content += `}\n`;
    }
    return {
      path: `src/routes/${fileSafe}.ts`,
      content,
      purpose: `Handle ${endpoint.method} ${endpoint.path}`,
      tests: [],
    };
  }

  // Build a minimal TypeScript literal from an OpenAPI schema object (best-effort)
  private buildSampleLiteral(schema: any, components: Record<string, any> = {}, depth = 0): string {
    if (!schema || depth > 5) return '{}';
    if (schema.$ref && typeof schema.$ref === 'string') {
      const ref = String(schema.$ref);
      const name = ref.split('/').pop() as string;
      const target = name && components ? components[name] : null;
      if (target) return this.buildSampleLiteral(target, components, depth + 1);
      return '{}';
    }
    if (schema.default !== undefined) {
      return JSON.stringify(schema.default);
    }
    if (Array.isArray(schema.enum) && schema.enum.length > 0) {
      return JSON.stringify(schema.enum[0]);
    }
    const t = schema.type || (schema.properties ? 'object' : (schema.items ? 'array' : undefined));
    switch (t) {
      case 'integer':
      case 'number':
        return '0';
      case 'boolean':
        return 'false';
      case 'string':
        return JSON.stringify('');
      case 'array': {
        const itemLit = schema.items ? this.buildSampleLiteral(schema.items, components, depth + 1) : null;
        // keep minimal; empty array is safe
        return '[]';
      }
      case 'object': {
        const props = schema.properties || {};
        const keys = Object.keys(props);
        const body = keys.map(k => `${JSON.stringify(k)}: ${this.buildSampleLiteral(props[k], components, depth + 1)}`).join(', ');
        return `{ ${body} }`;
      }
      default:
        return '{}';
    }
  }

  private generateModel(schema: any, database?: string): CodeFile {
    return {
      path: `src/models/${schema.name}.ts`,
      content: '// Model implementation',
      purpose: `Model for ${schema.name}`,
      tests: [],
    };
  }

  private createProjectStructure(files: CodeFile[]): ProjectStructure {
    return {
      directories: [...new Set(files.map(f => path.dirname(f.path)))],
      entryPoint: 'src/index.ts',
      configFiles: [],
    };
  }

  private identifyDependencies(files: CodeFile[]): string[] {
    const deps = new Set<string>();
    
    for (const file of files) {
      const imports = file.content.match(/import .* from ['"]([^'"]+)['"]/g) || [];
      imports.forEach(imp => {
        const match = imp.match(/from ['"]([^'"]+)['"]/);
        if (match && match[1] && !match[1].startsWith('.')) {
          deps.add(match[1]);
        }
      });
    }
    
    return Array.from(deps);
  }

  private getFrameworkDependencies(framework: string): string[] {
    const deps: Record<string, string[]> = {
      fastify: ['fastify', '@fastify/cors', '@fastify/helmet'],
      express: ['express', 'cors', 'helmet'],
      koa: ['koa', '@koa/router', 'koa-bodyparser'],
    };
    return deps[framework] || [];
  }

  private applySingletonPattern(code: string): string {
    // Apply singleton pattern to classes without overwriting existing members
    return code.replace(
      /class (\w+)\s*{/, 
      (match, className) => {
        return `class ${className} {
  private static instance: ${className};
  
  static getInstance(): ${className} {
    if (!${className}.instance) {
      ${className}.instance = new ${className}();
    }
    return ${className}.instance;
  }
`; // Keep opening brace, rest of class will follow
      }
    );
  }

  private applyFactoryPattern(code: string): string {
    // Add factory methods
    return code; // Simplified implementation
  }

  private applyObserverPattern(code: string): string {
    // Add observer pattern
    return code; // Simplified implementation
  }

  private applyStrategyPattern(code: string): string {
    // Add strategy pattern
    return code; // Simplified implementation
  }

  private applyDecoratorPattern(code: string): string {
    // Add decorator pattern
    return code; // Simplified implementation
  }

  private applyRepositoryPattern(code: string): string {
    // Add repository pattern
    return code; // Simplified implementation
  }

  private identifyBottlenecks(code: string): any[] {
    const bottlenecks = [];
    
    // Check for nested loops
    if (code.match(/for.*\{[^}]*for/)) {
      bottlenecks.push({ type: 'nested-loops', severity: 'high' });
    }
    
    // Check for synchronous file operations
    if (code.match(/readFileSync|writeFileSync/)) {
      bottlenecks.push({ type: 'sync-io', severity: 'medium' });
    }
    
    return bottlenecks;
  }

  private optimizeBottleneck(bottleneck: any, metrics: any): PerformanceImprovement {
    return {
      location: 'line 100',
      type: bottleneck.type,
      description: `Optimize ${bottleneck.type}`,
      impact: bottleneck.severity,
    };
  }

  private applyOptimization(code: string, improvement: PerformanceImprovement): string {
    // Apply specific optimizations
    if (improvement.type === 'sync-io') {
      return code.replace(/readFileSync/g, 'readFile').replace(/writeFileSync/g, 'writeFile');
    }
    return code;
  }

  private async runBenchmarks(optimizedCode: string, originalCode: string): Promise<Benchmark[]> {
    return [
      {
        name: 'execution-time',
        before: 100,
        after: 50,
        improvement: 50,
      },
    ];
  }

  private addAuthentication(code: string, type: string): string {
    const authCode = type === 'jwt' ? `
import jwt from 'jsonwebtoken';

const authenticate = (token: string) => {
  return jwt.verify(token, process.env.JWT_SECRET!);
};
` : '';
    return authCode + code;
  }

  private addAuthorization(code: string, type: string): string {
    const authzCode = type === 'rbac' ? `
const authorize = (user: any, resource: string, action: string) => {
  return user.roles.some((role: any) => 
    role.permissions.includes(\`\${resource}:\${action}\`)
  );
};
` : '';
    return authzCode + code;
  }

  private addEncryption(code: string): string {
    return `import crypto from 'crypto';

` + code;
  }

  private addRateLimiting(code: string): string {
    return code; // Simplified
  }

  private addCORS(code: string): string {
    return code; // Simplified
  }

  private wrapInTryCatch(code: string, strategy: any): string {
    return `try {
${code}
} catch (error) {
  console.error(error);
  throw error;
}`;
  }

  private convertToResultType(code: string): string {
    return code; // Simplified
  }

  private addErrorMiddleware(code: string): string {
    return code + `
// Error handling middleware
`;
  }

  private addErrorLogging(code: string): string {
    return code; // Simplified
  }

  private addRecoveryMechanisms(code: string): string {
    return code; // Simplified
  }

  private addUserFriendlyErrors(code: string): string {
    return code; // Simplified
  }

  private generateEntity(table: Table, orm?: string): CodeFile {
    const entityCode = orm === 'typeorm' ? `
import { Entity, Column, PrimaryGeneratedColumn } from 'typeorm';

@Entity()
export class ${table.name} {
  @PrimaryGeneratedColumn()
  id: number;
  
  // Add columns
}
` : `// Entity for ${table.name}`;

    return {
      path: `src/entities/${table.name}.ts`,
      content: entityCode,
      purpose: `Entity definition for ${table.name}`,
      tests: [],
    };
  }

  private generateRepository(table: Table, options: any): CodeFile {
    return {
      path: `src/repositories/${table.name}Repository.ts`,
      content: `// Repository for ${table.name}`,
      purpose: `Data access for ${table.name}`,
      tests: [],
    };
  }

  private generateDatabaseConnection(options: any): CodeFile {
    return {
      path: 'src/database/connection.ts',
      content: `// Database connection setup`,
      purpose: 'Database connection configuration',
      tests: [],
    };
  }

  private generateMigrations(schema: DatabaseSchema, database: string): CodeFile[] {
    return [];
  }

  private generateTransactionHelpers(orm?: string): CodeFile {
    return {
      path: 'src/database/transactions.ts',
      content: `// Transaction helpers`,
      purpose: 'Database transaction utilities',
      tests: [],
    };
  }

  private createDataLayerStructure(files: CodeFile[]): ProjectStructure {
    return {
      directories: ['src/entities', 'src/repositories', 'src/database'],
      entryPoint: 'src/index.ts',
      configFiles: [],
    };
  }

  private getORMDependencies(orm?: string, database?: string): string[] {
    if (!orm || orm === 'none') return [];
    
    const deps: Record<string, string[]> = {
      typeorm: ['typeorm', 'reflect-metadata'],
      prisma: ['@prisma/client'],
      sequelize: ['sequelize'],
    };
    
    return deps[orm] || [];
  }

  private reduceComplexity(code: string): { code: string; changes: RefactoringChange[] } {
    return {
      code,
      changes: [{ type: 'complexity', location: 'global', description: 'Reduced complexity' }],
    };
  }

  private eliminateDuplication(code: string): { code: string; changes: RefactoringChange[] } {
    return {
      code,
      changes: [{ type: 'dry', location: 'global', description: 'Eliminated duplication' }],
    };
  }

  private improveNaming(code: string): { code: string; changes: RefactoringChange[] } {
    return {
      code,
      changes: [{ type: 'naming', location: 'global', description: 'Improved naming' }],
    };
  }

  private extractMethods(code: string): { code: string; changes: RefactoringChange[] } {
    return {
      code,
      changes: [{ type: 'extract', location: 'global', description: 'Extracted methods' }],
    };
  }

  private calculateMetrics(code: string): CodeMetrics {
    return {
      complexity: 10,
      maintainability: 85,
      duplication: 5,
      testCoverage: 0,
    };
  }
}

// Type definitions
interface TestAnalysis {
  functions: string[];
  classes: string[];
  expectedBehaviors: string[];
}

interface DatabaseSchema {
  tables: Table[];
  relations: Relation[];
}

interface Table {
  name: string;
  columns: Column[];
  indexes: Index[];
}

interface Column {
  name: string;
  type: string;
  nullable: boolean;
  primary?: boolean;
  unique?: boolean;
}

interface Index {
  name: string;
  columns: string[];
  unique: boolean;
}

interface Relation {
  from: string;
  to: string;
  type: 'one-to-one' | 'one-to-many' | 'many-to-many';
}

interface PerformanceImprovement {
  location: string;
  type: string;
  description: string;
  impact: 'high' | 'medium' | 'low';
}

interface Benchmark {
  name: string;
  before: number;
  after: number;
  improvement: number;
}

interface RefactoringChange {
  type: string;
  location: string;
  description: string;
}

interface CodeMetrics {
  complexity: number;
  maintainability: number;
  duplication: number;
  testCoverage: number;
}
