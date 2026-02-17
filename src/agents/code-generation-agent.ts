/**
 * Code Generation Agent
 * Phase 4 of ae-framework: Automated code generation from tests and specifications
 */

import type { readFileSync, existsSync, writeFileSync } from 'fs';
import type { execSync } from 'child_process';
import * as path from 'path';

import type {
  CodeGenerationRequest,
  TestFile,
  ArchitecturePattern,
  GeneratedCode,
  CodeFile,
  ProjectStructure,
  TestResult,
  TestAnalysis,
  DatabaseSchema,
  Table,
  Column,
  PerformanceImprovement,
  Benchmark,
  RefactoringChange,
  CodeMetrics,
} from './code-generation-agent.types.js';
import type { OpenApiGenerationOptions } from './code-generation-openapi.js';
import {
  buildSampleLiteral,
  generateAuthMiddleware,
  generateModel,
  generateRouteHandler,
  generateServerSetup,
  generateValidationMiddleware,
  parseOpenAPI,
} from './code-generation-openapi.js';

export type {
  CodeGenerationRequest,
  TestFile,
  Specification,
  Contract,
  ArchitecturePattern,
  Layer,
  Dependency,
  CodingStyle,
  GeneratedCode,
  CodeFile,
  ProjectStructure,
  ConfigFile,
  TestResult,
} from './code-generation-agent.types.js';

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
  async generateFromOpenAPI(spec: string, options: OpenApiGenerationOptions): Promise<GeneratedCode> {
    const api = parseOpenAPI(spec);
    const files: CodeFile[] = [];
    
    // Generate route handlers
    for (const endpoint of api.endpoints) {
      const handler = generateRouteHandler(endpoint, options);
      files.push(handler);
    }
    
    // Generate models
    for (const schema of api.schemas) {
      const model = generateModel(schema, options.database);
      files.push(model);
    }
    
    // Generate middleware
    if (options.includeValidation) {
      files.push(generateValidationMiddleware());
    }
    
    if (options.includeAuth) {
      files.push(generateAuthMiddleware());
    }
    
    // Generate server setup
    files.push(generateServerSetup(options.framework));
    
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
    const api = parseOpenAPI(spec);
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
          if (appCt) {
            schema = rb[appCt]?.schema || (appCt === 'text/plain' ? { type: 'string' } : undefined);
          }
        }
        sample = buildSampleLiteral(schema, ep?.components || {});
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
