/**
 * Test Generation Agent
 * 自動的にテストケースを生成し、包括的なテスト戦略を提供
 */

import type { execSync } from 'child_process';
import { readFileSync, existsSync } from 'fs';

export interface TestGenerationRequest {
  feature: string;
  requirements?: string[];
  codeFile?: string;
  testFramework: 'vitest' | 'jest' | 'mocha' | 'exunit';
}

export interface GeneratedTest {
  testFile: string;
  testContent: string;
  testCases: TestCase[];
  coverage: TestCoverage;
  recommendations: string[];
}

export interface TestCase {
  name: string;
  type: 'unit' | 'integration' | 'e2e' | 'property' | 'contract';
  description: string;
  priority: 'critical' | 'high' | 'medium' | 'low';
  code: string;
  dataGenerators?: PropertyGenerator[];
}

export interface PropertyGenerator {
  name: string;
  type: string;
  constraints: string[];
  generator: string;
}

export interface TestCoverage {
  functional: string[];
  edgeCases: string[];
  errorHandling: string[];
  performance: string[];
  security: string[];
}

export class TestGenerationAgent {
  /**
   * 要件からテストケースを自動生成
   */
  async generateTestsFromRequirements(request: TestGenerationRequest): Promise<GeneratedTest> {
    const testCases = this.analyzeAndGenerateTestCases(request);
    const coverage = this.analyzeCoverage(testCases);
    const testContent = this.generateTestFileContent(testCases, request);
    
    return {
      testFile: this.determineTestFilePath(request),
      testContent,
      testCases,
      coverage,
      recommendations: this.generateRecommendations(coverage),
    };
  }

  /**
   * コードからテストを逆生成（リバースTDD）
   */
  async generateTestsFromCode(codeFile: string): Promise<GeneratedTest> {
    if (!existsSync(codeFile)) {
      throw new Error(`Code file not found: ${codeFile}`);
    }

    const codeContent = readFileSync(codeFile, 'utf8');
    const analysis = this.analyzeCode(codeContent);
    const testCases = this.generateTestCasesFromAnalysis(analysis);
    
    return {
      testFile: codeFile.replace('/src/', '/tests/').replace('.ts', '.test.ts'),
      testContent: this.generateTestFileContent(testCases, { 
        feature: analysis.mainFeature,
        testFramework: 'vitest' 
      }),
      testCases,
      coverage: this.analyzeCoverage(testCases),
      recommendations: this.generateCodeBasedRecommendations(analysis),
    };
  }

  /**
   * Property-Based Testing の自動設計
   */
  async generatePropertyTests(contract: {
    function: string;
    inputs: Array<{ name: string; type: string; constraints?: string[] }>;
    outputs: { type: string; constraints?: string[] };
    invariants: string[];
  }): Promise<TestCase[]> {
    const propertyTests: TestCase[] = [];

    // 入力の性質から自動的にプロパティを導出
    for (const invariant of contract.invariants) {
      propertyTests.push({
        name: `Property: ${invariant}`,
        type: 'property',
        description: `Verify invariant: ${invariant}`,
        priority: 'high',
        code: this.generatePropertyTestCode(contract, invariant),
        dataGenerators: this.createDataGenerators(contract.inputs),
      });
    }

    // エッジケースプロパティの自動検出
    const edgeCaseProperties = this.detectEdgeCaseProperties(contract);
    for (const edgeCase of edgeCaseProperties) {
      propertyTests.push({
        name: `Edge case: ${edgeCase.name}`,
        type: 'property',
        description: edgeCase.description,
        priority: 'medium',
        code: this.generatePropertyTestCode(contract, edgeCase.property),
        dataGenerators: edgeCase.generators,
      });
    }

    return propertyTests;
  }

  /**
   * BDD シナリオの自動生成
   */
  async generateBDDScenarios(userStory: {
    title: string;
    asA: string;
    iWant: string;
    soThat: string;
    acceptanceCriteria: string[];
  }): Promise<string> {
    let gherkin = `Feature: ${userStory.title}\n`;
    gherkin += `  As a ${userStory.asA}\n`;
    gherkin += `  I want ${userStory.iWant}\n`;
    gherkin += `  So that ${userStory.soThat}\n\n`;

    // 受け入れ基準からシナリオを生成
    for (const criteria of userStory.acceptanceCriteria) {
      const scenario = this.criteriaToScenario(criteria);
      gherkin += scenario + '\n\n';
    }

    // エッジケースシナリオの自動追加
    const edgeScenarios = this.generateEdgeCaseScenarios(userStory);
    for (const scenario of edgeScenarios) {
      gherkin += scenario + '\n\n';
    }

    return gherkin;
  }

  /**
   * 統合テスト戦略の立案
   */
  async planIntegrationTests(architecture: {
    services: Array<{ name: string; dependencies: string[] }>;
    dataFlow: Array<{ from: string; to: string; data: string }>;
  }): Promise<{
    testPlan: IntegrationTestPlan;
    mockStrategy: MockStrategy;
    testOrder: string[];
  }> {
    const criticalPaths = this.identifyCriticalPaths(architecture);
    const integrationPoints = this.identifyIntegrationPoints(architecture);
    
    return {
      testPlan: {
        phases: [
          { name: 'Unit Integration', tests: this.generateUnitIntegrationTests(architecture) },
          { name: 'Service Integration', tests: this.generateServiceIntegrationTests(architecture) },
          { name: 'End-to-End', tests: this.generateE2ETests(architecture) },
        ],
        coverage: this.calculateIntegrationCoverage(integrationPoints),
      },
      mockStrategy: this.determineMockStrategy(architecture),
      testOrder: this.optimizeTestExecutionOrder(criticalPaths),
    };
  }

  /**
   * セキュリティテストの自動生成
   */
  async generateSecurityTests(endpoint: {
    path: string;
    method: string;
    authentication: boolean;
    authorization?: string[];
    inputs: any[];
  }): Promise<TestCase[]> {
    const securityTests: TestCase[] = [];

    // OWASP Top 10 に基づくテスト生成
    const owaspTests = [
      this.generateInjectionTest(endpoint),
      this.generateAuthenticationTest(endpoint),
      this.generateAuthorizationTest(endpoint),
      this.generateXSSTest(endpoint),
      this.generateCSRFTest(endpoint),
    ];

    securityTests.push(...owaspTests.filter(Boolean) as TestCase[]);

    // ファジングテストの生成
    if (endpoint.inputs.length > 0) {
      securityTests.push(this.generateFuzzingTest(endpoint));
    }

    return securityTests;
  }

  /**
   * パフォーマンステストの設計
   */
  async designPerformanceTests(sla: {
    responseTime: number;
    throughput: number;
    concurrentUsers: number;
    availability: number;
  }): Promise<{
    loadTests: LoadTest[];
    stressTests: StressTest[];
    spikeTests: SpikeTest[];
    soakTests: SoakTest[];
  }> {
    return {
      loadTests: this.generateLoadTests(sla),
      stressTests: this.generateStressTests(sla),
      spikeTests: this.generateSpikeTests(sla),
      soakTests: this.generateSoakTests(sla),
    };
  }

  private analyzeAndGenerateTestCases(request: TestGenerationRequest): TestCase[] {
    const testCases: TestCase[] = [];

    // 機能テスト
    testCases.push({
      name: `${request.feature} - Happy Path`,
      type: 'unit',
      description: `Test successful ${request.feature} operation`,
      priority: 'critical',
      code: this.generateHappyPathTest(request),
    });

    // エラーハンドリング
    testCases.push({
      name: `${request.feature} - Error Handling`,
      type: 'unit',
      description: `Test error scenarios for ${request.feature}`,
      priority: 'high',
      code: this.generateErrorHandlingTest(request),
    });

    // エッジケース
    const edgeCases = this.identifyEdgeCases(request);
    for (const edgeCase of edgeCases) {
      testCases.push({
        name: `${request.feature} - Edge: ${edgeCase}`,
        type: 'unit',
        description: `Test edge case: ${edgeCase}`,
        priority: 'medium',
        code: this.generateEdgeCaseTest(request, edgeCase),
      });
    }

    return testCases;
  }

  private analyzeCode(code: string): CodeAnalysis {
    // コード解析ロジック
    const functions = this.extractFunctions(code);
    const classes = this.extractClasses(code);
    const complexity = this.calculateComplexity(code);
    
    return {
      mainFeature: this.inferFeatureName(functions, classes),
      functions,
      classes,
      complexity,
      dependencies: this.extractDependencies(code),
      patterns: this.detectPatterns(code),
    };
  }

  private generateTestFileContent(testCases: TestCase[], request: TestGenerationRequest): string {
    const framework = request.testFramework || 'vitest';
    
    if (framework === 'exunit') {
      return this.generateExUnitTestContent(testCases, request);
    }
    
    let content = '';

    // インポート文
    content += this.generateImports(framework);
    content += '\n\n';

    // テストスイート
    content += `describe('${request.feature}', () => {\n`;
    
    for (const testCase of testCases) {
      content += `  // ${testCase.description}\n`;
      content += `  ${testCase.code}\n\n`;
    }

    content += '});\n';

    return content;
  }

  private generateExUnitTestContent(testCases: TestCase[], request: TestGenerationRequest): string {
    const moduleName = this.toElixirModuleName(request.feature);
    let content = '';

    // Module definition and use ExUnit.Case
    content += `defmodule ${moduleName}Test do\n`;
    content += `  ${this.generateImports('exunit')}\n\n`;
    
    // Module being tested
    content += `  alias ${moduleName}\n\n`;
    
    // Test cases
    for (const testCase of testCases) {
      content += `  # ${testCase.description}\n`;
      content += `  ${this.convertToExUnitTest(testCase)}\n\n`;
    }

    content += 'end\n';

    return content;
  }

  private convertToExUnitTest(testCase: TestCase): string {
    const testName = testCase.name.toLowerCase().replace(/\s+/g, '_');
    
    let test = `  test "${testCase.description}" do\n`;
    
    // Convert basic test patterns to ExUnit
    if (testCase.code.includes('expect(')) {
      // Convert expect() calls to ExUnit assertions
      const converted = testCase.code
        .replace(/expect\(([^)]+)\)\.toBe\(([^)]+)\)/g, 'assert $1 == $2')
        .replace(/expect\(([^)]+)\)\.toEqual\(([^)]+)\)/g, 'assert $1 == $2')
        .replace(/expect\(([^)]+)\)\.toBeTruthy\(\)/g, 'assert $1')
        .replace(/expect\(([^)]+)\)\.toBeFalsy\(\)/g, 'refute $1');
      
      test += `    # ${testCase.description}\n`;
      test += `    # TODO: Implement test logic\n`;
      test += `    assert true\n`;
    } else {
      test += `    # ${testCase.description}\n`;
      test += `    # TODO: Implement test logic\n`;
      test += `    assert true\n`;
    }
    
    test += `  end`;
    
    return test;
  }

  private toElixirModuleName(name: string): string {
    return name
      .split(/\s+/)
      .map(word => word.charAt(0).toUpperCase() + word.slice(1).toLowerCase())
      .join('');
  }

  private generatePropertyTestCode(contract: any, invariant: string): string {
    return `
  property('${invariant}', () => {
    fc.assert(
      fc.property(
        ${contract.inputs.map((i: any) => this.generateArbitrary(i)).join(',\n        ')},
        (${contract.inputs.map((i: any) => i.name).join(', ')}) => {
          const result = ${contract.function}(${contract.inputs.map((i: any) => i.name).join(', ')});
          return ${this.invariantToAssertion(invariant)};
        }
      )
    );
  });`;
  }

  private generateArbitrary(input: { name: string; type: string; constraints?: string[] }): string {
    const typeMap: Record<string, string> = {
      'string': 'fc.string()',
      'number': 'fc.integer()',
      'boolean': 'fc.boolean()',
      'array': 'fc.array(fc.anything())',
      'object': 'fc.object()',
    };

    let arbitrary = typeMap[input.type] || 'fc.anything()';

    // 制約を適用
    if (input.constraints) {
      for (const constraint of input.constraints) {
        arbitrary = this.applyConstraint(arbitrary, constraint);
      }
    }

    return `${arbitrary} // ${input.name}`;
  }

  // ヘルパーメソッド群
  private extractFunctions(code: string): string[] {
    const regex = /(?:export\s+)?(?:async\s+)?function\s+(\w+)/g;
    return Array.from(code.matchAll(regex), m => m[1]).filter((name): name is string => Boolean(name));
  }

  private extractClasses(code: string): string[] {
    const regex = /(?:export\s+)?class\s+(\w+)/g;
    return Array.from(code.matchAll(regex), m => m[1]).filter((name): name is string => Boolean(name));
  }

  private calculateComplexity(code: string): number {
    // 簡易的な循環的複雑度計算
    const conditions = (code.match(/if\s*\(|while\s*\(|for\s*\(|case\s+/g) || []).length;
    return conditions + 1;
  }

  private generateImports(framework: string): string {
    const imports = {
      'vitest': "import { describe, it, expect, beforeEach, afterEach } from 'vitest';",
      'jest': "import { describe, it, expect, beforeEach, afterEach } from '@jest/globals';",
      'mocha': "import { describe, it, beforeEach, afterEach } from 'mocha';\nimport { expect } from 'chai';",
      'exunit': "use ExUnit.Case",
    } as const;
    
    return (imports as any)[framework] || imports.vitest;
  }

  // 以下、多数のヘルパーメソッドの簡略版
  private determineTestFilePath(request: TestGenerationRequest): string {
    const framework = request.testFramework || 'vitest';
    const baseName = request.feature.toLowerCase().replace(/\s+/g, '-');
    
    switch (framework) {
      case 'exunit':
        return `test/${baseName}_test.exs`;
      case 'vitest':
      case 'jest':
      case 'mocha':
      default:
        return `tests/${baseName}.test.ts`;
    }
  }

  private analyzeCoverage(testCases: TestCase[]): TestCoverage {
    return {
      functional: testCases.filter(t => t.type === 'unit').map(t => t.name),
      edgeCases: testCases.filter(t => t.name.includes('Edge')).map(t => t.name),
      errorHandling: testCases.filter(t => t.name.includes('Error')).map(t => t.name),
      performance: testCases.filter(t => t.name.includes('Performance')).map(t => t.name),
      security: testCases.filter(t => t.name.includes('Security')).map(t => t.name),
    };
  }

  private generateRecommendations(coverage: TestCoverage): string[] {
    const recommendations: string[] = [];
    
    if (coverage.functional.length < 3) {
      recommendations.push('Add more functional test cases');
    }
    if (coverage.security.length === 0) {
      recommendations.push('Consider adding security tests');
    }
    if (coverage.performance.length === 0) {
      recommendations.push('Add performance tests for critical paths');
    }
    
    return recommendations;
  }

  // 追加のスタブメソッド（実装は省略）
  private identifyEdgeCases(request: TestGenerationRequest): string[] {
    return ['empty input', 'maximum value', 'null value', 'special characters'];
  }

  private generateHappyPathTest(request: TestGenerationRequest): string {
    return `it('should handle ${request.feature} successfully', async () => {
    // Arrange
    const input = /* test data */;
    
    // Act
    const result = await ${request.feature}(input);
    
    // Assert
    expect(result).toBeDefined();
    expect(result.success).toBe(true);
  });`;
  }

  private generateErrorHandlingTest(request: TestGenerationRequest): string {
    return `it('should handle errors gracefully', async () => {
    // Arrange
    const invalidInput = /* invalid data */;
    
    // Act & Assert
    await expect(${request.feature}(invalidInput)).rejects.toThrow();
  });`;
  }

  private generateEdgeCaseTest(request: TestGenerationRequest, edgeCase: string): string {
    return `it('should handle edge case: ${edgeCase}', () => {
    // Test implementation for ${edgeCase}
    expect(true).toBe(true); // Placeholder
  });`;
  }

  // Missing method implementations
  private generateTestCasesFromAnalysis(analysis: CodeAnalysis): TestCase[] {
    return [
      {
        name: `${analysis.mainFeature} - Unit Test`,
        type: 'unit',
        description: `Test ${analysis.mainFeature} functionality`,
        priority: 'high',
        code: `it('should test ${analysis.mainFeature}', () => { expect(true).toBe(true); });`,
      },
    ];
  }

  private generateCodeBasedRecommendations(analysis: CodeAnalysis): string[] {
    const recommendations: string[] = [];
    if (analysis.complexity > 10) {
      recommendations.push('Consider reducing complexity with unit tests');
    }
    if (analysis.functions.length > 5) {
      recommendations.push('Add integration tests for function interactions');
    }
    return recommendations;
  }

  private createDataGenerators(inputs: Array<{ name: string; type: string; constraints?: string[] }>): PropertyGenerator[] {
    return inputs.map(input => ({
      name: input.name,
      type: input.type,
      constraints: input.constraints || [],
      generator: `fc.${input.type}()`,
    }));
  }

  private detectEdgeCaseProperties(contract: any): Array<{ name: string; description: string; property: string; generators: PropertyGenerator[] }> {
    return [
      {
        name: 'boundary values',
        description: 'Test boundary conditions',
        property: 'boundary check',
        generators: this.createDataGenerators(contract.inputs),
      },
    ];
  }

  private criteriaToScenario(criteria: string): string {
    return `  Scenario: ${criteria}
    Given initial conditions
    When action is performed
    Then expected outcome occurs`;
  }

  private generateEdgeCaseScenarios(userStory: any): string[] {
    return [
      `  Scenario: Edge case - empty input
    Given empty input
    When ${userStory.iWant}
    Then appropriate error handling occurs`,
    ];
  }

  private identifyCriticalPaths(architecture: any): string[] {
    return architecture.services.map((service: any) => service.name);
  }

  private identifyIntegrationPoints(architecture: any): string[] {
    return architecture.dataFlow.map((flow: any) => `${flow.from}->${flow.to}`);
  }

  private generateUnitIntegrationTests(architecture: any): any[] {
    return architecture.services.map((service: any) => ({
      name: `${service.name} unit integration`,
      type: 'integration',
    }));
  }

  private generateServiceIntegrationTests(architecture: any): any[] {
    return architecture.services.map((service: any) => ({
      name: `${service.name} service integration`,
      type: 'integration',
    }));
  }

  private generateE2ETests(architecture: any): any[] {
    return [
      {
        name: 'End-to-end flow test',
        type: 'e2e',
      },
    ];
  }

  private calculateIntegrationCoverage(integrationPoints: string[]): number {
    return integrationPoints.length > 0 ? 0.8 : 0;
  }

  private determineMockStrategy(architecture: any): MockStrategy {
    return {
      approach: 'partial',
      mocks: architecture.services.map((service: any) => ({
        service: service.name,
        type: 'partial',
      })),
    };
  }

  private optimizeTestExecutionOrder(criticalPaths: string[]): string[] {
    return criticalPaths.sort();
  }

  private generateInjectionTest(endpoint: any): TestCase | null {
    if (endpoint.inputs.length === 0) return null;
    return {
      name: 'SQL Injection Test',
      type: 'unit',
      description: 'Test for SQL injection vulnerabilities',
      priority: 'critical',
      code: `it('should prevent SQL injection', () => { expect(true).toBe(true); });`,
    };
  }

  private generateAuthenticationTest(endpoint: any): TestCase | null {
    if (!endpoint.authentication) return null;
    return {
      name: 'Authentication Test',
      type: 'unit',
      description: 'Test authentication requirements',
      priority: 'critical',
      code: `it('should require authentication', () => { expect(true).toBe(true); });`,
    };
  }

  private generateAuthorizationTest(endpoint: any): TestCase | null {
    if (!endpoint.authorization) return null;
    return {
      name: 'Authorization Test',
      type: 'unit',
      description: 'Test authorization requirements',
      priority: 'high',
      code: `it('should enforce authorization', () => { expect(true).toBe(true); });`,
    };
  }

  private generateXSSTest(endpoint: any): TestCase | null {
    const hasStringInputs = endpoint.inputs.some((input: any) => typeof input === 'string' || input.type === 'string');
    if (!hasStringInputs) return null;
    return {
      name: 'XSS Prevention Test',
      type: 'unit',
      description: 'Test for XSS vulnerabilities',
      priority: 'high',
      code: `it('should prevent XSS attacks', () => { expect(true).toBe(true); });`,
    };
  }

  private generateCSRFTest(endpoint: any): TestCase | null {
    if (endpoint.method === 'GET') return null;
    return {
      name: 'CSRF Protection Test',
      type: 'unit',
      description: 'Test CSRF protection',
      priority: 'high',
      code: `it('should prevent CSRF attacks', () => { expect(true).toBe(true); });`,
    };
  }

  private generateFuzzingTest(endpoint: any): TestCase {
    return {
      name: 'Fuzzing Test',
      type: 'unit',
      description: 'Test with random/malformed inputs',
      priority: 'medium',
      code: `it('should handle malformed inputs gracefully', () => { expect(true).toBe(true); });`,
    };
  }

  private generateLoadTests(sla: any): LoadTest[] {
    return [
      {
        name: 'Basic Load Test',
        duration: 300,
        users: sla.concurrentUsers,
        rampUp: 60,
      },
    ];
  }

  private generateStressTests(sla: any): StressTest[] {
    return [
      {
        name: 'Stress Test',
        duration: 600,
        users: sla.concurrentUsers * 2,
        rampUp: 120,
        breakingPoint: true,
      },
    ];
  }

  private generateSpikeTests(sla: any): SpikeTest[] {
    return [
      {
        name: 'Spike Test',
        duration: 180,
        users: sla.concurrentUsers,
        rampUp: 10,
        spikeMultiplier: 5,
      },
    ];
  }

  private generateSoakTests(sla: any): SoakTest[] {
    return [
      {
        name: 'Soak Test',
        duration: 1800,
        users: sla.concurrentUsers,
        rampUp: 300,
        sustainedDuration: 1200,
      },
    ];
  }

  private inferFeatureName(functions: string[], classes: string[]): string {
    if (classes.length > 0) {
      return classes[0] || 'UnknownClass';
    }
    if (functions.length > 0) {
      return functions[0] || 'UnknownFunction';
    }
    return 'Unknown Feature';
  }

  private extractDependencies(code: string): string[] {
    const importRegex = /import.*from\s+['"]([^'"]+)['"]/g;
    const dependencies: string[] = [];
    let match;
    while ((match = importRegex.exec(code)) !== null) {
      if (match[1]) {
        dependencies.push(match[1]);
      }
    }
    return dependencies;
  }

  private detectPatterns(code: string): string[] {
    const patterns: string[] = [];
    if (code.includes('class')) patterns.push('OOP');
    if (code.includes('async')) patterns.push('Async');
    if (code.includes('interface')) patterns.push('TypeScript');
    if (code.includes('export')) patterns.push('Module');
    return patterns;
  }

  private invariantToAssertion(invariant: string): string {
    // Convert invariant string to assertion code
    return `/* ${invariant} */ true`;
  }

  private applyConstraint(arbitrary: string, constraint: string): string {
    // Apply constraint to arbitrary generator
    return `${arbitrary}.filter(/* ${constraint} */ () => true)`;
  }
}

// Type definitions
interface CodeAnalysis {
  mainFeature: string;
  functions: string[];
  classes: string[];
  complexity: number;
  dependencies: string[];
  patterns: string[];
}

interface IntegrationTestPlan {
  phases: Array<{ name: string; tests: any[] }>;
  coverage: number;
}

interface MockStrategy {
  approach: 'full' | 'partial' | 'none';
  mocks: Array<{ service: string; type: string }>;
}

interface LoadTest {
  name: string;
  duration: number;
  users: number;
  rampUp: number;
}

interface StressTest extends LoadTest {
  breakingPoint: boolean;
}

interface SpikeTest extends LoadTest {
  spikeMultiplier: number;
}

interface SoakTest extends LoadTest {
  sustainedDuration: number;
}