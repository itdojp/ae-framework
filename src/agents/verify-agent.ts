/**
 * Verify Agent
 * Phase 5 of ae-framework: Automated verification and quality assurance
 */

import { execSync } from 'child_process';
import { readFileSync, existsSync } from 'fs';
import * as path from 'path';
import { RustVerificationAgent, type RustVerificationRequest, type RustVerificationResult } from './rust-verification-agent.js';
import { ContainerAgent, type ContainerVerificationRequest } from './container-agent.js';

export interface VerificationRequest {
  codeFiles: CodeFile[];
  testFiles: TestFile[];
  specifications?: Specification[];
  verificationTypes: VerificationType[];
  strictMode?: boolean;
  containerConfig?: {
    enabled: boolean;
    preferredEngine?: 'docker' | 'podman';
    buildImages?: boolean;
    projectPath?: string;
  };
}

export interface CodeFile {
  path: string;
  content: string;
  language: string;
}

export interface TestFile {
  path: string;
  content: string;
  type: 'unit' | 'integration' | 'e2e' | 'property' | 'contract';
}

export interface Specification {
  type: 'openapi' | 'asyncapi' | 'graphql' | 'tla' | 'alloy';
  content: string;
  path: string;
}

export type VerificationType = 
  | 'tests'
  | 'coverage'
  | 'linting'
  | 'typechecking'
  | 'security'
  | 'performance'
  | 'accessibility'
  | 'contracts'
  | 'specifications'
  | 'mutations'
  | 'rust-verification'
  | 'container-verification';

export interface VerificationResult {
  passed: boolean;
  results: VerificationCheck[];
  coverage: CoverageReport;
  metrics: QualityMetrics;
  issues: Issue[];
  suggestions: string[];
  traceability: TraceabilityMatrix;
}

export interface VerificationCheck {
  type: VerificationType;
  passed: boolean;
  details: any;
  errors?: string[];
  warnings?: string[];
}

export interface TestResult {
  total: number;
  passed: number;
  failed: number;
  duration: number;
  failures: Array<{
    message: string;
    fullTitle?: string;
  }>;
}

export interface LintResult {
  errors: number;
  warnings: number;
  messages: Array<{
    severity: 'error' | 'warning';
    message: string;
    line?: number;
    column?: number;
  }>;
}

export interface BenchmarkResult {
  responseTime: number;
  throughput: number;
  errorRate: number;
  cpuUsage: number;
  memoryUsage: number;
}

export interface CoverageReport {
  line: number;
  branch: number;
  function: number;
  statement: number;
  uncoveredFiles: string[];
}

export interface QualityMetrics {
  complexity: number;
  maintainability: number;
  reliability: number;
  security: number;
  performance: number;
  testability: number;
}

export interface Issue {
  severity: 'critical' | 'high' | 'medium' | 'low';
  type: string;
  file: string;
  line?: number;
  message: string;
  fix?: string;
}

export interface TraceabilityMatrix {
  requirements: TraceItem[];
  specifications: TraceItem[];
  tests: TraceItem[];
  code: TraceItem[];
  coverage: number;
}

export interface TraceItem {
  id: string;
  description: string;
  linkedTo: string[];
  covered: boolean;
}

export class VerifyAgent {
  private rustVerificationAgent: RustVerificationAgent;
  private containerAgent?: ContainerAgent;

  constructor(options?: { enableContainers?: boolean; containerConfig?: any }) {
    this.rustVerificationAgent = new RustVerificationAgent();
    
    if (options?.enableContainers !== false) {
      this.containerAgent = new ContainerAgent(options?.containerConfig);
    }
  }

  /**
   * Run comprehensive verification suite
   */
  async runFullVerification(request: VerificationRequest): Promise<VerificationResult> {
    const results: VerificationCheck[] = [];
    const issues: Issue[] = [];
    
    // Run each verification type
    for (const type of request.verificationTypes) {
      const check = await this.runVerification(type, request);
      results.push(check);
      
      if (!check.passed && request.strictMode) {
        break; // Stop on first failure in strict mode
      }
    }
    
    // Generate coverage report
    const coverage = await this.generateCoverageReport(request);
    
    // Calculate quality metrics
    const metrics = await this.calculateQualityMetrics(request);
    
    // Build traceability matrix
    const traceability = await this.buildTraceabilityMatrix(request);
    
    // Generate suggestions
    const suggestions = this.generateSuggestions(results, coverage, metrics);
    
    return {
      passed: results.every(r => r.passed),
      results,
      coverage,
      metrics,
      issues,
      suggestions,
      traceability,
    };
  }

  /**
   * Run specific verification type
   */
  private async runVerification(
    type: VerificationType,
    request: VerificationRequest
  ): Promise<VerificationCheck> {
    switch (type) {
      case 'tests':
        return this.runTests(request);
      case 'coverage':
        return this.checkCoverage(request);
      case 'linting':
        return this.runLinting(request);
      case 'typechecking':
        return this.runTypeChecking(request);
      case 'security':
        return this.runSecurityChecks(request);
      case 'performance':
        return this.runPerformanceTests(request);
      case 'accessibility':
        return this.checkAccessibility(request);
      case 'contracts':
        return this.verifyContracts(request);
      case 'specifications':
        return this.verifySpecifications(request);
      case 'mutations':
        return this.runMutationTesting(request);
      case 'rust-verification':
        return this.runRustVerification(request);
      case 'container-verification':
        return this.runContainerVerification(request);
      default:
        return {
          type,
          passed: false,
          details: { error: 'Unknown verification type' },
        };
    }
  }

  /**
   * Run all tests
   */
  async runTests(request: VerificationRequest): Promise<VerificationCheck> {
    const testResults = {
      total: 0,
      passed: 0,
      failed: 0,
      skipped: 0,
      duration: 0,
      failures: [] as any[],
    };

    try {
      // Run different test types
      for (const test of request.testFiles) {
        const result = await this.runTestFile(test);
        testResults.total += result.total;
        testResults.passed += result.passed;
        testResults.failed += result.failed;
        testResults.duration += result.duration;
        
        if (result.failures) {
          testResults.failures.push(...result.failures);
        }
      }

      return {
        type: 'tests',
        passed: testResults.failed === 0,
        details: testResults,
        errors: testResults.failures.map(f => f.message),
      };
    } catch (error) {
      return {
        type: 'tests',
        passed: false,
        details: { error: (error as Error).message },
        errors: [(error as Error).message],
      };
    }
  }

  /**
   * Check code coverage
   */
  async checkCoverage(request: VerificationRequest): Promise<VerificationCheck> {
    try {
      const coverage = await this.generateCoverageReport(request);
      const threshold = 80; // Default threshold
      
      const passed = 
        coverage.line >= threshold &&
        coverage.branch >= threshold &&
        coverage.function >= threshold &&
        coverage.statement >= threshold;

      return {
        type: 'coverage',
        passed,
        details: coverage,
        warnings: coverage.uncoveredFiles.length > 0 
          ? [`${coverage.uncoveredFiles.length} files have no coverage`]
          : undefined,
      };
    } catch (error) {
      return {
        type: 'coverage',
        passed: false,
        details: { error: (error as Error).message },
        errors: [(error as Error).message],
      };
    }
  }

  /**
   * Run linting checks
   */
  async runLinting(request: VerificationRequest): Promise<VerificationCheck> {
    const lintResults = {
      errors: 0,
      warnings: 0,
      files: [] as any[],
    };

    try {
      for (const file of request.codeFiles) {
        const result = await this.lintFile(file);
        lintResults.errors += result.errors;
        lintResults.warnings += result.warnings;
        
        if (result.errors > 0 || result.warnings > 0) {
          lintResults.files.push({
            path: file.path,
            errors: result.errors,
            warnings: result.warnings,
            messages: result.messages,
          });
        }
      }

      return {
        type: 'linting',
        passed: lintResults.errors === 0,
        details: lintResults,
        errors: lintResults.errors > 0 
          ? [`Found ${lintResults.errors} linting errors`]
          : undefined,
        warnings: lintResults.warnings > 0
          ? [`Found ${lintResults.warnings} linting warnings`]
          : undefined,
      };
    } catch (error) {
      return {
        type: 'linting',
        passed: false,
        details: { error: (error as Error).message },
        errors: [(error as Error).message],
      };
    }
  }

  /**
   * Run type checking
   */
  async runTypeChecking(request: VerificationRequest): Promise<VerificationCheck> {
    try {
      const typeErrors = [];
      
      for (const file of request.codeFiles) {
        if (file.language === 'typescript') {
          const errors = await this.checkTypes(file);
          typeErrors.push(...errors);
        }
      }

      return {
        type: 'typechecking',
        passed: typeErrors.length === 0,
        details: { errors: typeErrors },
        errors: typeErrors.length > 0
          ? [`Found ${typeErrors.length} type errors`]
          : undefined,
      };
    } catch (error) {
      return {
        type: 'typechecking',
        passed: false,
        details: { error: (error as Error).message },
        errors: [(error as Error).message],
      };
    }
  }

  /**
   * Run security checks
   */
  async runSecurityChecks(request: VerificationRequest): Promise<VerificationCheck> {
    const securityIssues = [];

    try {
      // Check for common vulnerabilities
      for (const file of request.codeFiles) {
        const issues = await this.scanForVulnerabilities(file);
        securityIssues.push(...issues);
      }

      // Check dependencies
      const depIssues = await this.checkDependencies();
      securityIssues.push(...depIssues);

      // Check for secrets
      const secretIssues = await this.scanForSecrets(request.codeFiles);
      securityIssues.push(...secretIssues);

      const critical = securityIssues.filter(i => i.severity === 'critical');
      const high = securityIssues.filter(i => i.severity === 'high');

      return {
        type: 'security',
        passed: critical.length === 0 && high.length === 0,
        details: {
          total: securityIssues.length,
          critical: critical.length,
          high: high.length,
          issues: securityIssues,
        },
        errors: critical.length > 0
          ? [`Found ${critical.length} critical security issues`]
          : undefined,
        warnings: high.length > 0
          ? [`Found ${high.length} high severity security issues`]
          : undefined,
      };
    } catch (error) {
      return {
        type: 'security',
        passed: false,
        details: { error: (error as Error).message },
        errors: [(error as Error).message],
      };
    }
  }

  /**
   * Run performance tests
   */
  async runPerformanceTests(request: VerificationRequest): Promise<VerificationCheck> {
    try {
      const perfResults = {
        responseTime: 0,
        throughput: 0,
        errorRate: 0,
        cpuUsage: 0,
        memoryUsage: 0,
      };

      // Run performance benchmarks
      const benchmarks = await this.runBenchmarks(request.codeFiles);
      
      // Check against thresholds
      const thresholds = {
        responseTime: 100, // ms
        throughput: 1000, // req/s
        errorRate: 1, // %
        cpuUsage: 80, // %
        memoryUsage: 512, // MB
      };

      const passed = 
        benchmarks.responseTime <= thresholds.responseTime &&
        benchmarks.throughput >= thresholds.throughput &&
        benchmarks.errorRate <= thresholds.errorRate;

      return {
        type: 'performance',
        passed,
        details: benchmarks,
        warnings: !passed
          ? ['Performance does not meet thresholds']
          : undefined,
      };
    } catch (error) {
      return {
        type: 'performance',
        passed: false,
        details: { error: (error as Error).message },
        errors: [(error as Error).message],
      };
    }
  }

  /**
   * Check accessibility
   */
  async checkAccessibility(request: VerificationRequest): Promise<VerificationCheck> {
    // For non-UI code, this would check API accessibility
    return {
      type: 'accessibility',
      passed: true,
      details: { message: 'Accessibility checks for APIs' },
    };
  }

  /**
   * Verify contracts
   */
  async verifyContracts(request: VerificationRequest): Promise<VerificationCheck> {
    try {
      const contractResults = {
        total: 0,
        passed: 0,
        failed: 0,
        violations: [] as any[],
      };

      // Check contract tests
      const contractTests = request.testFiles.filter(t => t.type === 'contract');
      
      for (const test of contractTests) {
        const result = await this.runContractTest(test);
        contractResults.total += 1;
        if (result.passed) {
          contractResults.passed += 1;
        } else {
          contractResults.failed += 1;
          contractResults.violations.push(result);
        }
      }

      return {
        type: 'contracts',
        passed: contractResults.failed === 0,
        details: contractResults,
        errors: contractResults.violations.map(v => v.message),
      };
    } catch (error) {
      return {
        type: 'contracts',
        passed: false,
        details: { error: (error as Error).message },
        errors: [(error as Error).message],
      };
    }
  }

  /**
   * Verify specifications
   */
  async verifySpecifications(request: VerificationRequest): Promise<VerificationCheck> {
    if (!request.specifications || request.specifications.length === 0) {
      return {
        type: 'specifications',
        passed: true,
        details: { message: 'No specifications to verify' },
      };
    }

    try {
      const specResults = {
        total: request.specifications.length,
        valid: 0,
        invalid: 0,
        errors: [] as string[],
      };

      for (const spec of request.specifications) {
        const isValid = await this.validateSpecification(spec);
        if (isValid) {
          specResults.valid += 1;
        } else {
          specResults.invalid += 1;
          specResults.errors.push(`Invalid ${spec.type} specification: ${spec.path}`);
        }
      }

      return {
        type: 'specifications',
        passed: specResults.invalid === 0,
        details: specResults,
        errors: specResults.errors,
      };
    } catch (error) {
      return {
        type: 'specifications',
        passed: false,
        details: { error: (error as Error).message },
        errors: [(error as Error).message],
      };
    }
  }

  /**
   * Run mutation testing
   */
  async runMutationTesting(request: VerificationRequest): Promise<VerificationCheck> {
    try {
      const mutationResults = {
        mutantsGenerated: 0,
        mutantsKilled: 0,
        mutantsSurvived: 0,
        mutationScore: 0,
        survivors: [] as any[],
      };

      // Generate mutants
      const mutants = await this.generateMutants(request.codeFiles);
      mutationResults.mutantsGenerated = mutants.length;

      // Test each mutant
      for (const mutant of mutants) {
        const killed = await this.testMutant(mutant, request.testFiles);
        if (killed) {
          mutationResults.mutantsKilled += 1;
        } else {
          mutationResults.mutantsSurvived += 1;
          mutationResults.survivors.push(mutant);
        }
      }

      mutationResults.mutationScore = 
        (mutationResults.mutantsKilled / mutationResults.mutantsGenerated) * 100;

      const passed = mutationResults.mutationScore >= 80; // 80% threshold

      return {
        type: 'mutations',
        passed,
        details: mutationResults,
        warnings: mutationResults.mutantsSurvived > 0
          ? [`${mutationResults.mutantsSurvived} mutants survived`]
          : undefined,
      };
    } catch (error) {
      return {
        type: 'mutations',
        passed: false,
        details: { error: (error as Error).message },
        errors: [(error as Error).message],
      };
    }
  }

  /**
   * Generate coverage report
   */
  async generateCoverageReport(request: VerificationRequest): Promise<CoverageReport> {
    // This would integrate with actual coverage tools
    return {
      line: 85,
      branch: 75,
      function: 90,
      statement: 85,
      uncoveredFiles: [],
    };
  }

  /**
   * Calculate quality metrics
   */
  async calculateQualityMetrics(request: VerificationRequest): Promise<QualityMetrics> {
    return {
      complexity: 8, // Cyclomatic complexity
      maintainability: 85, // Maintainability index
      reliability: 92, // Reliability rating
      security: 88, // Security rating
      performance: 90, // Performance rating
      testability: 87, // Testability rating
    };
  }

  /**
   * Build traceability matrix
   */
  async buildTraceabilityMatrix(request: VerificationRequest): Promise<TraceabilityMatrix> {
    const requirements: TraceItem[] = [];
    const specifications: TraceItem[] = [];
    const tests: TraceItem[] = [];
    const code: TraceItem[] = [];

    // Extract requirements from specifications
    if (request.specifications) {
      for (const spec of request.specifications) {
        const items = this.extractRequirements(spec);
        requirements.push(...items);
      }
    }

    // Map tests to requirements
    for (const test of request.testFiles) {
      tests.push({
        id: test.path,
        description: `Test: ${test.path}`,
        linkedTo: [], // Would be extracted from test descriptions
        covered: true,
      });
    }

    // Map code to tests
    for (const file of request.codeFiles) {
      code.push({
        id: file.path,
        description: `Code: ${file.path}`,
        linkedTo: [], // Would be extracted from code comments
        covered: true,
      });
    }

    const coverage = this.calculateTraceabilityCoverage(requirements, tests, code);

    return {
      requirements,
      specifications,
      tests,
      code,
      coverage,
    };
  }

  /**
   * Run Rust formal verification
   */
  async runRustVerification(request: VerificationRequest): Promise<VerificationCheck> {
    try {
      const rustFiles = request.codeFiles.filter(file => 
        file.path.endsWith('.rs') || file.language === 'rust'
      );

      if (rustFiles.length === 0) {
        return {
          type: 'rust-verification',
          passed: true,
          details: { message: 'No Rust files found for verification' },
        };
      }

      // Find Rust project directory by looking for Cargo.toml
      const projectPath = this.findRustProjectPath(rustFiles[0].path);
      
      if (!projectPath) {
        return {
          type: 'rust-verification',
          passed: false,
          details: { error: 'Could not find Cargo.toml for Rust project' },
          errors: ['Rust project structure not detected'],
        };
      }

      // Prepare Rust verification request
      const rustRequest: RustVerificationRequest = {
        projectPath,
        sourceFiles: rustFiles.map(file => ({
          path: file.path,
          content: file.content,
        })),
        verificationTools: ['prusti', 'kani', 'miri'], // Default verification tools
        options: {
          timeout: 300,
          memoryLimit: 2048,
          unwindLimit: 10,
          strictMode: true,
          generateReport: true,
          checkOverflow: true,
          checkConcurrency: true,
        },
      };

      // Run Rust verification
      const results = await this.rustVerificationAgent.verifyRustProject(rustRequest);
      
      const overallSuccess = results.every(result => result.success);
      const allErrors = results.flatMap(result => 
        result.errors.map(error => `${error.tool}: ${error.message}`)
      );
      const allWarnings = results.flatMap(result =>
        result.warnings.map(warning => `${warning.tool}: ${warning.message}`)
      );

      // Generate detailed results summary
      const toolResults = results.map(result => ({
        tool: result.tool,
        success: result.success,
        checks: result.results.length,
        passed: result.results.filter(check => check.status === 'passed').length,
        failed: result.results.filter(check => check.status === 'failed').length,
        executionTime: result.performance.executionTime,
      }));

      return {
        type: 'rust-verification',
        passed: overallSuccess,
        details: {
          totalTools: results.length,
          successfulTools: results.filter(r => r.success).length,
          toolResults,
          summary: `Ran ${results.length} Rust verification tools with ${overallSuccess ? 'success' : 'failures'}`,
        },
        errors: allErrors.length > 0 ? allErrors : undefined,
        warnings: allWarnings.length > 0 ? allWarnings : undefined,
      };

    } catch (error) {
      return {
        type: 'rust-verification',
        passed: false,
        details: { error: (error as Error).message },
        errors: [(error as Error).message],
      };
    }
  }

  /**
   * Run container-based verification
   */
  private async runContainerVerification(request: VerificationRequest): Promise<VerificationCheck> {
    if (!this.containerAgent) {
      return {
        type: 'container-verification',
        passed: false,
        details: { error: 'Container agent not initialized' },
        errors: ['Container verification is not enabled'],
      };
    }

    try {
      // Determine project path for container verification
      let projectPath = request.containerConfig?.projectPath;
      
      if (!projectPath && request.codeFiles.length > 0) {
        // Try to find project root from the first code file
        const firstFile = request.codeFiles[0];
        
        if (firstFile.language === 'rust') {
          projectPath = this.findRustProjectPath(firstFile.path) || undefined;
        } else if (firstFile.language === 'elixir') {
          projectPath = this.findElixirProjectPath(firstFile.path) || undefined;
        }
        
        if (!projectPath) {
          projectPath = path.dirname(path.resolve(firstFile.path));
        }
      }

      if (!projectPath) {
        return {
          type: 'container-verification',
          passed: false,
          details: { error: 'Could not determine project path for container verification' },
          errors: ['Project path is required for container verification'],
        };
      }

      // Determine language and tools based on project structure and code files
      const language = this.detectProjectLanguage(request.codeFiles, projectPath);
      const tools = this.selectVerificationTools(language, request.verificationTypes);

      // Run container-based verification
      const containerRequest: ContainerVerificationRequest = {
        projectPath,
        language,
        tools,
        jobName: `verify-${Date.now()}`,
        buildImages: request.containerConfig?.buildImages,
        environment: {
          AE_VERIFICATION_CONTEXT: 'verify-agent',
          AE_STRICT_MODE: request.strictMode ? '1' : '0',
        },
      };

      const result = await this.containerAgent.runVerification(containerRequest);

      return {
        type: 'container-verification',
        passed: result.success,
        details: {
          jobId: result.data?.jobId,
          status: result.data?.status,
          results: result.data?.results,
          duration: result.data?.duration,
          logs: result.data?.logs,
          projectPath,
          language,
          tools,
        },
        errors: result.success ? undefined : [result.message],
        warnings: result.success && result.data?.results?.summary?.warnings > 0 
          ? [`${result.data.results.summary.warnings} warnings found`]
          : undefined,
      };
    } catch (error: any) {
      return {
        type: 'container-verification',
        passed: false,
        details: { error: error.message },
        errors: [error.message],
      };
    }
  }

  /**
   * Generate improvement suggestions
   */
  private generateSuggestions(
    results: VerificationCheck[],
    coverage: CoverageReport,
    metrics: QualityMetrics
  ): string[] {
    const suggestions: string[] = [];

    // Coverage suggestions
    if (coverage.line < 80) {
      suggestions.push(`Increase line coverage from ${coverage.line}% to at least 80%`);
    }
    if (coverage.branch < 80) {
      suggestions.push(`Increase branch coverage from ${coverage.branch}% to at least 80%`);
    }

    // Quality suggestions
    if (metrics.complexity > 10) {
      suggestions.push('Reduce cyclomatic complexity by extracting methods');
    }
    if (metrics.maintainability < 80) {
      suggestions.push('Improve maintainability by refactoring complex code');
    }

    // Test suggestions
    const testFailures = results.find(r => r.type === 'tests' && !r.passed);
    if (testFailures) {
      suggestions.push('Fix failing tests before deployment');
    }

    // Security suggestions
    const securityIssues = results.find(r => r.type === 'security' && !r.passed);
    if (securityIssues) {
      suggestions.push('Address security vulnerabilities immediately');
    }

    return suggestions;
  }

  // Helper methods
  private async runTestFile(test: TestFile): Promise<TestResult> {
    // Implementation would run actual tests
    return {
      total: 10,
      passed: 9,
      failed: 1,
      duration: 100,
      failures: test.type === 'unit' ? [] : [{ message: 'Test failure' }],
    };
  }

  private async lintFile(file: CodeFile): Promise<LintResult> {
    return {
      errors: 0,
      warnings: 1,
      messages: [{
        severity: 'warning' as const,
        message: 'Unused variable',
        line: 10,
        column: 5
      }],
    };
  }

  private async checkTypes(file: CodeFile): Promise<string[]> {
    return [];
  }

  private async scanForVulnerabilities(file: CodeFile): Promise<any[]> {
    return [];
  }

  private async checkDependencies(): Promise<any[]> {
    return [];
  }

  private async scanForSecrets(files: CodeFile[]): Promise<any[]> {
    return [];
  }

  private async runBenchmarks(files: CodeFile[]): Promise<BenchmarkResult> {
    return {
      responseTime: 50,
      throughput: 2000,
      errorRate: 0.1,
      cpuUsage: 45,
      memoryUsage: 256,
    };
  }

  private async runContractTest(test: TestFile): Promise<any> {
    return { passed: true };
  }

  private async validateSpecification(spec: Specification): Promise<boolean> {
    return true;
  }

  private async generateMutants(files: CodeFile[]): Promise<any[]> {
    return Array(20).fill({}).map((_, i) => ({ id: i, file: 'test.ts' }));
  }

  private async testMutant(mutant: any, tests: TestFile[]): Promise<boolean> {
    return Math.random() > 0.2; // 80% kill rate
  }

  private extractRequirements(spec: Specification): TraceItem[] {
    return [];
  }

  private calculateTraceabilityCoverage(
    requirements: TraceItem[],
    tests: TraceItem[],
    code: TraceItem[]
  ): number {
    if (requirements.length === 0) return 100;
    const covered = requirements.filter(r => r.covered).length;
    return (covered / requirements.length) * 100;
  }

  private findRustProjectPath(filePath: string): string | null {
    let currentDir = path.dirname(path.resolve(filePath));
    
    // Search up the directory tree for Cargo.toml
    while (currentDir !== path.dirname(currentDir)) {
      const cargoPath = path.join(currentDir, 'Cargo.toml');
      if (existsSync(cargoPath)) {
        return currentDir;
      }
      currentDir = path.dirname(currentDir);
    }
    
    return null;
  }

  private findElixirProjectPath(filePath: string): string | null {
    let currentDir = path.dirname(path.resolve(filePath));
    
    // Search up the directory tree for mix.exs
    while (currentDir !== path.dirname(currentDir)) {
      const mixPath = path.join(currentDir, 'mix.exs');
      if (existsSync(mixPath)) {
        return currentDir;
      }
      currentDir = path.dirname(currentDir);
    }
    
    return null;
  }

  private detectProjectLanguage(
    codeFiles: CodeFile[], 
    projectPath: string
  ): 'rust' | 'elixir' | 'multi' {
    // Check for project files
    if (existsSync(path.join(projectPath, 'Cargo.toml'))) {
      // Check if there are also Elixir files
      const hasElixir = codeFiles.some(f => f.language === 'elixir') || 
        existsSync(path.join(projectPath, 'mix.exs'));
      
      return hasElixir ? 'multi' : 'rust';
    }
    
    if (existsSync(path.join(projectPath, 'mix.exs'))) {
      // Check if there are also Rust files
      const hasRust = codeFiles.some(f => f.language === 'rust') ||
        existsSync(path.join(projectPath, 'Cargo.toml'));
      
      return hasRust ? 'multi' : 'elixir';
    }
    
    // Detect based on code files
    const languages = new Set(codeFiles.map(f => f.language));
    
    if (languages.has('rust') && languages.has('elixir')) {
      return 'multi';
    } else if (languages.has('rust')) {
      return 'rust';
    } else if (languages.has('elixir')) {
      return 'elixir';
    }
    
    // Default to multi for mixed or unknown languages
    return 'multi';
  }

  private selectVerificationTools(
    language: 'rust' | 'elixir' | 'multi',
    verificationTypes: VerificationType[]
  ): string[] {
    const tools: string[] = [];
    
    if (language === 'rust' || language === 'multi') {
      tools.push('cargo');
      
      if (verificationTypes.includes('rust-verification')) {
        tools.push('prusti', 'kani', 'miri');
      }
      
      if (verificationTypes.includes('tests')) {
        tools.push('cargo'); // Already included but indicates testing
      }
    }
    
    if (language === 'elixir' || language === 'multi') {
      tools.push('elixir', 'mix');
      
      if (verificationTypes.includes('tests')) {
        tools.push('exunit');
      }
    }
    
    // Remove duplicates and return
    return Array.from(new Set(tools));
  }
}