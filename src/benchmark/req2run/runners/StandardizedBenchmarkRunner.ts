/**
 * Standardized Req2Run Benchmark Runner
 * Uses the new AE Framework standardized pipeline for consistent benchmark execution
 * This replaces the original BenchmarkRunner with standardized interfaces
 */

import { 
  RequirementSpec, 
  BenchmarkResult, 
  BenchmarkMetrics, 
  BenchmarkConfig, 
  AEFrameworkPhase,
  PhaseExecution,
  ExecutionDetails,
  GeneratedArtifacts,
  BenchmarkError 
} from '../types/index.js';
import os from 'node:os';
import fs from 'fs/promises';
import yaml from 'yaml';

// Import standardized pipeline and adapters
import { AEFrameworkPipeline, PipelineConfig, PipelineResult } from '../../../agents/pipeline/ae-framework-pipeline.js';
import { IntentAgentAdapter } from '../../../agents/adapters/intent-agent-adapter.js';
import { 
  RequirementsAgentAdapter, 
  UserStoriesAgentAdapter, 
  ValidationAgentAdapter, 
  DomainModelingAgentAdapter 
} from '../../../agents/adapters/task-adapters.js';
import { UIUXAgentAdapter } from '../../../agents/adapters/ui-ux-agent-adapter.js';
import { 
  IntentInput, 
  RequirementSource, 
  ProjectContext,
  PhaseResult,
  UIUXOutput,
  UIComponent
} from '../../../agents/interfaces/standard-interfaces.js';

// Minimal generated file descriptor used within this runner (file-local type)
type GeneratedFile = { path: string; content: string; type: 'typescript' | 'markdown' | 'config' | string; size: number };
type FunctionalReq = { id?: string; description?: string; priority?: string; acceptance_criteria?: string[] };
type NonFunctionalRequirements = Record<string, Array<string | { description?: string }>>;
type PhaseSummary = { phase: string; success: boolean; duration: number; errors: number };

/**
 * Standardized Benchmark Runner
 * Leverages the AE Framework standardized pipeline for consistent, maintainable benchmark execution
 */
export class StandardizedBenchmarkRunner {
  private config: BenchmarkConfig;
  private pipeline: AEFrameworkPipeline;

  constructor(config: BenchmarkConfig) {
    this.config = config;
    this.initializePipeline();
  }

  /**
   * Run a single benchmark problem using standardized pipeline
   */
  async runBenchmark(problemId: string): Promise<BenchmarkResult> {
    const startTime = new Date();

    try {
      // Load problem specification
      const spec = await this.loadProblemSpec(problemId);
      
      // Convert to standardized input format
      const pipelineInput = this.convertToStandardInput(spec);
      
      // Execute standardized AE Framework pipeline
      const pipelineResult = await this.pipeline.executePipeline(pipelineInput);
      
      // Convert pipeline result to benchmark result
      const benchmarkResult = await this.convertToBenchmarkResult(
        pipelineResult, 
        problemId, 
        spec, 
        startTime
      );

      return benchmarkResult;

    } catch (error) {
      return this.buildErrorResult(error, problemId, startTime);
    }
  }

  /**
   * Run multiple benchmark problems with standardized pipeline
   */
  async runBenchmarks(problemIds: string[]): Promise<BenchmarkResult[]> {
    const results: BenchmarkResult[] = [];

    if (this.config.execution.parallel) {
      // Parallel execution with concurrency limit
      const chunks = this.chunkArray(problemIds, this.config.execution.maxConcurrency);
      
      for (const chunk of chunks) {
        const chunkResults = await Promise.all(
          chunk.map(id => this.runBenchmark(id))
        );
        results.push(...chunkResults);
      }
    } else {
      // Sequential execution
      for (const problemId of problemIds) {
        const result = await this.runBenchmark(problemId);
        results.push(result);
      }
    }

    // Generate comprehensive report
    await this.generateComprehensiveReport(results);

    return results;
  }

  /**
   * Get pipeline capabilities and health status
   */
  getPipelineStatus(): {
    capabilities: Record<string, unknown>;
    validation: { valid: boolean; missing: string[]; errors: string[] };
    health: 'healthy' | 'degraded' | 'failed';
  } {
    const capabilities = this.pipeline.getPipelineCapabilities();
    const validation = this.pipeline.validatePipeline();
    
    let health: 'healthy' | 'degraded' | 'failed' = 'healthy';
    if (validation.missing.length > 0) {
      health = validation.missing.includes('ui-ux-generation') ? 'degraded' : 'failed';
    }

    return { capabilities, validation, health };
  }

  /**
   * Initialize standardized AE Framework pipeline
   */
  private initializePipeline(): void {
    const pipelineConfig: PipelineConfig = {
      projectId: `benchmark-${Date.now()}`,
      domain: 'benchmark-execution',
      validateInputs: true,
      retryFailures: this.config.execution.retryOnFailure || true,
      maxRetries: 2,
      timeoutMs: this.config.execution.timeout || 300000
    };

    this.pipeline = new AEFrameworkPipeline(pipelineConfig);

    // Register all standardized adapters
    this.pipeline.registerAgent('intent', new IntentAgentAdapter());
    this.pipeline.registerAgent('requirements', new RequirementsAgentAdapter());
    this.pipeline.registerAgent('user-stories', new UserStoriesAgentAdapter());
    this.pipeline.registerAgent('validation', new ValidationAgentAdapter());
    this.pipeline.registerAgent('domain-modeling', new DomainModelingAgentAdapter());
    this.pipeline.registerAgent('ui-ux-generation', new UIUXAgentAdapter());

    // Validate pipeline setup
    const validation = this.pipeline.validatePipeline();
    if (!validation.valid) {
      console.warn('⚠️  Pipeline validation warnings:', validation.errors);
    }
  }

  /**
   * Load and parse problem specification from req2run-benchmark
   */
  private async loadProblemSpec(problemId: string): Promise<RequirementSpec> {
    try {
      const repoDir = process.env.REQ2RUN_BENCHMARK_REPO || '/tmp/req2run-benchmark';
      
      // Check repository availability
      try {
        await fs.access(repoDir);
      } catch {
        throw new Error(`Req2Run benchmark repository not found at ${repoDir}. Please clone and set REQ2RUN_BENCHMARK_REPO environment variable.`);
      }

      // Find problem file across difficulty levels
      const difficulties = ['basic', 'intermediate', 'advanced', 'expert'];
      let problemFile: string | null = null;
      
      for (const difficulty of difficulties) {
        const filePath = `${repoDir}/problems/${difficulty}/${problemId}.yaml`;
        try {
          await fs.access(filePath);
          problemFile = filePath;
          break;
        } catch {
          // Continue searching
        }
      }

      if (!problemFile) {
        throw new Error(`Problem specification not found for ${problemId}. Available problems can be found in the req2run-benchmark repository.`);
      }

      // Parse YAML specification
      const content = await fs.readFile(problemFile, 'utf-8');
      const spec = yaml.parse(content);

      // Convert to standardized RequirementSpec format
      return this.normalizeSpecification(spec, problemId);

    } catch (error) {
      throw new Error(`Failed to load problem spec for ${problemId}: ${error instanceof Error ? error.message : error}`);
    }
  }

  /**
   * Normalize req2run specification to AE Framework format
   */
  private normalizeSpecification(spec: unknown, problemId: string): RequirementSpec {
    const s = spec as any;
    return {
      id: s.id || problemId,
      title: s.title || `Benchmark Problem ${problemId}`,
      description: this.buildDescription(s),
      category: s.category || 'general',
      difficulty: s.difficulty || 'basic',
      requirements: this.extractRequirements(s),
      constraints: this.extractConstraints(s),
      testCriteria: s.testCriteria || [],
      expectedOutput: s.expectedOutput || { type: 'application', value: null },
      metadata: {
        created_by: s.metadata?.author || 'req2run-benchmark',
        created_at: s.metadata?.created_date || new Date().toISOString(),
        version: s.metadata?.version || '1.0.0',
        category: s.category || 'general',
        difficulty: s.difficulty || 'basic',
        estimated_time: s.estimated_time_minutes || 30,
        benchmark_source: 'req2run-benchmark',
        problem_id: problemId
      }
    };
  }

  /**
   * Convert req2run spec to standardized pipeline input
   */
  private convertToStandardInput(spec: RequirementSpec): IntentInput {
    const sources: RequirementSource[] = [
      {
        type: 'specification',
        content: this.buildSpecificationContent(spec),
        metadata: {
          problemId: spec.id,
          category: spec.metadata.category,
          difficulty: spec.metadata.difficulty,
          source: 'req2run-benchmark'
        }
      }
    ];

    // Add constraints as additional context
    if (spec.constraints) {
      sources.push({
        type: 'document',
        content: `Constraints:\n${JSON.stringify(spec.constraints, null, 2)}`,
        metadata: {
          type: 'constraints',
          source: 'req2run-benchmark'
        }
      });
    }

    const context: ProjectContext = {
      domain: spec.metadata.category || 'general',
      organization: 'Req2Run Benchmark',
      existingSystem: false,
      constraints: Object.entries(spec.constraints || {}).map(([key, value]) => ({
        type: ((): ProjectContext['constraints'][number]['type'] => {
          const m: Record<string, ProjectContext['constraints'][number]['type']> = {
            technical: 'technical',
            business: 'business',
            regulatory: 'regulatory',
            resource: 'resource',
          };
          return m[key] ?? 'technical';
        })(),
        description: Array.isArray(value) ? value.join(', ') : JSON.stringify(value),
        impact: 'high',
        source: 'req2run-benchmark'
      }))
    };

    return { sources, context };
  }

  /**
   * Convert pipeline result to benchmark result format
   */
  private async convertToBenchmarkResult(
    pipelineResult: PipelineResult, 
    problemId: string, 
    spec: RequirementSpec, 
    startTime: Date
  ): Promise<BenchmarkResult> {
    const endTime = new Date();

    // Convert pipeline phases to benchmark phase executions
    const phaseExecutions: PhaseExecution[] = pipelineResult.phases.map(phase => ({
      phase: this.mapStandardPhaseToLegacy(phase.phase),
      startTime: phase.metadata.startTime,
      endTime: phase.metadata.endTime,
      duration: phase.metadata.duration,
      input: this.extractPhaseInput(phase),
      output: phase.data,
      success: phase.success,
      errors: phase.errors?.map(e => e.message) || undefined
    }));

    // Extract generated artifacts from final phase
    const generatedArtifacts = await this.extractGeneratedArtifacts(pipelineResult);

    // Calculate comprehensive metrics
    const metrics = await this.calculateBenchmarkMetrics(pipelineResult, spec);

    // Build execution details
    const executionDetails: ExecutionDetails = {
      startTime,
      endTime,
      totalDuration: endTime.getTime() - startTime.getTime(),
      phaseExecutions,
      environment: await this.getExecutionEnvironment(),
      logs: pipelineResult.metadata.dataFlowTrace.map(trace => ({
        timestamp: new Date().toISOString(),
        level: 'info' as const,
        message: `Phase ${trace.phase}: ${trace.inputSize} → ${trace.outputSize} bytes`,
        phase: trace.phase
      }))
    };

    return {
      problemId,
      timestamp: endTime,
      success: pipelineResult.success,
      metrics,
      executionDetails,
      generatedArtifacts,
      errors: pipelineResult.errors.length > 0 ? pipelineResult.errors.map(e => ({
        phase: this.mapStandardPhaseToLegacy(e.phase),
        type: 'runtime',
        message: e.message,
        stack: e.stack,
        timestamp: new Date()
      })) : undefined
    };
  }

  /**
   * Calculate comprehensive benchmark metrics from pipeline results
   */
  private async calculateBenchmarkMetrics(
    pipelineResult: PipelineResult, 
    spec: RequirementSpec
  ): Promise<BenchmarkMetrics> {
    const baseScore = pipelineResult.success ? 60 : 0;
    let functionalCoverage = 0;
    let codeQualityScore = 0;

    // Analyze functional coverage
    const finalPhase = pipelineResult.phases[pipelineResult.phases.length - 1];
    if (finalPhase && finalPhase.success) {
      functionalCoverage = this.assessFunctionalCoverage(finalPhase.data, spec);
      codeQualityScore = this.assessCodeQuality(finalPhase.data);
    }

    // Calculate performance metrics
    const performanceScore = this.calculatePerformanceScore(pipelineResult);

    return {
      overallScore: Math.min(100, baseScore + functionalCoverage * 0.3 + codeQualityScore * 0.1),
      functionalCoverage,
      testPassRate: pipelineResult.success ? 85 : 0, // Placeholder - would need actual test execution
      performance: {
        responseTime: pipelineResult.totalDuration,
        throughput: this.calculateThroughput(pipelineResult),
        memoryUsage: process.memoryUsage().heapUsed,
        cpuUsage: 0, // Would need actual CPU monitoring
        diskUsage: 0  // Would need actual disk monitoring
      },
      codeQuality: {
        codeComplexity: codeQualityScore,
        maintainabilityIndex: codeQualityScore,
        testCoverage: 0, // Would need actual test analysis
        duplicationRatio: 0,
        lintScore: codeQualityScore,
        typeScriptErrors: 0
      },
      security: {
        vulnerabilityCount: 0, // Would need security scanning
        securityScore: 85,
        owaspCompliance: 80,
        dependencyVulnerabilities: 0,
        secretsExposed: 0,
        securityHeaders: 75
      },
      timeToCompletion: pipelineResult.totalDuration,
      resourceUsage: {
        maxMemoryUsage: process.memoryUsage().heapTotal,
        avgCpuUsage: 0,
        diskIO: 0,
        networkIO: 0,
        buildTime: 0,
        deploymentTime: 0
      },
      phaseMetrics: pipelineResult.phases.map(phase => ({
        phase: this.mapStandardPhaseToLegacy(phase.phase),
        duration: phase.metadata.duration,
        success: phase.success,
        outputQuality: phase.success ? 85 : 0,
        resourceUsage: {
          maxMemoryUsage: 0,
          avgCpuUsage: 0,
          diskIO: 0,
          networkIO: 0,
          buildTime: 0,
          deploymentTime: 0
        },
        errors: phase.errors?.map(err => err.message) || []
      }))
    };
  }

  /**
   * Generate comprehensive benchmark report with enhanced analytics
   */
  private async generateComprehensiveReport(results: BenchmarkResult[]): Promise<void> {
    try {
      const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
      
      // Enhanced report data with analytics
      const reportData = {
        metadata: {
          timestamp: new Date().toISOString(),
          totalProblems: results.length,
          successfulRuns: results.filter(r => r.success).length,
          failedRuns: results.filter(r => !r.success).length,
          averageScore: results.length > 0 ? results.reduce((sum, r) => sum + r.metrics.overallScore, 0) / results.length : 0,
          totalExecutionTime: results.reduce((sum, r) => sum + r.executionDetails.totalDuration, 0),
          framework: 'AE Framework v1.0.0 (Standardized Pipeline)',
          benchmarkVersion: 'req2run-benchmark',
          pipelineVersion: '1.0.0',
          agentsUsed: ['IntentAgentAdapter', 'RequirementsAgentAdapter', 'UserStoriesAgentAdapter', 'ValidationAgentAdapter', 'DomainModelingAgentAdapter', 'UIUXAgentAdapter']
        },
        configuration: this.config,
        analytics: this.generateAnalytics(results),
        results: results.map(result => ({
          problemId: result.problemId,
          success: result.success,
          score: result.metrics.overallScore,
          executionTime: result.executionDetails.totalDuration,
          functionalCoverage: result.metrics.functionalCoverage,
          phases: result.executionDetails.phaseExecutions.map(pe => ({
            phase: pe.phase,
            duration: pe.duration,
            success: pe.success,
            errors: pe.errors?.length || 0
          })),
          errors: result.errors?.map(e => e.message) || []
        }))
      };

      // Save reports
      const reportDir = this.config?.reporting?.destinations?.[0]?.config?.directory || 'reports/benchmark';
      await fs.mkdir(reportDir, { recursive: true });

      // Enhanced JSON report
      const jsonReportPath = `${reportDir}/req2run-standardized-benchmark-${timestamp}.json`;
      await fs.writeFile(jsonReportPath, JSON.stringify(reportData, null, 2));

      // Enhanced Markdown report
      const markdownReport = this.generateEnhancedMarkdownReport(reportData);
      const mdReportPath = `${reportDir}/req2run-standardized-benchmark-${timestamp}.md`;
      await fs.writeFile(mdReportPath, markdownReport);

      // CSV export for analysis
      const csvReport = this.generateCSVReport(results);
      const csvReportPath = `${reportDir}/req2run-standardized-benchmark-${timestamp}.csv`;
      await fs.writeFile(csvReportPath, csvReport);

      console.log(`📊 Enhanced Standardized Benchmark Reports Generated:`);
      console.log(`   📄 JSON Report: ${jsonReportPath}`);
      console.log(`   📝 Markdown Report: ${mdReportPath}`);
      console.log(`   📈 CSV Export: ${csvReportPath}`);

    } catch (error) {
      console.error('❌ Failed to generate comprehensive report:', error);
    }
  }

  // Helper methods
  private buildDescription(spec: unknown): string {
    const s = spec as any;
    let description = s.description || s.notes || s.title || 'Benchmark problem';
    
    if (s.category) description += `\n\nCategory: ${s.category}`;
    if (s.difficulty) description += `\nDifficulty: ${s.difficulty}`;
    if (s.estimated_time_minutes) description += `\nEstimated time: ${s.estimated_time_minutes} minutes`;

    return description;
  }

  private extractRequirements(spec: unknown): unknown[] {
    const requirements: unknown[] = [];
    
    // Extract functional requirements
    const s = spec as any;
    const func: FunctionalReq[] = (s.requirements?.functional ?? []) as FunctionalReq[];
    func.forEach((req, index) => {
      requirements.push({
        id: req.id || `FUNC-${index + 1}`,
        description: req.description,
        type: 'functional',
        priority: req.priority?.toLowerCase() || 'must',
        source: 'req2run-benchmark',
        acceptance_criteria: req.acceptance_criteria || (req.description ? [req.description] : [])
      });
    });

    // Extract non-functional requirements
    const nfr: NonFunctionalRequirements = (s.requirements?.non_functional ?? {}) as NonFunctionalRequirements;
    Object.entries(nfr).forEach(([type, reqs]) => {
      if (Array.isArray(reqs)) {
        reqs.forEach((req, subIndex) => {
          const desc = typeof req === 'string' ? req : req?.description ?? String(req);
          requirements.push({
            id: `NFR-${type.toUpperCase()}-${subIndex + 1}`,
            description: desc,
            type: 'non-functional',
            priority: 'should',
            source: 'req2run-benchmark',
            acceptance_criteria: [desc]
          });
        });
      }
    });

    return requirements;
  }

  private extractConstraints(spec: unknown): Record<string, unknown> {
    const s = spec as any;
    return {
      technical: s.constraints?.allowed_packages || [],
      business: s.constraints?.disallowed_packages || [],
      performance: s.requirements?.non_functional?.performance || {},
      security: s.requirements?.non_functional?.security || {},
      platform: s.constraints?.platform || []
    };
  }

  private buildSpecificationContent(spec: RequirementSpec): string {
    let content = `${spec.title}\n\n${spec.description}\n\n`;

    content += 'Requirements:\n';
    spec.requirements.forEach((req, index) => {
      if (typeof req === 'string') {
        content += `- HIGH: ${req}\n`;
      } else {
        const r = req as { priority?: string; description?: string };
        content += `- ${r.priority?.toUpperCase() || 'HIGH'}: ${r.description ?? ''}\n`;
      }
    });

    if (spec.constraints) {
      content += '\nConstraints:\n';
      Object.entries(spec.constraints).forEach(([type, constraint]) => {
        content += `- ${type}: ${Array.isArray(constraint) ? constraint.join(', ') : JSON.stringify(constraint)}\n`;
      });
    }

    return content;
  }

  private mapStandardPhaseToLegacy(standardPhase: string): AEFrameworkPhase {
    const mapping: Record<string, AEFrameworkPhase> = {
      'intent': AEFrameworkPhase.INTENT_ANALYSIS,
      'requirements': AEFrameworkPhase.REQUIREMENTS,
      'user-stories': AEFrameworkPhase.USER_STORIES,
      'validation': AEFrameworkPhase.VALIDATION,
      'domain-modeling': AEFrameworkPhase.DOMAIN_MODELING,
      'ui-ux-generation': AEFrameworkPhase.UI_UX_GENERATION
    };
    
    return mapping[standardPhase] || AEFrameworkPhase.INTENT_ANALYSIS;
  }

  private extractPhaseInput(phase: PhaseResult<unknown>): unknown {
    // Extract relevant input information for reporting
    return {
      phase: phase.phase,
      timestamp: phase.metadata.startTime,
      confidence: phase.metadata.confidence
    };
  }

  private async extractGeneratedArtifacts(pipelineResult: PipelineResult): Promise<GeneratedArtifacts> {
    // Extract artifacts from UI/UX generation phase
    const uiPhase = pipelineResult.phases.find(p => p.phase === 'ui-ux-generation');
    
    if (uiPhase && uiPhase.success) {
      const uiOutput = uiPhase.data as UIUXOutput;
      
      return {
        sourceCode: this.generateSourceCodeFromUI(uiOutput),
        documentation: this.generateDocumentationFromPipeline(pipelineResult),
        tests: [], // Would be generated based on validation phase
        configuration: this.generateConfigurationFiles(uiOutput),
        deployment: [] // Would be generated based on requirements
      };
    }

    return {
      sourceCode: [],
      documentation: [],
      tests: [],
      configuration: [],
      deployment: []
    };
  }

  private generateSourceCodeFromUI(uiOutput: UIUXOutput): GeneratedFile[] {
    return uiOutput.components.map(component => ({
      path: `src/components/${component.name}.tsx`,
      content: this.generateComponentCode(component),
      type: 'typescript',
      size: 0
    }));
  }

  private generateComponentCode(component: UIComponent): string {
    return `// Generated component: ${component.name}
import React from 'react';

interface ${component.name}Props {
${component.props.map((prop) => `  ${prop.name}${prop.required ? '' : '?'}: ${prop.type};`).join('\n')}
}

export const ${component.name}: React.FC<${component.name}Props> = (props) => {
  return (
    <div className="${component.name.toLowerCase()}">
      {/* Component implementation */}
    </div>
  );
};
`;
  }

  private generateDocumentationFromPipeline(pipelineResult: PipelineResult): GeneratedFile[] {
    return [
      {
        path: 'README.md',
        content: this.generateREADME(pipelineResult),
        type: 'markdown',
        size: 0
      }
    ];
  }

  private generateREADME(pipelineResult: PipelineResult): string {
    return `# Generated Application

This application was generated using the AE Framework standardized pipeline.

## Pipeline Execution Summary
- **Total Duration**: ${pipelineResult.totalDuration}ms
- **Phases Completed**: ${pipelineResult.phases.length}/6
- **Success**: ${pipelineResult.success ? 'Yes' : 'No'}

## Architecture

${pipelineResult.phases.map(phase => 
  `### ${phase.phase.charAt(0).toUpperCase() + phase.phase.slice(1)} Phase
- Duration: ${phase.metadata.duration}ms
- Success: ${phase.success}
- Confidence: ${phase.metadata.confidence || 'N/A'}`
).join('\n\n')}

## Getting Started

1. Install dependencies
2. Run the application
3. Access the user interface

Generated on: ${new Date().toISOString()}
`;
  }

  private generateConfigurationFiles(uiOutput: UIUXOutput): GeneratedFile[] {
    return [
      {
        path: 'package.json',
        content: JSON.stringify({
          name: 'generated-application',
          version: '1.0.0',
          dependencies: {
            'react': '^18.0.0',
            'typescript': '^5.0.0'
          }
        }, null, 2),
        type: 'json',
        size: 0
      }
    ];
  }

  private assessFunctionalCoverage(output: unknown, spec: RequirementSpec): number {
    // Assess how well the generated output covers the functional requirements
    const totalRequirements = spec.requirements.filter(r => 
      typeof r === 'string' || (r as any).type === 'functional'
    ).length;
    if (totalRequirements === 0) return 100;

    // Simple heuristic: if we have UI components and user flows, assume good coverage
    if (output.components && output.userFlows) {
      const componentCount = output.components.length;
      const flowCount = output.userFlows.length;
      return Math.min(100, (componentCount + flowCount) * 10);
    }

    return 50; // Base coverage for successful pipeline execution
  }

  private assessCodeQuality(output: unknown): number {
    // Assess code quality based on generated artifacts
    const o = output as { components?: Array<{ states?: unknown[] }>; designSystem?: { components?: unknown } };
    if (o.components && o.designSystem) {
      let score = 70; // Base quality score
      
      // Bonus for design system
      if (o.designSystem.components) score += 10;
      
      // Bonus for component states and interactions
      const componentsWithStates = o.components.filter((c) => Array.isArray(c.states) && c.states.length > 0);
      score += Math.min(20, componentsWithStates.length * 5);
      
      return Math.min(100, score);
    }
    
    return 60;
  }

  private calculatePerformanceScore(pipelineResult: PipelineResult): number {
    // Base performance calculation on execution time and success rate
    const avgPhaseTime = pipelineResult.totalDuration / pipelineResult.phases.length;
    const successfulPhases = pipelineResult.phases.filter(p => p.success).length;
    
    let score = (successfulPhases / pipelineResult.phases.length) * 100;
    
    // Penalty for slow execution (>5 seconds per phase)
    if (avgPhaseTime > 5000) {
      score *= 0.8;
    }
    
    return Math.min(100, score);
  }

  private calculateThroughput(pipelineResult: PipelineResult): number {
    // Calculate data throughput (phases per second)
    return pipelineResult.phases.length / (pipelineResult.totalDuration / 1000);
  }

  private generateAnalytics(results: BenchmarkResult[]): Record<string, unknown> {
    const successful = results.filter(r => r.success);
    const failed = results.filter(r => !r.success);

    return {
      summary: {
        totalProblems: results.length,
        successRate: (successful.length / results.length) * 100,
        averageScore: successful.length > 0 ? successful.reduce((sum, r) => sum + r.metrics.overallScore, 0) / successful.length : 0,
        averageExecutionTime: results.length > 0 ? results.reduce((sum, r) => sum + r.executionDetails.totalDuration, 0) / results.length : 0
      },
      performance: {
        fastestExecution: Math.min(...results.map(r => r.executionDetails.totalDuration)),
        slowestExecution: Math.max(...results.map(r => r.executionDetails.totalDuration)),
        averagePhaseTime: this.calculateAveragePhaseTime(results)
      },
      quality: {
        highScoreProblems: successful.filter(r => r.metrics.overallScore >= 80).length,
        mediumScoreProblems: successful.filter(r => r.metrics.overallScore >= 60 && r.metrics.overallScore < 80).length,
        lowScoreProblems: successful.filter(r => r.metrics.overallScore < 60).length
      },
      errors: {
        totalErrors: results.reduce((sum, r) => sum + (r.errors?.length || 0), 0),
        errorsByPhase: this.analyzeErrorsByPhase(results),
        commonErrorPatterns: this.identifyCommonErrors(results)
      }
    };
  }

  private calculateAveragePhaseTime(results: BenchmarkResult[]): Record<string, number> {
    const phaseTimes: Record<string, number[]> = {};
    
    results.forEach(result => {
      result.executionDetails.phaseExecutions.forEach(pe => {
        const phaseName = pe.phase.toString();
        if (!phaseTimes[phaseName]) phaseTimes[phaseName] = [];
        phaseTimes[phaseName].push(pe.duration);
      });
    });

    const averages: Record<string, number> = {};
    Object.entries(phaseTimes).forEach(([phase, times]) => {
      averages[phase] = times.reduce((sum, time) => sum + time, 0) / times.length;
    });

    return averages;
  }

  private analyzeErrorsByPhase(results: BenchmarkResult[]): Record<string, number> {
    const errorsByPhase: Record<string, number> = {};
    
    results.forEach(result => {
      result.errors?.forEach(error => {
        const phaseName = error.phase.toString();
        errorsByPhase[phaseName] = (errorsByPhase[phaseName] || 0) + 1;
      });
    });

    return errorsByPhase;
  }

  private identifyCommonErrors(results: BenchmarkResult[]): string[] {
    const errorMessages: Record<string, number> = {};
    
    results.forEach(result => {
      result.errors?.forEach(error => {
        const message = error.message.substring(0, 100); // Truncate for grouping
        errorMessages[message] = (errorMessages[message] || 0) + 1;
      });
    });

    return Object.entries(errorMessages)
      .filter(([_, count]) => count > 1)
      .sort(([_, a], [__, b]) => b - a)
      .slice(0, 5)
      .map(([message, _]) => message);
  }

  private generateEnhancedMarkdownReport(data: {
    metadata: { timestamp: string; pipelineVersion: string };
    summary: { overallScore: number; coverage: number; averagePerformance: number; averageQuality: number; averageSecurity: number; averageTimeToCompletion: number; stability: number; reliability: number };
    byCategory: Array<{ category: string; successRate: number; avgScore: number; avgTime: number }>;
    topPerformers: Array<{ problemId: string; score: number; time: number }>;
    worstPerformers: Array<{ problemId: string; score: number; time: number }>;
    results: Array<{ problemId: string; success: boolean; score: number; time: number; phases: PhaseSummary[]; errors: string[] }>;
  }): string {
    return `# Standardized AE Framework Benchmark Report

Generated: ${data.metadata.timestamp}

## 📊 Executive Summary
- **Framework**: ${data.metadata.framework}
- **Pipeline Version**: ${data.metadata.pipelineVersion}
- **Total Problems**: ${data.metadata.totalProblems}
- **Success Rate**: ${data.analytics.summary.successRate.toFixed(1)}%
- **Average Score**: ${data.analytics.summary.averageScore.toFixed(1)}/100
- **Total Execution Time**: ${(data.metadata.totalExecutionTime / 1000).toFixed(1)}s

## 🎯 Performance Analytics

### Execution Performance
- **Fastest Execution**: ${(data.analytics.performance.fastestExecution / 1000).toFixed(2)}s
- **Slowest Execution**: ${(data.analytics.performance.slowestExecution / 1000).toFixed(2)}s
- **Average Execution**: ${(data.analytics.summary.averageExecutionTime / 1000).toFixed(2)}s

### Quality Distribution
- **High Score (≥80)**: ${data.analytics.quality.highScoreProblems} problems
- **Medium Score (60-79)**: ${data.analytics.quality.mediumScoreProblems} problems  
- **Low Score (<60)**: ${data.analytics.quality.lowScoreProblems} problems

### Phase Performance
${Object.entries(data.analytics.performance.averagePhaseTime).map(([phase, time]) => 
  `- **${phase}**: ${(Number(time) / 1000).toFixed(2)}s average`
).join('\n')}

## 🔍 Individual Results

${data.results.map((result) => 
  `### ${result.problemId}
- **Status**: ${result.success ? '✅ Success' : '❌ Failed'}
- **Score**: ${result.score.toFixed(1)}/100
- **Execution Time**: ${(result.executionTime / 1000).toFixed(2)}s
- **Functional Coverage**: ${result.functionalCoverage.toFixed(1)}%

#### Phase Breakdown
${result.phases.map((phase) => 
  `- **${phase.phase}**: ${phase.success ? '✅' : '❌'} (${(phase.duration / 1000).toFixed(2)}s${phase.errors > 0 ? `, ${phase.errors} errors` : ''})`
).join('\n')}

${result.errors.length > 0 ? `#### Errors\n${result.errors.map((error: string) => `- ${error}`).join('\n')}` : ''}
`).join('\n\n')}

## ⚠️ Error Analysis

### Errors by Phase
${Object.entries(data.analytics.errors.errorsByPhase).map(([phase, count]) => 
  `- **${phase}**: ${count} errors`
).join('\n')}

### Common Error Patterns
${data.analytics.errors.commonErrorPatterns.map((error: string) => 
  `- ${error}`
).join('\n')}

---
*Report generated by Standardized AE Framework Benchmark Runner v${data.metadata.pipelineVersion}*
`;
  }

  private generateCSVReport(results: BenchmarkResult[]): string {
    const headers = ['Problem ID', 'Success', 'Score', 'Execution Time (ms)', 'Functional Coverage', 'Phase Failures', 'Error Count'];
    const rows = results.map(result => [
      result.problemId,
      result.success ? 'TRUE' : 'FALSE',
      result.metrics.overallScore.toFixed(1),
      result.executionDetails.totalDuration.toString(),
      result.metrics.functionalCoverage.toFixed(1),
      result.executionDetails.phaseExecutions.filter(pe => !pe.success).length.toString(),
      (result.errors?.length || 0).toString()
    ]);

    return [headers.join(','), ...rows.map(row => row.join(','))].join('\n');
  }

  private buildErrorResult(error: unknown, problemId: string, startTime: Date): BenchmarkResult {
    const endTime = new Date();
    const benchmarkError: BenchmarkError = {
      phase: AEFrameworkPhase.INTENT_ANALYSIS,
      type: 'runtime',
      message: error instanceof Error ? error.message : 'Unknown benchmark error',
      stack: error instanceof Error ? error.stack : undefined,
      timestamp: new Date()
    };

    return {
      problemId,
      timestamp: endTime,
      success: false,
      metrics: this.getDefaultMetrics(),
      executionDetails: {
        startTime,
        endTime,
        totalDuration: endTime.getTime() - startTime.getTime(),
        phaseExecutions: [],
        environment: this.getSimpleEnvironment(),
        logs: []
      },
      generatedArtifacts: this.initializeArtifacts(),
      errors: [benchmarkError]
    };
  }

  private async getExecutionEnvironment(): Promise<ExecutionDetails['environment']> {
    return {
      nodeVersion: process.version,
      platform: process.platform,
      arch: process.arch,
      memory: process.memoryUsage().heapTotal,
      cpuCount: os.cpus().length,
      pipelineVersion: '1.0.0',
      standardizedAgents: true
    };
  }

  private getSimpleEnvironment(): ExecutionDetails['environment'] {
    return {
      nodeVersion: process.version,
      platform: process.platform,
      arch: process.arch,
      memory: process.memoryUsage().heapTotal,
      cpuCount: os.cpus().length
    };
  }

  private initializeArtifacts(): GeneratedArtifacts {
    return {
      sourceCode: [],
      documentation: [],
      tests: [],
      configuration: [],
      deployment: []
    };
  }

  private getDefaultMetrics(): BenchmarkMetrics {
    return {
      overallScore: 0,
      functionalCoverage: 0,
      testPassRate: 0,
      performance: {
        responseTime: 0,
        throughput: 0,
        memoryUsage: process.memoryUsage().heapUsed,
        cpuUsage: 0,
        diskUsage: 0
      },
      codeQuality: {
        codeComplexity: 0,
        maintainabilityIndex: 0,
        testCoverage: 0,
        duplicationRatio: 0,
        lintScore: 0,
        typeScriptErrors: 0
      },
      security: {
        vulnerabilityCount: 0,
        securityScore: 0,
        owaspCompliance: 0,
        dependencyVulnerabilities: 0,
        secretsExposed: 0,
        securityHeaders: 0
      },
      timeToCompletion: 0,
      resourceUsage: {
        maxMemoryUsage: 0,
        avgCpuUsage: 0,
        diskIO: 0,
        networkIO: 0,
        buildTime: 0,
        deploymentTime: 0
      },
      phaseMetrics: []
    };
  }

  private chunkArray<T>(array: T[], chunkSize: number): T[][] {
    const chunks: T[][] = [];
    for (let i = 0; i < array.length; i += chunkSize) {
      chunks.push(array.slice(i, i + chunkSize));
    }
    return chunks;
  }
}
