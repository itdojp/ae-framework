/**
 * Req2Run Benchmark Runner
 * Orchestrates the execution of AE Framework against Req2Run benchmark problems
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

import { IntentAgent } from '../../../agents/intent-agent.js';
import { NaturalLanguageTaskAdapter } from '../../../agents/natural-language-task-adapter.js';
import { UserStoriesTaskAdapter } from '../../../agents/user-stories-task-adapter.js';
import { ValidationTaskAdapter } from '../../../agents/validation-task-adapter.js';
import { DomainModelingTaskAdapter } from '../../../agents/domain-modeling-task-adapter.js';
// Note: UI generation agent will be integrated when available

export class BenchmarkRunner {
  private config: BenchmarkConfig;
  private intentAgent: IntentAgent;
  private nlpAgent: NaturalLanguageTaskAdapter;
  private storiesAgent: UserStoriesTaskAdapter;
  private validationAgent: ValidationTaskAdapter;
  private domainAgent: DomainModelingTaskAdapter;

  constructor(config: BenchmarkConfig) {
    this.config = config;
    this.initializeAgents();
  }

  /**
   * Run a single benchmark problem
   */
  async runBenchmark(problemId: string): Promise<BenchmarkResult> {
    const startTime = new Date();
    const phaseExecutions: PhaseExecution[] = [];
    const errors: BenchmarkError[] = [];
    let generatedArtifacts: GeneratedArtifacts = this.initializeArtifacts();

    try {
      // Load problem specification
      const spec = await this.loadProblemSpec(problemId);
      
      // Execute AE Framework 6-phase pipeline
      const intent = await this.executePhase(
        AEFrameworkPhase.INTENT_ANALYSIS,
        () => this.intentAgent.analyze(spec),
        phaseExecutions,
        errors
      );

      const requirements = await this.executePhase(
        AEFrameworkPhase.REQUIREMENTS,
        () => this.nlpAgent.process(intent),
        phaseExecutions,
        errors
      );

      const userStories = await this.executePhase(
        AEFrameworkPhase.USER_STORIES,
        () => this.storiesAgent.generate(requirements),
        phaseExecutions,
        errors
      );

      const validation = await this.executePhase(
        AEFrameworkPhase.VALIDATION,
        () => this.validationAgent.verify(userStories),
        phaseExecutions,
        errors
      );

      const domainModel = await this.executePhase(
        AEFrameworkPhase.DOMAIN_MODELING,
        () => this.domainAgent.model(validation),
        phaseExecutions,
        errors
      );

      // TODO: Implement UI/UX generation phase
      const application = await this.executePhase(
        AEFrameworkPhase.UI_UX_GENERATION,
        () => this.generateUIUX(domainModel),
        phaseExecutions,
        errors
      );

      // Collect generated artifacts
      generatedArtifacts = await this.collectArtifacts(application);

      // Evaluate the result
      const metrics = await this.evaluateResult(application, spec, phaseExecutions);

      const endTime = new Date();
      const executionDetails: ExecutionDetails = {
        startTime,
        endTime,
        totalDuration: endTime.getTime() - startTime.getTime(),
        phaseExecutions,
        environment: await this.getExecutionEnvironment(),
        logs: [] // TODO: Implement logging
      };

      return {
        problemId,
        timestamp: endTime,
        success: errors.length === 0,
        metrics,
        executionDetails,
        generatedArtifacts,
        errors: errors.length > 0 ? errors : undefined
      };

    } catch (error) {
      const benchmarkError: BenchmarkError = {
        phase: AEFrameworkPhase.INTENT_ANALYSIS, // Default phase
        type: 'runtime',
        message: error instanceof Error ? error.message : 'Unknown error',
        stack: error instanceof Error ? error.stack : undefined,
        timestamp: new Date()
      };
      errors.push(benchmarkError);

      const endTime = new Date();
      return {
        problemId,
        timestamp: endTime,
        success: false,
        metrics: this.getDefaultMetrics(),
        executionDetails: {
          startTime,
          endTime,
          totalDuration: endTime.getTime() - startTime.getTime(),
          phaseExecutions,
          environment: await this.getExecutionEnvironment(),
          logs: []
        },
        generatedArtifacts,
        errors
      };
    }
  }

  /**
   * Run multiple benchmark problems
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

    return results;
  }

  /**
   * Execute a single phase with error handling and metrics collection
   */
  private async executePhase<T>(
    phase: AEFrameworkPhase,
    executor: () => Promise<T>,
    phaseExecutions: PhaseExecution[],
    errors: BenchmarkError[]
  ): Promise<T> {
    const startTime = new Date();
    
    try {
      const input = this.getPhaseInput(phase, phaseExecutions);
      const output = await executor();
      const endTime = new Date();

      phaseExecutions.push({
        phase,
        startTime,
        endTime,
        duration: endTime.getTime() - startTime.getTime(),
        input,
        output,
        success: true
      });

      return output;
    } catch (error) {
      const endTime = new Date();
      const errorMessage = error instanceof Error ? error.message : 'Unknown error';

      phaseExecutions.push({
        phase,
        startTime,
        endTime,
        duration: endTime.getTime() - startTime.getTime(),
        input: null,
        output: null,
        success: false,
        errors: [errorMessage]
      });

      const benchmarkError: BenchmarkError = {
        phase,
        type: 'runtime',
        message: errorMessage,
        stack: error instanceof Error ? error.stack : undefined,
        timestamp: new Date()
      };
      errors.push(benchmarkError);

      throw error;
    }
  }

  /**
   * Initialize AE Framework agents
   */
  private initializeAgents(): void {
    this.intentAgent = new IntentAgent();
    this.nlpAgent = new NaturalLanguageTaskAdapter();
    this.storiesAgent = new UserStoriesTaskAdapter();
    this.validationAgent = new ValidationTaskAdapter();
    this.domainAgent = new DomainModelingTaskAdapter();
  }

  /**
   * Load problem specification from Req2Run repository
   */
  private async loadProblemSpec(problemId: string): Promise<RequirementSpec> {
    // TODO: Implement problem specification loading
    // This would typically fetch from the req2run-benchmark repository
    throw new Error(`Problem specification loading not implemented for ${problemId}`);
  }

  /**
   * Placeholder for UI/UX generation phase
   */
  private async generateUIUX(domainModel: any): Promise<any> {
    // TODO: Implement UI/UX generation when the agent is available
    console.warn('UI/UX generation phase not yet implemented');
    return domainModel; // Return domain model as placeholder
  }

  /**
   * Evaluate the generated application against the problem specification
   */
  private async evaluateResult(
    application: any,
    spec: RequirementSpec,
    phaseExecutions: PhaseExecution[]
  ): Promise<BenchmarkMetrics> {
    // TODO: Implement comprehensive evaluation logic
    // This would include:
    // - Functional testing
    // - Performance testing
    // - Security analysis
    // - Code quality analysis
    
    return this.getDefaultMetrics();
  }

  /**
   * Collect generated artifacts from the application
   */
  private async collectArtifacts(application: any): Promise<GeneratedArtifacts> {
    // TODO: Implement artifact collection
    return this.initializeArtifacts();
  }

  /**
   * Get execution environment information
   */
  private async getExecutionEnvironment() {
    return {
      nodeVersion: process.version,
      platform: process.platform,
      arch: process.arch,
      memory: process.memoryUsage().heapTotal,
      cpuCount: require('os').cpus().length
    };
  }

  /**
   * Get input for a specific phase
   */
  private getPhaseInput(phase: AEFrameworkPhase, phaseExecutions: PhaseExecution[]): any {
    if (phaseExecutions.length === 0) return null;
    const lastExecution = phaseExecutions[phaseExecutions.length - 1];
    return lastExecution.output;
  }

  /**
   * Initialize empty artifacts structure
   */
  private initializeArtifacts(): GeneratedArtifacts {
    return {
      sourceCode: [],
      documentation: [],
      tests: [],
      configuration: [],
      deployment: []
    };
  }

  /**
   * Get default metrics for failed executions
   */
  private getDefaultMetrics(): BenchmarkMetrics {
    return {
      overallScore: 0,
      functionalCoverage: 0,
      testPassRate: 0,
      performance: {
        responseTime: 0,
        throughput: 0,
        memoryUsage: 0,
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

  /**
   * Split array into chunks of specified size
   */
  private chunkArray<T>(array: T[], chunkSize: number): T[][] {
    const chunks: T[][] = [];
    for (let i = 0; i < array.length; i += chunkSize) {
      chunks.push(array.slice(i, i + chunkSize));
    }
    return chunks;
  }
}