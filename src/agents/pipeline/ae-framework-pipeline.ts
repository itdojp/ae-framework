/**
 * AE Framework Pipeline Orchestrator
 * Provides standardized pipeline execution for the 6-phase AE Framework workflow
 */

import type { 
  ProcessingContext, 
  PhaseResult, 
  PhaseType, 
  StandardAEAgent,
  IntentInput,
  IntentOutput,
  RequirementsInput,
  RequirementsOutput,
  UserStoriesInput, 
  UserStoriesOutput,
  ValidationInput,
  ValidationOutput,
  DomainModelingInput,
  DomainModelingOutput,
  UIUXInput,
  UIUXOutput,
  AgentError
} from '../interfaces/standard-interfaces.js';

/**
 * Pipeline execution configuration
 */
export interface PipelineConfig {
  projectId: string;
  domain: string;
  enableParallelProcessing?: boolean;
  validateInputs?: boolean;
  retryFailures?: boolean;
  maxRetries?: number;
  timeoutMs?: number;
}

/**
 * Pipeline execution result
 */
export interface PipelineResult {
  success: boolean;
  config: PipelineConfig;
  phases: PhaseResult[];
  totalDuration: number;
  errors: AgentError[];
  metadata: PipelineMetadata;
}

/**
 * Pipeline metadata
 */
export interface PipelineMetadata {
  startTime: Date;
  endTime: Date;
  version: string;
  agentsUsed: string[];
  dataFlowTrace: DataFlowTrace[];
}

/**
 * Data flow tracing for debugging
 */
export interface DataFlowTrace {
  phase: PhaseType;
  inputSize: number;
  outputSize: number;
  transformations: string[];
}

/**
 * AE Framework Pipeline orchestrator class
 */
export class AEFrameworkPipeline {
  private agents: Map<PhaseType, StandardAEAgent> = new Map();
  private config: PipelineConfig;

  constructor(config: PipelineConfig) {
    this.config = {
      enableParallelProcessing: false,
      validateInputs: true,
      retryFailures: true,
      maxRetries: 2,
      timeoutMs: 300000, // 5 minutes default
      ...config
    };
  }

  /**
   * Register an agent for a specific phase
   */
  registerAgent(phase: PhaseType, agent: StandardAEAgent): void {
    this.agents.set(phase, agent);
  }

  /**
   * Execute complete 6-phase AE Framework pipeline
   */
  async executePipeline(input: IntentInput): Promise<PipelineResult> {
    const startTime = new Date();
    const phases: PhaseResult[] = [];
    const errors: AgentError[] = [];
    const dataFlowTrace: DataFlowTrace[] = [];

    try {
      // Phase 1: Intent Analysis
      const intentResult = await this.executePhase('intent', input, {
        projectId: this.config.projectId,
        domain: this.config.domain,
        requestId: `${this.config.projectId}-${Date.now()}`,
        timestamp: startTime.toISOString()
      });
      phases.push(intentResult);
      this.traceDataFlow('intent', input, intentResult.data, dataFlowTrace);

      if (!intentResult.success) {
        errors.push(...(intentResult.errors || []));
        return this.buildPipelineResult(false, phases, errors, startTime, dataFlowTrace);
      }

      // Phase 2: Requirements Processing
      const addReq = input.context?.glossary?.map(g => `${g.term}: ${g.definition}`).join('\n');
      const reqInput: RequirementsInput = {
        intentAnalysis: intentResult.data as IntentOutput,
        ...(addReq ? { additionalRequirements: addReq } : {})
      };

      const reqResult = await this.executePhase('requirements', reqInput, {
        projectId: this.config.projectId,
        domain: this.config.domain,
        previousPhaseResults: [intentResult],
        requestId: `${this.config.projectId}-${Date.now()}`,
        timestamp: new Date().toISOString()
      });
      phases.push(reqResult);
      this.traceDataFlow('requirements', reqInput, reqResult.data, dataFlowTrace);

      if (!reqResult.success) {
        errors.push(...(reqResult.errors || []));
        return this.buildPipelineResult(false, phases, errors, startTime, dataFlowTrace);
      }

      // Phase 3: User Stories Generation
      const storiesInput: UserStoriesInput = {
        requirements: reqResult.data as RequirementsOutput,
        stakeholders: (intentResult.data as IntentOutput).stakeholders
      };

      const storiesResult = await this.executePhase('user-stories', storiesInput, {
        projectId: this.config.projectId,
        domain: this.config.domain,
        previousPhaseResults: [intentResult, reqResult],
        requestId: `${this.config.projectId}-${Date.now()}`,
        timestamp: new Date().toISOString()
      });
      phases.push(storiesResult);
      this.traceDataFlow('user-stories', storiesInput, storiesResult.data, dataFlowTrace);

      if (!storiesResult.success) {
        errors.push(...(storiesResult.errors || []));
        return this.buildPipelineResult(false, phases, errors, startTime, dataFlowTrace);
      }

      // Phase 4: Validation
      const validationInput: ValidationInput = {
        userStories: storiesResult.data as UserStoriesOutput,
        requirements: reqResult.data as RequirementsOutput,
        constraints: (intentResult.data as IntentOutput).constraints
      };

      const validationResult = await this.executePhase('validation', validationInput, {
        projectId: this.config.projectId,
        domain: this.config.domain,
        previousPhaseResults: [intentResult, reqResult, storiesResult],
        requestId: `${this.config.projectId}-${Date.now()}`,
        timestamp: new Date().toISOString()
      });
      phases.push(validationResult);
      this.traceDataFlow('validation', validationInput, validationResult.data, dataFlowTrace);

      if (!validationResult.success) {
        errors.push(...(validationResult.errors || []));
        return this.buildPipelineResult(false, phases, errors, startTime, dataFlowTrace);
      }

      // Phase 5: Domain Modeling
      const domainInput: DomainModelingInput = {
        validatedUserStories: validationResult.data as ValidationOutput,
        requirements: reqResult.data as RequirementsOutput,
        businessContext: (intentResult.data as IntentOutput).businessContext
      };

      const domainResult = await this.executePhase('domain-modeling', domainInput, {
        projectId: this.config.projectId,
        domain: this.config.domain,
        previousPhaseResults: [intentResult, reqResult, storiesResult, validationResult],
        requestId: `${this.config.projectId}-${Date.now()}`,
        timestamp: new Date().toISOString()
      });
      phases.push(domainResult);
      this.traceDataFlow('domain-modeling', domainInput, domainResult.data, dataFlowTrace);

      if (!domainResult.success) {
        errors.push(...(domainResult.errors || []));
        return this.buildPipelineResult(false, phases, errors, startTime, dataFlowTrace);
      }

      // Phase 6: UI/UX Generation
      const uiInput: UIUXInput = {
        domainModel: domainResult.data as DomainModelingOutput,
        userStories: storiesResult.data as UserStoriesOutput,
        stakeholders: (intentResult.data as IntentOutput).stakeholders
      };

      const uiResult = await this.executePhase('ui-ux-generation', uiInput, {
        projectId: this.config.projectId,
        domain: this.config.domain,
        previousPhaseResults: [intentResult, reqResult, storiesResult, validationResult, domainResult],
        requestId: `${this.config.projectId}-${Date.now()}`,
        timestamp: new Date().toISOString()
      });
      phases.push(uiResult);
      this.traceDataFlow('ui-ux-generation', uiInput, uiResult.data, dataFlowTrace);

      if (!uiResult.success) {
        errors.push(...(uiResult.errors || []));
        return this.buildPipelineResult(false, phases, errors, startTime, dataFlowTrace);
      }

      return this.buildPipelineResult(true, phases, errors, startTime, dataFlowTrace);

    } catch (error) {
      const agentError: AgentError = {
        code: 'PIPELINE_ERROR',
        message: error instanceof Error ? error.message : 'Unknown pipeline error',
        phase: phases.length > 0 ? (phases[phases.length - 1]?.phase || 'intent') : 'intent',
        severity: 'error',
        context: { config: this.config }
      };
      errors.push(agentError);

      return this.buildPipelineResult(false, phases, errors, startTime, dataFlowTrace);
    }
  }

  /**
   * Execute a single phase with error handling and retries
   */
  async executePhase<TInput, TOutput>(
    phase: PhaseType, 
    input: TInput, 
    context?: ProcessingContext
  ): Promise<PhaseResult<TOutput>> {
    const agent = this.agents.get(phase);
    if (!agent) {
      return {
        success: false,
        data: {} as TOutput,
        metadata: {
          phase,
          agentName: 'unknown',
          startTime: new Date(),
          endTime: new Date(),
          duration: 0,
          version: '0.0.0'
        },
        errors: [{
          code: 'AGENT_NOT_FOUND',
          message: `No agent registered for phase: ${phase}`,
          phase,
          severity: 'error'
        }],
        phase
      };
    }

    let attempt = 1;
    const maxAttempts = this.config.retryFailures ? (this.config.maxRetries || 2) + 1 : 1;

    while (attempt <= maxAttempts) {
      try {
        // Input validation if enabled
        if (this.config.validateInputs) {
          const validation = agent.validateInput(input);
          if (!validation.valid) {
            return {
              success: false,
              data: {} as TOutput,
              metadata: {
                phase,
                agentName: agent.agentName,
                startTime: new Date(),
                endTime: new Date(),
                duration: 0,
                version: agent.version
              },
              errors: validation.errors.map(error => ({
                code: 'INPUT_VALIDATION_ERROR',
                message: error,
                phase,
                severity: 'error' as const
              })),
              warnings: validation.warnings,
              phase
            };
          }
        }

        // Execute with timeout
        const result = await this.withTimeout(
          agent.process(input, context),
          this.config.timeoutMs || 300000
        );

        return result;

      } catch (error) {
        const isLastAttempt = attempt === maxAttempts;
        
        if (isLastAttempt) {
          return {
            success: false,
            data: {} as TOutput,
            metadata: {
              phase,
              agentName: agent.agentName,
              startTime: new Date(),
              endTime: new Date(),
              duration: 0,
              version: agent.version
            },
            errors: [{
              code: 'EXECUTION_ERROR',
              message: error instanceof Error ? error.message : 'Unknown execution error',
              phase,
              severity: 'error',
              ...(error instanceof Error && error.stack ? { stack: error.stack } : {})
            }],
            phase
          };
        }

        attempt++;
        await this.delay(1000 * attempt); // Progressive backoff
      }
    }

    // This should never be reached, but TypeScript requires it
    throw new Error('Unexpected execution path');
  }

  /**
   * Get pipeline status and capabilities
   */
  getPipelineCapabilities(): Record<PhaseType, any> {
    const capabilities: Record<string, any> = {};
    
    for (const [phase, agent] of this.agents.entries()) {
      capabilities[phase] = agent.getCapabilities();
    }

    return capabilities;
  }

  /**
   * Validate pipeline configuration
   */
  validatePipeline(): { valid: boolean; missing: PhaseType[]; errors: string[] } {
    const requiredPhases: PhaseType[] = [
      'intent', 'requirements', 'user-stories', 
      'validation', 'domain-modeling', 'ui-ux-generation'
    ];
    
    const missing = requiredPhases.filter(phase => !this.agents.has(phase));
    const errors: string[] = [];

    if (missing.length > 0) {
      errors.push(`Missing agents for phases: ${missing.join(', ')}`);
    }

    return {
      valid: missing.length === 0,
      missing,
      errors
    };
  }

  // Private helper methods
  private buildPipelineResult(
    success: boolean, 
    phases: PhaseResult[], 
    errors: AgentError[], 
    startTime: Date,
    dataFlowTrace: DataFlowTrace[]
  ): PipelineResult {
    const endTime = new Date();
    
    return {
      success,
      config: this.config,
      phases,
      totalDuration: endTime.getTime() - startTime.getTime(),
      errors,
      metadata: {
        startTime,
        endTime,
        version: '1.0.0',
        agentsUsed: Array.from(this.agents.values()).map(a => a.agentName),
        dataFlowTrace
      }
    };
  }

  private traceDataFlow(
    phase: PhaseType, 
    input: any, 
    output: any, 
    trace: DataFlowTrace[]
  ): void {
    trace.push({
      phase,
      inputSize: JSON.stringify(input).length,
      outputSize: JSON.stringify(output).length,
      transformations: [] // Could be enhanced to track specific transformations
    });
  }

  private async withTimeout<T>(promise: Promise<T>, timeoutMs: number): Promise<T> {
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        reject(new Error(`Operation timed out after ${timeoutMs}ms`));
      }, timeoutMs);

      promise
        .then(resolve)
        .catch(reject)
        .finally(() => clearTimeout(timer));
    });
  }

  private delay(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}
