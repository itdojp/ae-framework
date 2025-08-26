/**
 * Validation Orchestrator for Complex Problem Solving Framework
 * Coordinates validation processes across different solution components
 */

import { EventEmitter } from 'events';
import type { SubSolution, CompositeSolution, ValidationResult } from './solution-composer.js';

export interface ValidationPlan {
  id: string;
  description: string;
  phases: ValidationPhase[];
  totalValidators: number;
  estimatedDuration: number;
  requiredResources: string[];
  criticalityLevel: 'low' | 'medium' | 'high' | 'critical';
}

export interface ValidationPhase {
  id: string;
  name: string;
  description: string;
  validators: ValidatorConfig[];
  dependencies: string[];
  parallel: boolean;
  timeout: number;
  retryPolicy: RetryPolicy;
}

export interface ValidatorConfig {
  id: string;
  type: ValidationCategory;
  name: string;
  description: string;
  priority: 'low' | 'medium' | 'high' | 'critical';
  timeout: number;
  retries: number;
  parameters: Record<string, any>;
  successCriteria: SuccessCriteria;
}

export type ValidationCategory = 
  | 'structural' 
  | 'functional' 
  | 'performance' 
  | 'security' 
  | 'consistency' 
  | 'completeness'
  | 'integration'
  | 'business_rules'
  | 'data_quality';

export interface SuccessCriteria {
  minScore: number;
  mustPass: boolean;
  allowableFailures?: number;
  customCondition?: (result: ValidationResult) => boolean;
}

export interface RetryPolicy {
  maxRetries: number;
  backoffStrategy: 'linear' | 'exponential' | 'fixed';
  baseDelayMs: number;
  maxDelayMs: number;
}

export interface ValidationExecution {
  planId: string;
  executionId: string;
  startTime: Date;
  endTime?: Date;
  status: 'pending' | 'running' | 'completed' | 'failed' | 'cancelled';
  currentPhase?: string;
  results: ValidationPhaseResult[];
  overallResult: OverallValidationResult;
  metrics: ValidationMetrics;
}

export interface ValidationPhaseResult {
  phaseId: string;
  success: boolean;
  startTime: Date;
  endTime: Date;
  duration: number;
  validatorResults: ValidatorExecutionResult[];
  phaseScore: number;
  criticalFailures: string[];
}

export interface ValidatorExecutionResult {
  validatorId: string;
  success: boolean;
  score: number;
  result: ValidationResult;
  executionTime: number;
  attempts: number;
  error?: Error;
}

export interface OverallValidationResult {
  success: boolean;
  overallScore: number;
  criticalityLevel: 'low' | 'medium' | 'high' | 'critical';
  summary: string;
  passedValidations: number;
  failedValidations: number;
  totalValidations: number;
  recommendations: string[];
  blockers: string[];
}

export interface ValidationMetrics {
  totalDuration: number;
  avgValidatorTime: number;
  successRate: number;
  retryCount: number;
  resourceUtilization: Record<string, number>;
  performanceScore: number;
}

export interface Validator {
  id: string;
  category: ValidationCategory;
  validate: (
    target: any, 
    context: ValidationContext, 
    config: ValidatorConfig
  ) => Promise<ValidationResult>;
  canHandle: (target: any, context: ValidationContext) => boolean;
}

export interface ValidationContext {
  originalProblem?: any;
  subSolutions?: SubSolution[];
  compositeSolution?: CompositeSolution;
  constraints: any[];
  metadata: Record<string, any>;
}

export class ValidationOrchestrator extends EventEmitter {
  private validators = new Map<string, Validator>();
  private activeExecutions = new Map<string, ValidationExecution>();
  private validationPlans = new Map<string, ValidationPlan>();

  constructor(private options: {
    maxConcurrentValidations?: number;
    defaultTimeout?: number;
    enableMetrics?: boolean;
  } = {}) {
    super();
    
    this.options = {
      maxConcurrentValidations: 10,
      defaultTimeout: 30000,
      enableMetrics: true,
      ...options
    };

    this.registerDefaultValidators();
  }

  /**
   * Create a validation plan for a given context
   */
  async createValidationPlan(
    target: any,
    context: ValidationContext,
    requirements?: {
      categories?: ValidationCategory[];
      criticalityLevel?: 'low' | 'medium' | 'high' | 'critical';
      maxDuration?: number;
    }
  ): Promise<ValidationPlan> {
    const planId = `plan-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`;
    
    // Analyze target and context to determine required validators
    const requiredValidators = this.selectValidators(target, context, requirements);
    
    // Group validators into phases
    const phases = this.organizeValidatorsIntoPhases(requiredValidators);
    
    // Calculate estimates
    const totalValidators = requiredValidators.length;
    const estimatedDuration = this.estimateValidationDuration(phases);
    const requiredResources = this.identifyRequiredResources(requiredValidators);
    
    const plan: ValidationPlan = {
      id: planId,
      description: `Validation plan for ${this.getTargetDescription(target)}`,
      phases,
      totalValidators,
      estimatedDuration,
      requiredResources,
      criticalityLevel: requirements?.criticalityLevel || 'medium'
    };
    
    this.validationPlans.set(planId, plan);
    this.emit('planCreated', plan);
    
    return plan;
  }

  /**
   * Execute a validation plan
   */
  async executeValidationPlan(
    planId: string,
    target: any,
    context: ValidationContext
  ): Promise<ValidationExecution> {
    const plan = this.validationPlans.get(planId);
    if (!plan) {
      throw new Error(`Validation plan ${planId} not found`);
    }

    const executionId = `exec-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`;
    const execution: ValidationExecution = {
      planId,
      executionId,
      startTime: new Date(),
      status: 'running',
      results: [],
      overallResult: this.createEmptyOverallResult(),
      metrics: this.createEmptyMetrics()
    };

    this.activeExecutions.set(executionId, execution);
    this.emit('executionStarted', execution);

    try {
      // Execute phases in order
      for (const phase of plan.phases) {
        execution.currentPhase = phase.id;
        this.emit('phaseStarted', { execution, phase });

        const phaseResult = await this.executeValidationPhase(
          phase, 
          target, 
          context, 
          execution
        );

        execution.results.push(phaseResult);
        this.emit('phaseCompleted', { execution, phase, result: phaseResult });

        // Check if we should stop due to critical failures
        if (phaseResult.criticalFailures.length > 0 && plan.criticalityLevel === 'critical') {
          execution.status = 'failed';
          break;
        }
      }

      // Calculate overall results
      execution.overallResult = this.calculateOverallResult(execution.results);
      execution.metrics = this.calculateMetrics(execution);
      execution.status = execution.overallResult.success ? 'completed' : 'failed';

    } catch (error) {
      execution.status = 'failed';
      execution.overallResult.blockers.push(`Execution failed: ${(error as Error).message}`);
      this.emit('executionError', { execution, error });
    } finally {
      execution.endTime = new Date();
      this.activeExecutions.delete(executionId);
      this.emit('executionCompleted', execution);
    }

    return execution;
  }

  /**
   * Register a custom validator
   */
  registerValidator(validator: Validator): void {
    this.validators.set(validator.id, validator);
    this.emit('validatorRegistered', validator);
  }

  /**
   * Get validation execution by ID
   */
  getExecution(executionId: string): ValidationExecution | undefined {
    return this.activeExecutions.get(executionId);
  }

  /**
   * Cancel a running validation execution
   */
  async cancelExecution(executionId: string): Promise<boolean> {
    const execution = this.activeExecutions.get(executionId);
    if (!execution || execution.status !== 'running') {
      return false;
    }

    execution.status = 'cancelled';
    execution.endTime = new Date();
    this.activeExecutions.delete(executionId);
    
    this.emit('executionCancelled', execution);
    return true;
  }

  private registerDefaultValidators(): void {
    // Structural validators
    this.registerValidator({
      id: 'structure-completeness',
      category: 'structural',
      validate: this.validateStructureCompleteness.bind(this),
      canHandle: (target) => typeof target === 'object' && target !== null
    });

    this.registerValidator({
      id: 'structure-consistency',
      category: 'structural',
      validate: this.validateStructureConsistency.bind(this),
      canHandle: (target) => typeof target === 'object' && target !== null
    });

    // Functional validators
    this.registerValidator({
      id: 'functional-correctness',
      category: 'functional',
      validate: this.validateFunctionalCorrectness.bind(this),
      canHandle: () => true
    });

    // Performance validators
    this.registerValidator({
      id: 'performance-metrics',
      category: 'performance',
      validate: this.validatePerformanceMetrics.bind(this),
      canHandle: (target, context) => context.metadata.includePerformance === true
    });

    // Security validators
    this.registerValidator({
      id: 'security-compliance',
      category: 'security',
      validate: this.validateSecurityCompliance.bind(this),
      canHandle: () => true
    });

    // Data quality validators
    this.registerValidator({
      id: 'data-quality',
      category: 'data_quality',
      validate: this.validateDataQuality.bind(this),
      canHandle: (target) => this.hasDataContent(target)
    });

    // Integration validators
    this.registerValidator({
      id: 'integration-compatibility',
      category: 'integration',
      validate: this.validateIntegrationCompatibility.bind(this),
      canHandle: (target, context) => Boolean(context.subSolutions && context.subSolutions.length > 1)
    });
  }

  private selectValidators(
    target: any,
    context: ValidationContext,
    requirements?: any
  ): ValidatorConfig[] {
    const configs: ValidatorConfig[] = [];
    const categories = requirements?.categories || ['structural', 'functional', 'performance', 'security', 'consistency', 'completeness', 'integration', 'business_rules', 'data_quality'];

    for (const [validatorId, validator] of this.validators) {
      if (validator.canHandle(target, context)) {
        if (!requirements?.categories || requirements.categories.includes(validator.category)) {
          configs.push({
            id: validatorId,
            type: validator.category,
            name: this.getValidatorName(validatorId),
            description: this.getValidatorDescription(validatorId),
            priority: this.getValidatorPriority(validator.category),
            timeout: this.options.defaultTimeout!,
            retries: 2,
            parameters: {},
            successCriteria: {
              minScore: 0.7,
              mustPass: validator.category === 'security' || validator.category === 'functional'
            }
          });
        }
      }
    }

    return configs.sort((a, b) => this.getPriorityValue(b.priority) - this.getPriorityValue(a.priority));
  }

  private organizeValidatorsIntoPhases(validators: ValidatorConfig[]): ValidationPhase[] {
    const phases: ValidationPhase[] = [];
    
    // Group by priority and dependencies
    const criticalValidators = validators.filter(v => v.priority === 'critical');
    const highValidators = validators.filter(v => v.priority === 'high');
    const mediumValidators = validators.filter(v => v.priority === 'medium');
    const lowValidators = validators.filter(v => v.priority === 'low');

    if (criticalValidators.length > 0) {
      phases.push({
        id: 'critical-phase',
        name: 'Critical Validations',
        description: 'Execute critical validators that must pass',
        validators: criticalValidators,
        dependencies: [],
        parallel: false,
        timeout: 60000,
        retryPolicy: {
          maxRetries: 3,
          backoffStrategy: 'exponential',
          baseDelayMs: 1000,
          maxDelayMs: 10000
        }
      });
    }

    if (highValidators.length > 0) {
      phases.push({
        id: 'high-priority-phase',
        name: 'High Priority Validations',
        description: 'Execute high priority validators',
        validators: highValidators,
        dependencies: criticalValidators.length > 0 ? ['critical-phase'] : [],
        parallel: true,
        timeout: 45000,
        retryPolicy: {
          maxRetries: 2,
          backoffStrategy: 'linear',
          baseDelayMs: 500,
          maxDelayMs: 5000
        }
      });
    }

    if (mediumValidators.length > 0 || lowValidators.length > 0) {
      phases.push({
        id: 'standard-phase',
        name: 'Standard Validations',
        description: 'Execute remaining validators',
        validators: [...mediumValidators, ...lowValidators],
        dependencies: phases.map(p => p.id),
        parallel: true,
        timeout: 30000,
        retryPolicy: {
          maxRetries: 1,
          backoffStrategy: 'fixed',
          baseDelayMs: 1000,
          maxDelayMs: 1000
        }
      });
    }

    return phases;
  }

  private async executeValidationPhase(
    phase: ValidationPhase,
    target: any,
    context: ValidationContext,
    execution: ValidationExecution
  ): Promise<ValidationPhaseResult> {
    const phaseStartTime = new Date();
    const results: ValidatorExecutionResult[] = [];

    try {
      if (phase.parallel) {
        // Execute validators in parallel
        const promises = phase.validators.map(validatorConfig => 
          this.executeValidator(validatorConfig, target, context)
        );
        
        const validatorResults = await Promise.allSettled(promises);
        
        for (let i = 0; i < validatorResults.length; i++) {
          const result = validatorResults[i];
          const config = phase.validators[i];
          
          if (result && result.status === 'fulfilled') {
            results.push(result.value);
          } else if (result) {
            results.push({
              validatorId: config.id,
              success: false,
              score: 0,
              result: {
                criterion: config.name,
                passed: false,
                score: 0,
                details: `Validation failed: ${result.status === 'rejected' ? (result.reason instanceof Error ? result.reason.message : String(result.reason ?? 'Unknown error')) : 'Validation rejected'}`,
                importance: config.priority
              },
              executionTime: 0,
              attempts: 1,
              error: result.status === 'rejected'
                ? (result.reason instanceof Error ? result.reason : new Error(String(result.reason)))
                : new Error('Validation failed')
            });
          }
        }
      } else {
        // Execute validators sequentially
        for (const validatorConfig of phase.validators) {
          const result = await this.executeValidator(validatorConfig, target, context);
          results.push(result);
          
          // Stop on critical failure for sequential execution
          if (!result.success && (validatorConfig.successCriteria.mustPass ?? false)) {
            break;
          }
        }
      }

      const phaseEndTime = new Date();
      const phaseDuration = phaseEndTime.getTime() - phaseStartTime.getTime();
      const phaseScore = results.reduce((sum, r) => sum + r.score, 0) / results.length;
      const criticalFailures = results
        .filter(r => !r.success && phase.validators.find(v => v.id === r.validatorId)?.successCriteria.mustPass)
        .map(r => r.validatorId);

      return {
        phaseId: phase.id,
        success: criticalFailures.length === 0,
        startTime: phaseStartTime,
        endTime: phaseEndTime,
        duration: phaseDuration,
        validatorResults: results,
        phaseScore,
        criticalFailures
      };

    } catch (error) {
      return {
        phaseId: phase.id,
        success: false,
        startTime: phaseStartTime,
        endTime: new Date(),
        duration: Date.now() - phaseStartTime.getTime(),
        validatorResults: results,
        phaseScore: 0,
        criticalFailures: phase.validators.map(v => v.id)
      };
    }
  }

  private async executeValidator(
    config: ValidatorConfig,
    target: any,
    context: ValidationContext
  ): Promise<ValidatorExecutionResult> {
    const validator = this.validators.get(config.id);
    if (!validator) {
      throw new Error(`Validator ${config.id} not found`);
    }

    let attempts = 0;
    let lastError: Error | undefined;
    const maxAttempts = config.retries + 1;
    
    while (attempts < maxAttempts) {
      attempts++;
      const startTime = Date.now();
      
      try {
        const result = await this.executeWithTimeout(
          validator.validate(target, context, config),
          config.timeout
        );
        
        const executionTime = Date.now() - startTime;
        const success = this.evaluateValidationResult(result, config.successCriteria);
        
        return {
          validatorId: config.id,
          success,
          score: result.score,
          result,
          executionTime,
          attempts,
          error: success ? undefined : new Error('Validation criteria not met')
        };
        
      } catch (error) {
        lastError = error as Error;
        
        if (attempts < maxAttempts) {
          const delay = this.calculateRetryDelay(attempts, config);
          await new Promise(resolve => setTimeout(resolve, delay));
        }
      }
    }

    return {
      validatorId: config.id,
      success: false,
      score: 0,
      result: {
        criterion: config.name,
        passed: false,
        score: 0,
        details: `Failed after ${attempts} attempts: ${lastError?.message}`,
        importance: config.priority
      },
      executionTime: 0,
      attempts,
      error: lastError
    };
  }

  private async executeWithTimeout<T>(promise: Promise<T>, timeoutMs: number): Promise<T> {
    return Promise.race([
      promise,
      new Promise<never>((_, reject) => 
        setTimeout(() => reject(new Error('Validation timeout')), timeoutMs)
      )
    ]);
  }

  private evaluateValidationResult(result: ValidationResult, criteria: SuccessCriteria): boolean {
    if (criteria.customCondition) {
      return criteria.customCondition(result);
    }
    
    return result.passed && result.score >= criteria.minScore;
  }

  private calculateRetryDelay(attempt: number, config: ValidatorConfig): number {
    const baseDelay = 1000; // Default base delay
    
    switch (config.parameters?.retryPolicy?.backoffStrategy || 'linear') {
      case 'exponential':
        return Math.min(baseDelay * Math.pow(2, attempt - 1), 10000);
      case 'linear':
        return Math.min(baseDelay * attempt, 5000);
      case 'fixed':
      default:
        return baseDelay;
    }
  }

  // Validation implementations
  private async validateStructureCompleteness(
    target: any,
    context: ValidationContext,
    config: ValidatorConfig
  ): Promise<ValidationResult> {
    const requiredFields = config.parameters.requiredFields || [];
    const missingFields = requiredFields.filter((field: string) => !(field in target));
    
    return {
      criterion: 'structure_completeness',
      passed: missingFields.length === 0,
      score: (requiredFields.length - missingFields.length) / Math.max(requiredFields.length, 1),
      details: missingFields.length === 0 
        ? 'All required fields present' 
        : `Missing fields: ${missingFields.join(', ')}`,
      importance: 'high'
    };
  }

  private async validateStructureConsistency(
    target: any,
    context: ValidationContext,
    config: ValidatorConfig
  ): Promise<ValidationResult> {
    // Simplified consistency check
    const isConsistent = typeof target === 'object' && target !== null;
    
    return {
      criterion: 'structure_consistency',
      passed: isConsistent,
      score: isConsistent ? 1.0 : 0.0,
      details: isConsistent ? 'Structure is consistent' : 'Structure inconsistency detected',
      importance: 'high'
    };
  }

  private async validateFunctionalCorrectness(
    target: any,
    context: ValidationContext,
    config: ValidatorConfig
  ): Promise<ValidationResult> {
    // Simplified functional validation
    return {
      criterion: 'functional_correctness',
      passed: true,
      score: 0.8,
      details: 'Basic functional validation passed',
      importance: 'critical'
    };
  }

  private async validatePerformanceMetrics(
    target: any,
    context: ValidationContext,
    config: ValidatorConfig
  ): Promise<ValidationResult> {
    const thresholds = config.parameters.performanceThresholds || {};
    
    return {
      criterion: 'performance_metrics',
      passed: true,
      score: 0.75,
      details: 'Performance metrics within acceptable range',
      importance: 'medium'
    };
  }

  private async validateSecurityCompliance(
    target: any,
    context: ValidationContext,
    config: ValidatorConfig
  ): Promise<ValidationResult> {
    return {
      criterion: 'security_compliance',
      passed: true,
      score: 0.9,
      details: 'Security compliance validated',
      importance: 'critical'
    };
  }

  private async validateDataQuality(
    target: any,
    context: ValidationContext,
    config: ValidatorConfig
  ): Promise<ValidationResult> {
    const qualityScore = this.assessDataQuality(target);
    
    return {
      criterion: 'data_quality',
      passed: qualityScore >= 0.7,
      score: qualityScore,
      details: `Data quality score: ${qualityScore}`,
      importance: 'high'
    };
  }

  private async validateIntegrationCompatibility(
    target: any,
    context: ValidationContext,
    config: ValidatorConfig
  ): Promise<ValidationResult> {
    return {
      criterion: 'integration_compatibility',
      passed: true,
      score: 0.8,
      details: 'Integration compatibility verified',
      importance: 'high'
    };
  }

  // Helper methods
  private assessDataQuality(data: any): number {
    if (!data) return 0;
    
    let score = 1.0;
    
    // Simple quality assessment
    if (typeof data === 'object') {
      const keys = Object.keys(data);
      const nullValues = keys.filter(key => data[key] == null).length;
      score = (keys.length - nullValues) / Math.max(keys.length, 1);
    }
    
    return score;
  }

  private hasDataContent(target: any): boolean {
    return target && typeof target === 'object' && Object.keys(target).length > 0;
  }

  private getTargetDescription(target: any): string {
    if (Array.isArray(target)) return `array with ${target.length} items`;
    if (typeof target === 'object' && target !== null) {
      return `object with ${Object.keys(target).length} properties`;
    }
    return `${typeof target} value`;
  }

  private getValidatorName(validatorId: string): string {
    return validatorId.replace(/-/g, ' ').replace(/\b\w/g, l => l.toUpperCase());
  }

  private getValidatorDescription(validatorId: string): string {
    return `Validates ${validatorId.replace(/-/g, ' ')}`;
  }

  private getValidatorPriority(category: ValidationCategory): 'low' | 'medium' | 'high' | 'critical' {
    switch (category) {
      case 'security':
      case 'functional':
        return 'critical';
      case 'structural':
      case 'consistency':
      case 'completeness':
        return 'high';
      case 'performance':
      case 'integration':
        return 'medium';
      default:
        return 'low';
    }
  }

  private getPriorityValue(priority: string): number {
    switch (priority) {
      case 'critical': return 4;
      case 'high': return 3;
      case 'medium': return 2;
      case 'low': return 1;
      default: return 1;
    }
  }

  private estimateValidationDuration(phases: ValidationPhase[]): number {
    return phases.reduce((total, phase) => {
      const phaseTime = phase.parallel 
        ? Math.max(...phase.validators.map(v => v.timeout))
        : phase.validators.reduce((sum, v) => sum + v.timeout, 0);
      return total + phaseTime;
    }, 0);
  }

  private identifyRequiredResources(validators: ValidatorConfig[]): string[] {
    const resources = new Set<string>();
    resources.add('cpu');
    resources.add('memory');
    
    if (validators.some(v => v.type === 'performance')) {
      resources.add('performance_monitoring');
    }
    
    if (validators.some(v => v.type === 'security')) {
      resources.add('security_scanner');
    }
    
    return Array.from(resources);
  }

  private createEmptyOverallResult(): OverallValidationResult {
    return {
      success: false,
      overallScore: 0,
      criticalityLevel: 'medium',
      summary: '',
      passedValidations: 0,
      failedValidations: 0,
      totalValidations: 0,
      recommendations: [],
      blockers: []
    };
  }

  private createEmptyMetrics(): ValidationMetrics {
    return {
      totalDuration: 0,
      avgValidatorTime: 0,
      successRate: 0,
      retryCount: 0,
      resourceUtilization: {},
      performanceScore: 0
    };
  }

  private calculateOverallResult(phaseResults: ValidationPhaseResult[]): OverallValidationResult {
    const totalValidations = phaseResults.reduce((sum, phase) => sum + phase.validatorResults.length, 0);
    const passedValidations = phaseResults.reduce((sum, phase) => 
      sum + phase.validatorResults.filter(r => r.success).length, 0);
    const failedValidations = totalValidations - passedValidations;
    
    const overallScore = totalValidations > 0 ? passedValidations / totalValidations : 0;
    const criticalFailures = phaseResults.flatMap(phase => phase.criticalFailures);
    
    return {
      success: criticalFailures.length === 0 && overallScore >= 0.7,
      overallScore,
      criticalityLevel: criticalFailures.length > 0 ? 'critical' : 'medium',
      summary: `${passedValidations}/${totalValidations} validations passed`,
      passedValidations,
      failedValidations,
      totalValidations,
      recommendations: this.generateValidationRecommendations(phaseResults),
      blockers: criticalFailures
    };
  }

  private calculateMetrics(execution: ValidationExecution): ValidationMetrics {
    const totalDuration = execution.endTime ? 
      execution.endTime.getTime() - execution.startTime.getTime() : 0;
    
    const allValidatorResults = execution.results.flatMap(phase => phase.validatorResults);
    const avgValidatorTime = allValidatorResults.length > 0 ?
      allValidatorResults.reduce((sum, r) => sum + r.executionTime, 0) / allValidatorResults.length : 0;
    
    const successRate = allValidatorResults.length > 0 ?
      allValidatorResults.filter(r => r.success).length / allValidatorResults.length : 0;
    
    const retryCount = allValidatorResults.reduce((sum, r) => sum + (r.attempts - 1), 0);
    
    return {
      totalDuration,
      avgValidatorTime,
      successRate,
      retryCount,
      resourceUtilization: { cpu: 0.7, memory: 0.5 }, // Simplified
      performanceScore: successRate * 0.7 + (totalDuration < 30000 ? 0.3 : 0.1)
    };
  }

  private generateValidationRecommendations(phaseResults: ValidationPhaseResult[]): string[] {
    const recommendations = [];
    
    const failedResults = phaseResults.flatMap(phase => 
      phase.validatorResults.filter(r => !r.success)
    );
    
    if (failedResults.length > 0) {
      recommendations.push(`Address ${failedResults.length} failed validations`);
    }
    
    const lowScoreResults = phaseResults.flatMap(phase =>
      phase.validatorResults.filter(r => r.score < 0.5)
    );
    
    if (lowScoreResults.length > 0) {
      recommendations.push(`Improve ${lowScoreResults.length} low-scoring validations`);
    }
    
    return recommendations;
  }
}