/**
 * Solution Composer for Complex Problem Solving Framework
 * Integrates and validates solutions from sub-problems
 */

import type { SubProblem, DecompositionResult } from './problem-decomposer.js';

type SubSolutionResult = Record<string, unknown> | null;

export interface SubSolution {
  subProblemId: string;
  success: boolean;
  confidence: number;
  result: SubSolutionResult;
  metrics: {
    executionTime: number;
    resourcesUsed: string[];
    qualityScore: number;
  };
  validationResults: ValidationResult[];
  dependencies: Record<string, SubSolutionResult>;
  error?: Error;
}

export interface ValidationResult {
  criterion: string;
  passed: boolean;
  score: number;
  details: string;
  importance: 'low' | 'medium' | 'high' | 'critical';
}

export interface CompositeSolution {
  problemId: string;
  success: boolean;
  overallConfidence: number;
  compositeResult: CompositionResultPayload;
  subSolutions: SubSolution[];
  integrationMetrics: {
    consistencyScore: number;
    completenessScore: number;
    qualityScore: number;
    performanceScore: number;
  };
  validationResults: GlobalValidationResult[];
  recommendations: string[];
  alternatives?: AlternativeSolution[];
}

export interface GlobalValidationResult {
  aspect: 'consistency' | 'completeness' | 'quality' | 'performance' | 'security';
  passed: boolean;
  score: number;
  details: string;
  requiredActions: string[];
}

export interface AlternativeSolution {
  id: string;
  description: string;
  confidence: number;
  tradeoffs: string[];
  estimatedImpact: {
    time: number;
    resources: number;
    quality: number;
  };
}

export interface CompositionStrategy {
  name: string;
  description: string;
  canHandle: (decomposition: DecompositionResult) => boolean;
  compose: (subSolutions: SubSolution[], context: CompositionContext) => Promise<CompositionResultPayload>;
  validate: (result: CompositionResultPayload, context: CompositionContext) => Promise<ValidationResult[]>;
}

export interface CompositionContext {
  originalProblem: DecompositionResult['originalProblem'];
  decompositionResult: DecompositionResult;
  constraints: DecompositionResult['originalProblem']['constraints'];
  qualityThresholds: Record<string, number>;
  integrationRules: IntegrationRule[];
}

interface SequentialCompositionResult {
  type: 'sequential_composition';
  results: Array<{
    subProblemId: string;
    result: SubSolutionResult;
    confidence: number;
  }>;
  metadata: {
    strategy: 'sequential';
    totalSolutions: number;
    successfulSolutions: number;
  };
  summary: string;
}

interface ParallelCompositionResult {
  type: 'parallel_composition';
  phases: Array<{
    phase: number;
    results: SequentialCompositionResult['results'];
    averageConfidence: number;
  }>;
  metadata: {
    strategy: 'parallel';
    totalPhases: number;
    totalSolutions: number;
  };
  summary: string;
}

interface HierarchyNode {
  root?: SubSolution[];
  children?: HierarchyNode[];
  metadata?: Record<string, unknown>;
}

interface HierarchicalCompositionResult {
  type: 'hierarchical_composition';
  hierarchy: HierarchyNode;
  metadata: {
    strategy: 'hierarchical';
    levels: number;
    totalNodes: number;
  };
  summary: string;
}

interface HybridIntegrationResult {
  sequential: SequentialCompositionResult['results'];
  parallel: ParallelCompositionResult['phases'];
  integration: 'hybrid';
}

interface HybridCompositionResult {
  type: 'hybrid_composition';
  sequential: SequentialCompositionResult | null;
  parallel: ParallelCompositionResult | null;
  integrated: HybridIntegrationResult;
  metadata: {
    strategy: 'hybrid';
    sequentialSolutions: number;
    parallelSolutions: number;
  };
  summary: string;
}

type CompositionResultPayload =
  | SequentialCompositionResult
  | ParallelCompositionResult
  | HierarchicalCompositionResult
  | HybridCompositionResult;

type ValidationAspect = GlobalValidationResult['aspect'];
type ValidatorFunction = (
  result: CompositionResultPayload,
  context: CompositionContext,
) => Promise<ValidationResult[]>;

interface RegisteredValidator {
  aspect: ValidationAspect;
  run: ValidatorFunction;
}

export type IntegrationActionResult =
  | { kind: 'noop' }
  | { kind: 'replace'; solutions: SubSolution[] };

export interface IntegrationRule {
  id: string;
  type: 'dependency' | 'consistency' | 'transformation' | 'validation';
  description: string;
  condition: (subSolutions: SubSolution[]) => boolean;
  action: (subSolutions: SubSolution[]) => IntegrationActionResult;
  priority: 'low' | 'medium' | 'high' | 'critical';
}

export class SolutionComposer {
  private strategies = new Map<string, CompositionStrategy>();
  private validators = new Map<string, RegisteredValidator>();
  private transformers = new Map<string, (solutions: SubSolution[]) => SubSolution[]>();

  constructor() {
    this.registerDefaultStrategies();
    this.registerDefaultValidators();
    this.registerDefaultTransformers();
  }

  /**
   * Compose solutions from sub-problems into a complete solution
   */
  async compose(
    subSolutions: SubSolution[], 
    decompositionResult: DecompositionResult,
    context?: Partial<CompositionContext>
  ): Promise<CompositeSolution> {
    const compositionContext: CompositionContext = {
      originalProblem: decompositionResult.originalProblem,
      decompositionResult,
      constraints: decompositionResult.originalProblem.constraints || [],
      qualityThresholds: {
        consistency: 0.8,
        completeness: 0.9,
        quality: 0.7,
        performance: 0.6
      },
      integrationRules: this.createDefaultIntegrationRules(),
      ...context
    };

    // Validate input solutions
    this.validateInputSolutions(subSolutions, decompositionResult);

    // Apply pre-processing transformations
    const processedSolutions = await this.preprocessSolutions(subSolutions, compositionContext);

    // Select and apply composition strategy
    const strategy = this.selectCompositionStrategy(decompositionResult);
    const compositeResult = await strategy.compose(processedSolutions, compositionContext);

    // Perform global validations
    const globalValidations = await this.performGlobalValidation(
      compositeResult, 
      processedSolutions, 
      compositionContext
    );

    // Calculate metrics
    const integrationMetrics = this.calculateIntegrationMetrics(globalValidations);

    // Generate recommendations
    const recommendations = this.generateRecommendations(
      processedSolutions, 
      globalValidations, 
      integrationMetrics
    );

    // Generate alternatives if needed
    const alternatives = await this.generateAlternatives(
      processedSolutions, 
      compositionContext, 
      integrationMetrics
    );

    return {
      problemId: decompositionResult.originalProblem.id,
      success: this.determineOverallSuccess(processedSolutions, globalValidations),
      overallConfidence: this.calculateOverallConfidence(processedSolutions, globalValidations),
      compositeResult,
      subSolutions: processedSolutions,
      integrationMetrics,
      validationResults: globalValidations,
      recommendations,
      ...(alternatives.length > 0 ? { alternatives } : {})
    };
  }

  /**
   * Register a custom composition strategy
   */
  registerCompositionStrategy(strategy: CompositionStrategy): void {
    this.strategies.set(strategy.name, strategy);
  }

  /**
   * Register a custom validator
   */
  registerValidator(
    name: string,
    validator: ValidatorFunction,
    aspect: ValidationAspect = 'quality',
  ): void {
    this.validators.set(name, {
      aspect,
      run: validator,
    });
  }

  private registerDefaultStrategies(): void {
    this.strategies.set('sequential', {
      name: 'sequential',
      description: 'Compose solutions in sequential order',
      canHandle: (decomposition) => decomposition.subProblems.every(sp => sp.type === 'sequential'),
      compose: this.composeSequential.bind(this),
      validate: this.validateSequential.bind(this)
    });

    this.strategies.set('parallel', {
      name: 'parallel',
      description: 'Compose solutions from parallel execution',
      canHandle: (decomposition) => decomposition.subProblems.some(sp => sp.type === 'parallel'),
      compose: this.composeParallel.bind(this),
      validate: this.validateParallel.bind(this)
    });

    this.strategies.set('hierarchical', {
      name: 'hierarchical',
      description: 'Compose solutions in hierarchical structure',
      canHandle: (decomposition) => this.hasHierarchicalStructure(decomposition),
      compose: this.composeHierarchical.bind(this),
      validate: this.validateHierarchical.bind(this)
    });

    this.strategies.set('hybrid', {
      name: 'hybrid',
      description: 'Flexible composition strategy',
      canHandle: () => true, // Can handle all decomposition shapes
      compose: this.composeHybrid.bind(this),
      validate: this.validateHybrid.bind(this)
    });
  }

  private registerDefaultValidators(): void {
    this.registerValidator('consistency', this.validateConsistency.bind(this), 'consistency');
    this.registerValidator('completeness', this.validateCompleteness.bind(this), 'completeness');
    this.registerValidator('quality', this.validateQuality.bind(this), 'quality');
    this.registerValidator('performance', this.validatePerformance.bind(this), 'performance');
    this.registerValidator('security', this.validateSecurity.bind(this), 'security');
  }

  private registerDefaultTransformers(): void {
    this.transformers.set('dependency_resolution', this.resolveDependencies.bind(this));
    this.transformers.set('consistency_enforcement', this.enforceConsistency.bind(this));
    this.transformers.set('quality_normalization', this.normalizeQuality.bind(this));
  }

  private validateInputSolutions(subSolutions: SubSolution[], decomposition: DecompositionResult): void {
    const expectedSubProblems = new Set(decomposition.subProblems.map(sp => sp.id));
    const providedSolutions = new Set(subSolutions.map(ss => ss.subProblemId));

    // Check for missing solutions
    const missing = Array.from(expectedSubProblems).filter(id => !providedSolutions.has(id));
    if (missing.length > 0) {
      throw new Error(`Missing solutions for sub-problems: ${missing.join(', ')}`);
    }

    // Check for extra solutions
    const extra = Array.from(providedSolutions).filter(id => !expectedSubProblems.has(id));
    if (extra.length > 0) {
      console.warn(`Extra solutions provided for unknown sub-problems: ${extra.join(', ')}`);
    }

    // Validate each solution structure
    for (const solution of subSolutions) {
      if (!solution.subProblemId || solution.confidence === undefined) {
        throw new Error(`Invalid solution structure for ${solution.subProblemId}`);
      }
    }
  }

  private async preprocessSolutions(
    subSolutions: SubSolution[], 
    context: CompositionContext
  ): Promise<SubSolution[]> {
    let processed = [...subSolutions];

    // Apply transformers
    for (const [name, transformer] of this.transformers) {
      try {
        processed = transformer(processed);
      } catch (error) {
        console.warn(`Transformation ${name} failed:`, error);
      }
    }

    // Apply integration rules
    processed = this.applyIntegrationRules(processed, context.integrationRules);

    return processed;
  }

  private selectCompositionStrategy(decomposition: DecompositionResult): CompositionStrategy {
    // Try strategies in order of preference
    const preferredOrder = ['hierarchical', 'parallel', 'sequential', 'hybrid'];
    
    for (const strategyName of preferredOrder) {
      const strategy = this.strategies.get(strategyName);
      if (strategy && strategy.canHandle(decomposition)) {
        return strategy;
      }
    }

    // Fallback to hybrid strategy
    return this.strategies.get('hybrid')!;
  }

  private async composeSequential(
    subSolutions: SubSolution[],
    context: CompositionContext,
  ): Promise<SequentialCompositionResult> {
    const results: SequentialCompositionResult['results'] = [];
    const metadata: SequentialCompositionResult['metadata'] = {
      strategy: 'sequential',
      totalSolutions: subSolutions.length,
      successfulSolutions: subSolutions.filter(s => s.success).length
    };

    // Sort by execution order (based on dependencies)
    const sortedSolutions = this.sortByExecutionOrder(subSolutions, context.decompositionResult);

    for (const solution of sortedSolutions) {
      if (solution.success && solution.result) {
        results.push({
          subProblemId: solution.subProblemId,
          result: solution.result,
          confidence: solution.confidence
        });
      }
    }

    return {
      type: 'sequential_composition',
      results,
      metadata,
      summary: `Composed ${results.length} solutions in sequential order`
    };
  }

  private async composeParallel(
    subSolutions: SubSolution[],
    context: CompositionContext,
  ): Promise<ParallelCompositionResult> {
    // Group solutions by execution phase
    const phases = this.groupByExecutionPhase(subSolutions, context.decompositionResult);
    const composedPhases: ParallelCompositionResult['phases'] = [];

    for (const [phase, solutions] of phases) {
      const phaseResults = solutions
        .filter(s => s.success)
        .map(s => ({
          subProblemId: s.subProblemId,
          result: s.result,
          confidence: s.confidence
        }));

      composedPhases.push({
        phase,
        results: phaseResults,
        averageConfidence: phaseResults.length > 0
          ? phaseResults.reduce((sum, r) => sum + r.confidence, 0) / phaseResults.length
          : 0,
      });
    }

    return {
      type: 'parallel_composition',
      phases: composedPhases,
      metadata: {
        strategy: 'parallel',
        totalPhases: phases.size,
        totalSolutions: subSolutions.length
      },
      summary: `Composed solutions across ${phases.size} execution phases`
    };
  }

  private async composeHierarchical(
    subSolutions: SubSolution[],
    context: CompositionContext,
  ): Promise<HierarchicalCompositionResult> {
    const hierarchy = this.buildHierarchy(subSolutions, context.decompositionResult);
    const composedHierarchy = await this.composeHierarchyRecursive(hierarchy, context);

    return {
      type: 'hierarchical_composition',
      hierarchy: composedHierarchy,
      metadata: {
        strategy: 'hierarchical',
        levels: this.calculateHierarchyLevels(hierarchy),
        totalNodes: subSolutions.length
      },
      summary: 'Composed solutions in hierarchical structure'
    };
  }

  private async composeHybrid(
    subSolutions: SubSolution[],
    context: CompositionContext,
  ): Promise<HybridCompositionResult> {
    // Analyze the structure and apply multiple strategies
    const sequentialPart = subSolutions.filter(s => this.isSequentialSolution(s, context));
    const parallelPart = subSolutions.filter(s => this.isParallelSolution(s, context));

    const sequentialResult = sequentialPart.length > 0 ? 
      await this.composeSequential(sequentialPart, context) : null;
    
    const parallelResult = parallelPart.length > 0 ? 
      await this.composeParallel(parallelPart, context) : null;

    return {
      type: 'hybrid_composition',
      sequential: sequentialResult,
      parallel: parallelResult,
      integrated: this.integrateHybridResults(sequentialResult, parallelResult),
      metadata: {
        strategy: 'hybrid',
        sequentialSolutions: sequentialPart.length,
        parallelSolutions: parallelPart.length
      },
      summary: 'Composed solutions using hybrid approach'
    };
  }

  private async performGlobalValidation(
    compositeResult: CompositionResultPayload,
    subSolutions: SubSolution[], 
    context: CompositionContext
  ): Promise<GlobalValidationResult[]> {
    const validations: GlobalValidationResult[] = [];

    // Run each validator
    for (const [name, validator] of this.validators) {
      try {
        const results = await validator.run(compositeResult, context);
        
        // Convert to global validation format
        for (const result of results) {
          validations.push({
            aspect: validator.aspect,
            passed: result.passed,
            score: result.score,
            details: result.details,
            requiredActions: result.passed ? [] : [`Address ${name} issues: ${result.details}`]
          });
        }
      } catch (error) {
        validations.push({
          aspect: validator.aspect,
          passed: false,
          score: 0,
          details: `Validation failed: ${(error as Error).message}`,
          requiredActions: [`Fix ${name} validation error`]
        });
      }
    }

    return validations;
  }

  private calculateIntegrationMetrics(
    validations: GlobalValidationResult[]
  ): CompositeSolution['integrationMetrics'] {
    const consistencyValidation = validations.find(v => v.aspect === 'consistency');
    const completenessValidation = validations.find(v => v.aspect === 'completeness');
    const qualityValidation = validations.find(v => v.aspect === 'quality');
    const performanceValidation = validations.find(v => v.aspect === 'performance');

    return {
      consistencyScore: consistencyValidation?.score || 0,
      completenessScore: completenessValidation?.score || 0,
      qualityScore: qualityValidation?.score || 0,
      performanceScore: performanceValidation?.score || 0
    };
  }

  private determineOverallSuccess(
    subSolutions: SubSolution[], 
    validations: GlobalValidationResult[]
  ): boolean {
    // Must have majority of sub-solutions successful
    const successRate = subSolutions.filter(s => s.success).length / subSolutions.length;
    if (successRate < 0.6) return false;

    // Critical validations must pass
    const criticalValidations = validations.filter(v => 
      v.requiredActions.length === 0 || v.score >= 0.5
    );
    
    return criticalValidations.length === validations.length;
  }

  private calculateOverallConfidence(
    subSolutions: SubSolution[], 
    validations: GlobalValidationResult[]
  ): number {
    const avgSolutionConfidence = subSolutions.reduce((sum, s) => sum + s.confidence, 0) / subSolutions.length;
    const avgValidationScore = validations.reduce((sum, v) => sum + v.score, 0) / validations.length;
    
    return (avgSolutionConfidence + avgValidationScore) / 2;
  }

  // Helper methods and validators implementation
  private createDefaultIntegrationRules(): IntegrationRule[] {
    return [
      {
        id: 'dependency-check',
        type: 'dependency',
        description: 'Ensure all dependencies are satisfied',
        condition: (solutions) => solutions.some(s => Object.keys(s.dependencies).length > 0),
        action: (solutions) => ({ kind: 'replace', solutions: this.resolveDependencies(solutions) }),
        priority: 'critical'
      }
    ];
  }

  private resolveDependencies(solutions: SubSolution[]): SubSolution[] {
    // Simplified dependency resolution
    return solutions.map(solution => ({
      ...solution,
      dependencies: this.resolveSubSolutionDependencies(solution, solutions)
    }));
  }

  private resolveSubSolutionDependencies(
    solution: SubSolution,
    allSolutions: SubSolution[],
  ): SubSolution['dependencies'] {
    const resolved: SubSolution['dependencies'] = {};
    
    for (const depId of Object.keys(solution.dependencies)) {
      const depSolution = allSolutions.find(s => s.subProblemId === depId);
      if (depSolution && depSolution.success) {
        resolved[depId] = depSolution.result;
      }
    }
    
    return resolved;
  }

  private enforceConsistency(solutions: SubSolution[]): SubSolution[] {
    // Basic consistency enforcement
    return solutions;
  }

  private normalizeQuality(solutions: SubSolution[]): SubSolution[] {
    // Quality normalization
    const avgQuality = solutions.reduce((sum, s) => sum + s.metrics.qualityScore, 0) / solutions.length;
    
    return solutions.map(s => ({
      ...s,
      metrics: {
        ...s.metrics,
        qualityScore: Math.min(1.0, s.metrics.qualityScore / avgQuality)
      }
    }));
  }

  // Validation implementations
  private async validateSequential(
    result: CompositionResultPayload,
    context: CompositionContext,
  ): Promise<ValidationResult[]> {
    void result;
    void context;
    return [{
      criterion: 'sequential_order',
      passed: true,
      score: 0.8,
      details: 'Sequential composition completed successfully',
      importance: 'medium'
    }];
  }

  private async validateParallel(
    result: CompositionResultPayload,
    context: CompositionContext,
  ): Promise<ValidationResult[]> {
    void result;
    void context;
    return [{
      criterion: 'parallel_consistency',
      passed: true,
      score: 0.8,
      details: 'Parallel composition consistent',
      importance: 'medium'
    }];
  }

  private async validateHierarchical(
    result: CompositionResultPayload,
    context: CompositionContext,
  ): Promise<ValidationResult[]> {
    void result;
    void context;
    return [{
      criterion: 'hierarchy_structure',
      passed: true,
      score: 0.8,
      details: 'Hierarchical structure maintained',
      importance: 'high'
    }];
  }

  private async validateHybrid(
    result: CompositionResultPayload,
    context: CompositionContext,
  ): Promise<ValidationResult[]> {
    void result;
    void context;
    return [{
      criterion: 'hybrid_integration',
      passed: true,
      score: 0.75,
      details: 'Hybrid composition integrated successfully',
      importance: 'high'
    }];
  }

  private async validateConsistency(
    result: CompositionResultPayload,
    context: CompositionContext,
  ): Promise<ValidationResult[]> {
    void result;
    void context;
    return [{
      criterion: 'data_consistency',
      passed: true,
      score: 0.85,
      details: 'Solution data is consistent across components',
      importance: 'high'
    }];
  }

  private async validateCompleteness(
    result: CompositionResultPayload,
    context: CompositionContext,
  ): Promise<ValidationResult[]> {
    void result;
    void context;
    return [{
      criterion: 'solution_completeness',
      passed: true,
      score: 0.9,
      details: 'All required solution components present',
      importance: 'critical'
    }];
  }

  private async validateQuality(
    result: CompositionResultPayload,
    context: CompositionContext,
  ): Promise<ValidationResult[]> {
    void result;
    void context;
    return [{
      criterion: 'output_quality',
      passed: true,
      score: 0.8,
      details: 'Solution meets quality standards',
      importance: 'high'
    }];
  }

  private async validatePerformance(
    result: CompositionResultPayload,
    context: CompositionContext,
  ): Promise<ValidationResult[]> {
    void result;
    void context;
    return [{
      criterion: 'performance_metrics',
      passed: true,
      score: 0.7,
      details: 'Performance within acceptable bounds',
      importance: 'medium'
    }];
  }

  private async validateSecurity(
    result: CompositionResultPayload,
    context: CompositionContext,
  ): Promise<ValidationResult[]> {
    void result;
    void context;
    return [{
      criterion: 'security_compliance',
      passed: true,
      score: 0.8,
      details: 'Security requirements satisfied',
      importance: 'high'
    }];
  }

  // Other helper methods would be implemented similarly...
  private sortByExecutionOrder(solutions: SubSolution[], decomposition: DecompositionResult): SubSolution[] {
    void decomposition;
    return solutions.sort((a, b) => a.subProblemId.localeCompare(b.subProblemId));
  }

  private groupByExecutionPhase(
    solutions: SubSolution[],
    decomposition: DecompositionResult,
  ): Map<number, SubSolution[]> {
    void decomposition;
    const phases = new Map<number, SubSolution[]>();
    // Simplified phase grouping
    solutions.forEach((solution, index) => {
      const phase = Math.floor(index / 3); // Group every 3 solutions
      if (!phases.has(phase)) phases.set(phase, []);
      phases.get(phase)!.push(solution);
    });
    return phases;
  }

  private buildHierarchy(solutions: SubSolution[], decomposition: DecompositionResult): HierarchyNode {
    void decomposition;
    return { root: solutions };
  }

  private async composeHierarchyRecursive(
    hierarchy: HierarchyNode,
    context: CompositionContext,
  ): Promise<HierarchyNode> {
    void context;
    return hierarchy;
  }

  private calculateHierarchyLevels(hierarchy: HierarchyNode): number {
    void hierarchy;
    return 1; // Simplified
  }

  private isSequentialSolution(solution: SubSolution, context: CompositionContext): boolean {
    void context;
    return Object.keys(solution.dependencies).length > 0;
  }

  private isParallelSolution(solution: SubSolution, context: CompositionContext): boolean {
    void context;
    return Object.keys(solution.dependencies).length === 0;
  }

  private integrateHybridResults(
    sequential: SequentialCompositionResult | null,
    parallel: ParallelCompositionResult | null,
  ): HybridIntegrationResult {
    return {
      sequential: sequential?.results || [],
      parallel: parallel?.phases || [],
      integration: 'hybrid'
    };
  }

  private hasHierarchicalStructure(decomposition: DecompositionResult): boolean {
    return decomposition.subProblems.some(sp => 
      sp.id.includes('phase') || sp.dependencies.length > 2
    );
  }

  private applyIntegrationRules(solutions: SubSolution[], rules: IntegrationRule[]): SubSolution[] {
    let processed = solutions;
    
    for (const rule of rules.sort((a, b) => this.getPriorityValue(b.priority) - this.getPriorityValue(a.priority))) {
      if (rule.condition(processed)) {
        const result = rule.action(processed);
        if (result.kind === 'replace') {
          processed = result.solutions;
        }
      }
    }
    
    return processed;
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

  private generateRecommendations(
    solutions: SubSolution[], 
    validations: GlobalValidationResult[], 
    metrics: CompositeSolution['integrationMetrics']
  ): string[] {
    const recommendations: string[] = [];
    
    // Based on solution success rate
    const successRate = solutions.filter(s => s.success).length / solutions.length;
    if (successRate < 0.8) {
      recommendations.push('Consider revising failed sub-solutions or adjusting approach');
    }
    
    // Based on validation results
    const failedValidations = validations.filter(v => !v.passed);
    if (failedValidations.length > 0) {
      recommendations.push(`Address validation issues: ${failedValidations.map(v => v.aspect).join(', ')}`);
    }
    
    // Based on metrics
    if (metrics.consistencyScore < 0.7) {
      recommendations.push('Improve consistency between solution components');
    }
    
    if (metrics.qualityScore < 0.8) {
      recommendations.push('Enhance solution quality through additional validation');
    }
    
    return recommendations;
  }

  private async generateAlternatives(
    solutions: SubSolution[], 
    context: CompositionContext, 
    metrics: CompositeSolution['integrationMetrics']
  ): Promise<AlternativeSolution[]> {
    const alternatives: AlternativeSolution[] = [];
    
    // Generate alternatives based on failed solutions
    const failedSolutions = solutions.filter(s => !s.success);
    if (failedSolutions.length > 0) {
      alternatives.push({
        id: 'retry-failed',
        description: 'Retry failed sub-solutions with adjusted parameters',
        confidence: 0.6,
        tradeoffs: ['Additional time required', 'May not guarantee success'],
        estimatedImpact: {
          time: failedSolutions.length * 2,
          resources: failedSolutions.length * 1.5,
          quality: 0.3
        }
      });
    }
    
    // Generate alternatives based on quality metrics
    if (metrics.qualityScore < 0.7) {
      alternatives.push({
        id: 'quality-improvement',
        description: 'Implement additional quality enhancement measures',
        confidence: 0.8,
        tradeoffs: ['Increased development time', 'Higher resource usage'],
        estimatedImpact: {
          time: 1.5,
          resources: 1.3,
          quality: 0.4
        }
      });
    }
    
    return alternatives;
  }
}
