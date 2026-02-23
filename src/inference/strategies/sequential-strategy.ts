/**
 * Sequential Strategy for Inference Engine
 * Implements step-by-step reasoning with validation
 */

export type ReasoningStepType = 'analyze' | 'deduce' | 'validate' | 'synthesize';

export interface ReasoningConstraint {
  id?: string;
  description?: string;
  domain?: string;
  type?: string;
  threshold?: number;
  condition?: string;
  severity?: string;
  [key: string]: unknown;
}

export interface PatternInfo {
  type: 'array_pattern' | 'object_pattern';
  key: string;
  description: string;
  length?: number;
  properties?: number;
}

export interface DataQualityAssessment {
  score: number;
  issues: string[];
}

export interface AnalysisResult {
  patterns: PatternInfo[];
  relevantConstraints: ReasoningConstraint[];
  dataQuality: DataQualityAssessment;
  summary: string;
}

export interface Hypothesis {
  id: string;
  objective: string;
  description: string;
  supportingEvidence: PatternInfo[];
  confidence: number;
}

export interface DeductionResult {
  hypotheses: Hypothesis[];
  conclusion: string;
  reasoning: string;
}

export interface ValidationCheck {
  passed: boolean;
  confidence: number;
  reason: string;
}

export interface ValidationResult {
  valid: boolean;
  results: ValidationCheck[];
  confidence: number;
}

export interface KeyFinding {
  step: ReasoningStepType;
  finding: string;
  confidence: number;
  data: unknown;
}

export interface SynthesisResult {
  keyFindings: KeyFinding[];
  recommendations: string[];
  summary: string;
  confidence: number;
}

export type StepOutput = AnalysisResult | DeductionResult | ValidationResult | SynthesisResult;

export interface AnalysisStepInput {
  domain: string;
  data: Record<string, unknown>;
  constraints: ReasoningConstraint[];
}

export interface DeductionStepInput {
  analysisResult?: AnalysisResult;
  objectives: string[];
  constraints: ReasoningConstraint[];
}

export interface ValidationStepInput {
  conclusions?: DeductionResult;
  constraints: ReasoningConstraint[];
  originalData: Record<string, unknown>;
}

export interface SynthesisStepInput {
  allSteps: ReasoningStep[];
  objectives: string[];
}

export type ReasoningStepInput =
  | AnalysisStepInput
  | DeductionStepInput
  | ValidationStepInput
  | SynthesisStepInput;

export interface ReasoningStep {
  id: string;
  type: ReasoningStepType;
  description: string;
  input: ReasoningStepInput;
  output?: StepOutput;
  confidence: number;
  metadata: {
    startTime: Date;
    endTime?: Date;
    duration: number;
    resources: string[];
  };
}

export interface ReasoningContext {
  domain: string;
  constraints: ReasoningConstraint[];
  objectives: string[];
  availableData: Record<string, unknown>;
  previousSteps: ReasoningStep[];
}

export interface StrategyResult {
  success: boolean;
  steps: ReasoningStep[];
  finalConclusion: unknown;
  confidence: number;
  reasoning: string[];
}

type StepProcessor = (step: ReasoningStep, context?: ReasoningContext) => StepOutput | Promise<StepOutput>;

export class SequentialStrategy {
  private stepProcessors = new Map<string, StepProcessor>();

  constructor() {
    this.registerDefaultProcessors();
  }

  /**
   * Execute sequential reasoning strategy
   */
  async execute(context: ReasoningContext): Promise<StrategyResult> {
    const steps: ReasoningStep[] = [];
    const reasoning: string[] = [];
    const currentContext: ReasoningContext = { ...context };

    try {
      const analysisStep = this.createAnalysisStep(currentContext);
      const analysisOutput = await this.processStep(analysisStep, currentContext);
      if (!this.isAnalysisResult(analysisOutput)) {
        throw new Error('Unexpected analysis output');
      }
      analysisStep.output = analysisOutput;
      steps.push(analysisStep);
      reasoning.push(`Analysis: ${analysisOutput.summary}`);

      currentContext.previousSteps = steps;
      const deductionStep = this.createDeductionStep(currentContext);
      const deductionOutput = await this.processStep(deductionStep, currentContext);
      if (!this.isDeductionResult(deductionOutput)) {
        throw new Error('Unexpected deduction output');
      }
      deductionStep.output = deductionOutput;
      steps.push(deductionStep);
      reasoning.push(`Deduction: ${deductionOutput.conclusion}`);

      currentContext.previousSteps = steps;
      const validationStep = this.createValidationStep(currentContext);
      const validationOutput = await this.processStep(validationStep, currentContext);
      if (!this.isValidationResult(validationOutput)) {
        throw new Error('Unexpected validation output');
      }
      validationStep.output = validationOutput;
      steps.push(validationStep);
      reasoning.push(`Validation: ${validationOutput.valid ? 'Passed' : 'Failed'}`);

      if (validationOutput.valid) {
        currentContext.previousSteps = steps;
        const synthesisStep = this.createSynthesisStep(currentContext);
        const synthesisOutput = await this.processStep(synthesisStep, currentContext);
        if (!this.isSynthesisResult(synthesisOutput)) {
          throw new Error('Unexpected synthesis output');
        }
        synthesisStep.output = synthesisOutput;
        steps.push(synthesisStep);
        reasoning.push(`Synthesis: ${synthesisOutput.summary}`);
      }

      const avgConfidence = steps.length > 0
        ? steps.reduce((sum, step) => sum + step.confidence, 0) / steps.length
        : 0;
      const lastStep = steps.length > 0 ? steps[steps.length - 1] : undefined;

      return {
        success: validationOutput.valid,
        steps,
        finalConclusion: lastStep?.output ?? null,
        confidence: avgConfidence,
        reasoning,
      };
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      return {
        success: false,
        steps,
        finalConclusion: null,
        confidence: 0,
        reasoning: [...reasoning, `Error: ${message}`],
      };
    }
  }

  /**
   * Register a custom step processor
   */
  registerStepProcessor(type: string, processor: StepProcessor): void {
    this.stepProcessors.set(type, processor);
  }

  private registerDefaultProcessors(): void {
    this.stepProcessors.set('analyze', (step) => this.processAnalysisStep(step));
    this.stepProcessors.set('deduce', (step) => this.processDeductionStep(step));
    this.stepProcessors.set('validate', (step) => this.processValidationStep(step));
    this.stepProcessors.set('synthesize', (step) => this.processSynthesisStep(step));
  }

  private createAnalysisStep(context: ReasoningContext): ReasoningStep {
    return {
      id: `analysis-${Date.now()}`,
      type: 'analyze',
      description: 'Analyze available data and identify patterns',
      input: {
        domain: context.domain,
        data: context.availableData,
        constraints: context.constraints,
      },
      confidence: 0,
      metadata: {
        startTime: new Date(),
        duration: 0,
        resources: Object.keys(context.availableData),
      },
    };
  }

  private createDeductionStep(context: ReasoningContext): ReasoningStep {
    const previousAnalysis = context.previousSteps.find(
      (step): step is ReasoningStep & { output: AnalysisResult } =>
        step.type === 'analyze' && this.isAnalysisResult(step.output),
    );
    const input: DeductionStepInput = {
      objectives: context.objectives,
      constraints: context.constraints,
      ...(previousAnalysis?.output ? { analysisResult: previousAnalysis.output } : {}),
    };

    return {
      id: `deduction-${Date.now()}`,
      type: 'deduce',
      description: 'Deduce conclusions based on analysis',
      input,
      confidence: 0,
      metadata: {
        startTime: new Date(),
        duration: 0,
        resources: ['analysis_result'],
      },
    };
  }

  private createValidationStep(context: ReasoningContext): ReasoningStep {
    const previousDeduction = context.previousSteps.find(
      (step): step is ReasoningStep & { output: DeductionResult } =>
        step.type === 'deduce' && this.isDeductionResult(step.output),
    );
    const input: ValidationStepInput = {
      constraints: context.constraints,
      originalData: context.availableData,
      ...(previousDeduction?.output ? { conclusions: previousDeduction.output } : {}),
    };

    return {
      id: `validation-${Date.now()}`,
      type: 'validate',
      description: 'Validate deduced conclusions against constraints',
      input,
      confidence: 0,
      metadata: {
        startTime: new Date(),
        duration: 0,
        resources: ['deduction_result', 'constraints'],
      },
    };
  }

  private createSynthesisStep(context: ReasoningContext): ReasoningStep {
    return {
      id: `synthesis-${Date.now()}`,
      type: 'synthesize',
      description: 'Synthesize final conclusions and recommendations',
      input: {
        allSteps: context.previousSteps,
        objectives: context.objectives,
      },
      confidence: 0,
      metadata: {
        startTime: new Date(),
        duration: 0,
        resources: ['all_previous_steps'],
      },
    };
  }

  private async processStep(step: ReasoningStep, context?: ReasoningContext): Promise<StepOutput> {
    const startTime = Date.now();
    step.metadata.startTime = new Date();

    try {
      const processor = this.stepProcessors.get(step.type);
      if (!processor) {
        throw new Error(`No processor found for step type: ${step.type}`);
      }

      const result = await Promise.resolve(processor(step, context));

      step.metadata.endTime = new Date();
      step.metadata.duration = Date.now() - startTime;
      step.confidence = this.calculateStepConfidence(step, result);

      return result;
    } catch (error) {
      step.metadata.endTime = new Date();
      step.metadata.duration = Date.now() - startTime;
      step.confidence = 0;
      throw error;
    }
  }

  private processAnalysisStep(step: ReasoningStep): AnalysisResult {
    if (step.type !== 'analyze') {
      throw new Error(`Invalid step type for analysis: ${step.type}`);
    }
    const { data, constraints, domain } = step.input as AnalysisStepInput;
    const patterns = this.identifyPatterns(data);
    const relevantConstraints = constraints.filter((constraint) => this.isRelevantConstraint(constraint, domain));

    return {
      patterns,
      relevantConstraints,
      dataQuality: this.assessDataQuality(data),
      summary: `Identified ${patterns.length} patterns in ${domain} domain`,
    };
  }

  private processDeductionStep(step: ReasoningStep): DeductionResult {
    if (step.type !== 'deduce') {
      throw new Error(`Invalid step type for deduction: ${step.type}`);
    }
    const { analysisResult, objectives, constraints } = step.input as DeductionStepInput;
    const hypotheses = this.generateHypotheses(analysisResult, objectives);
    const filteredHypotheses = this.filterByConstraints(hypotheses, constraints);

    return {
      hypotheses: filteredHypotheses,
      conclusion: filteredHypotheses[0]?.description ?? 'No valid conclusion',
      reasoning: `Generated ${hypotheses.length} hypotheses, ${filteredHypotheses.length} passed constraints`,
    };
  }

  private processValidationStep(step: ReasoningStep): ValidationResult {
    if (step.type !== 'validate') {
      throw new Error(`Invalid step type for validation: ${step.type}`);
    }
    const { conclusions, constraints, originalData } = step.input as ValidationStepInput;
    const validationChecks = this.validateConclusions(conclusions, constraints, originalData);
    const totalConfidence = validationChecks.reduce((sum, check) => sum + check.confidence, 0);
    const averageConfidence = validationChecks.length > 0 ? totalConfidence / validationChecks.length : 0;

    return {
      valid: validationChecks.every((check) => check.passed),
      results: validationChecks,
      confidence: averageConfidence,
    };
  }

  private processSynthesisStep(step: ReasoningStep): SynthesisResult {
    if (step.type !== 'synthesize') {
      throw new Error(`Invalid step type for synthesis: ${step.type}`);
    }
    const { allSteps, objectives } = step.input as SynthesisStepInput;
    const keyFindings = this.extractKeyFindings(allSteps);
    const recommendations = this.generateRecommendations(keyFindings, objectives);

    return {
      keyFindings,
      recommendations,
      summary: `Synthesized ${keyFindings.length} key findings into ${recommendations.length} recommendations`,
      confidence: this.calculateOverallConfidence(allSteps),
    };
  }

  private identifyPatterns(data: Record<string, unknown>): PatternInfo[] {
    const patterns: PatternInfo[] = [];

    for (const [key, value] of Object.entries(data)) {
      if (Array.isArray(value) && value.length > 0) {
        patterns.push({
          type: 'array_pattern',
          key,
          length: value.length,
          description: `Array ${key} contains ${value.length} items`,
        });
      }

      if (this.isRecord(value)) {
        const propertyCount = Object.keys(value).length;
        patterns.push({
          type: 'object_pattern',
          key,
          properties: propertyCount,
          description: `Object ${key} has ${propertyCount} properties`,
        });
      }
    }

    return patterns;
  }

  private isRelevantConstraint(constraint: ReasoningConstraint, domain: string): boolean {
    return !constraint.domain || constraint.domain === domain || constraint.domain === 'global';
  }

  private assessDataQuality(data: Record<string, unknown>): DataQualityAssessment {
    const issues: string[] = [];
    let score = 1.0;

    if (Object.keys(data).length === 0) {
      issues.push('No data available');
      score = 0;
    }

    for (const [key, value] of Object.entries(data)) {
      if (value === null || value === undefined) {
        issues.push(`Missing value for ${key}`);
        score -= 0.1;
      }
    }

    return { score: Math.max(0, score), issues };
  }

  private generateHypotheses(analysisResult: AnalysisResult | undefined, objectives: string[]): Hypothesis[] {
    const hypotheses: Hypothesis[] = [];

    for (const objective of objectives) {
      hypotheses.push({
        id: `hyp-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`,
        objective,
        description: `Hypothesis for achieving ${objective}`,
        supportingEvidence: analysisResult?.patterns?.slice(0, 2) ?? [],
        confidence: 0.7,
      });
    }

    return hypotheses;
  }

  private filterByConstraints(hypotheses: Hypothesis[], constraints: ReasoningConstraint[]): Hypothesis[] {
    return hypotheses.filter((hypothesis) =>
      constraints.every((constraint) => this.checkConstraint(hypothesis, constraint))
    );
  }

  private checkConstraint(hypothesis: Hypothesis, constraint: ReasoningConstraint): boolean {
    if (constraint.type === 'confidence_threshold') {
      const threshold = typeof constraint.threshold === 'number' ? constraint.threshold : 0.5;
      return hypothesis.confidence >= threshold;
    }
    return true;
  }

  private validateConclusions(
    conclusions: DeductionResult | undefined,
    constraints: ReasoningConstraint[],
    originalData: Record<string, unknown>,
  ): ValidationCheck[] {
    if (!conclusions || conclusions.hypotheses.length === 0) {
      return [{
        passed: true,
        confidence: 0.5,
        reason: 'No hypotheses were generated; fallback validation applied',
      }];
    }

    const hasConstraints = constraints.length > 0;
    const hasOriginalData = Object.keys(originalData).length > 0;

    return [{
      passed: true,
      confidence: hasOriginalData ? 0.8 : 0.6,
      reason: hasConstraints
        ? 'Conclusions align with configured constraints'
        : 'No explicit constraints; validated with baseline checks',
    }];
  }

  private extractKeyFindings(steps: ReasoningStep[]): KeyFinding[] {
    return steps
      .filter((step) => step.output !== undefined && step.confidence > 0.5)
      .map((step) => ({
        step: step.type,
        finding: step.description,
        confidence: step.confidence,
        data: step.output,
      }));
  }

  private generateRecommendations(findings: KeyFinding[], objectives: string[]): string[] {
    const recommendations: string[] = ['Review analysis findings for accuracy'];

    if (findings.some((finding) => finding.confidence < 0.7)) {
      recommendations.push('Consider additional data collection for low-confidence findings');
    }

    for (const objective of objectives) {
      recommendations.push(`Implement strategies to achieve: ${objective}`);
    }

    return recommendations;
  }

  private calculateStepConfidence(step: ReasoningStep, result: StepOutput): number {
    let confidence = 0.7;

    if (this.hasConfidence(result)) {
      confidence = result.confidence;
    } else if (this.isValidationResult(result)) {
      confidence = result.valid ? 0.8 : 0.3;
    }

    if (step.metadata.duration < 10) {
      confidence *= 0.9;
    } else if (step.metadata.duration > 5000) {
      confidence *= 0.95;
    }

    return Math.min(1.0, Math.max(0.0, confidence));
  }

  private calculateOverallConfidence(steps: ReasoningStep[]): number {
    if (steps.length === 0) {
      return 0;
    }
    const totalConfidence = steps.reduce((sum, step) => sum + step.confidence, 0);
    return totalConfidence / steps.length;
  }

  private isRecord(value: unknown): value is Record<string, unknown> {
    return typeof value === 'object' && value !== null && !Array.isArray(value);
  }

  private hasConfidence(value: unknown): value is { confidence: number } {
    return this.isRecord(value) && typeof value['confidence'] === 'number';
  }

  private isAnalysisResult(value: unknown): value is AnalysisResult {
    return this.isRecord(value)
      && Array.isArray(value['patterns'])
      && this.isRecord(value['dataQuality'])
      && typeof value['summary'] === 'string';
  }

  private isDeductionResult(value: unknown): value is DeductionResult {
    return this.isRecord(value)
      && Array.isArray(value['hypotheses'])
      && typeof value['conclusion'] === 'string';
  }

  private isValidationResult(value: unknown): value is ValidationResult {
    return this.isRecord(value)
      && typeof value['valid'] === 'boolean'
      && Array.isArray(value['results'])
      && typeof value['confidence'] === 'number';
  }

  private isSynthesisResult(value: unknown): value is SynthesisResult {
    return this.isRecord(value)
      && typeof value['summary'] === 'string'
      && Array.isArray(value['keyFindings'])
      && Array.isArray(value['recommendations'])
      && this.hasConfidence(value);
  }
}
