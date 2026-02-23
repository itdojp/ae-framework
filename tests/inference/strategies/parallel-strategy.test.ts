import { beforeEach, describe, expect, test } from 'vitest';
import {
  ParallelStrategy,
  type ParallelTask,
} from '../../../src/inference/strategies/parallel-strategy.js';
import type {
  AnalysisResult,
  ReasoningConstraint,
  ReasoningContext,
  ReasoningStep,
  ValidationResult,
} from '../../../src/inference/strategies/sequential-strategy.js';

function createContext(overrides: Partial<ReasoningContext> = {}): ReasoningContext {
  return {
    domain: 'parallel-test',
    constraints: [],
    objectives: ['verify parallel strategy'],
    availableData: {
      numbers: [1, 2, 3],
      profile: { role: 'admin' },
    },
    previousSteps: [],
    ...overrides,
  };
}

function expectStep(step: ReasoningStep | undefined, message: string): ReasoningStep {
  expect(step, message).toBeDefined();
  return step as ReasoningStep;
}

function expectAnalysisOutput(step: ReasoningStep): AnalysisResult {
  expect(step.output).toBeDefined();
  return step.output as AnalysisResult;
}

function expectValidationOutput(step: ReasoningStep): ValidationResult {
  expect(step.output).toBeDefined();
  return step.output as ValidationResult;
}

describe('ParallelStrategy', () => {
  let strategy: ParallelStrategy;

  beforeEach(() => {
    strategy = new ParallelStrategy({ maxConcurrency: 2 });
  });

  test('keeps per-domain analyze input and restores analysis patterns', async () => {
    const constraints: ReasoningConstraint[] = [
      { id: 'c-1', description: 'must keep constraints' },
    ];

    strategy.registerTaskProcessor('analyze', async (task: ParallelTask) => {
      const domain = String(task.input['domain'] ?? 'unknown');
      const data = task.input['data'];
      const isArray = Array.isArray(data);

      return {
        domain,
        patterns: isArray
          ? [{ type: 'array', length: data.length }]
          : [{ type: 'object', keys: Object.keys((data as Record<string, unknown>) ?? {}).length }],
        statistics: isArray
          ? { type: 'array', count: data.length }
          : { type: 'object', properties: Object.keys((data as Record<string, unknown>) ?? {}).length },
        insights: [`analyzed ${domain}`],
      };
    });

    strategy.registerTaskProcessor('validate', async (task: ParallelTask) => {
      const constraint = task.input['constraint'] as ReasoningConstraint;
      return {
        constraintId: constraint.id,
        passed: true,
        confidence: 0.92,
        details: `validated ${constraint.id}`,
      };
    });

    strategy.registerTaskProcessor('synthesize', async () => ({
      summary: 'synthesized',
      confidence: 0.88,
    }));

    const result = await strategy.execute(createContext({ constraints }));

    expect(result.success).toBe(true);

    const analyzeNumbersStep = expectStep(
      result.steps.find((step) => step.id === 'analyze-numbers'),
      'analyze-numbers step should exist',
    );
    expect(analyzeNumbersStep.input).toMatchObject({
      domain: 'numbers',
      data: { items: [1, 2, 3] },
    });

    const analyzeOutput = expectAnalysisOutput(analyzeNumbersStep);
    expect(analyzeOutput.patterns).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ type: 'array_pattern', key: 'data', length: 3 }),
      ]),
    );
    expect(analyzeOutput.relevantConstraints).toEqual(constraints);
  });

  test('builds fallback analysis output when task result is non-object', async () => {
    strategy.registerTaskProcessor('analyze', async () => 'raw-analysis');
    strategy.registerTaskProcessor('validate', async () => ({
      passed: true,
      confidence: 0.9,
      details: 'validated',
    }));
    strategy.registerTaskProcessor('synthesize', async () => ({
      summary: 'done',
      confidence: 0.9,
    }));

    const result = await strategy.execute(createContext());

    const analyzeStep = expectStep(
      result.steps.find((step) => step.id === 'analyze-numbers'),
      'analyze step should exist',
    );
    const analyzeOutput = expectAnalysisOutput(analyzeStep);

    expect(analyzeOutput.summary).toBe('raw-analysis');
    expect(analyzeOutput.patterns).toEqual([]);
    expect(analyzeOutput.dataQuality.issues).toContain('analysis result was not structured');
  });

  test('maps each validation step to its own constraint', async () => {
    const constraints: ReasoningConstraint[] = [
      { id: 'c-a', description: 'constraint A' },
      { id: 'c-b', description: 'constraint B' },
    ];

    strategy.registerTaskProcessor('analyze', async () => ({
      patterns: [{ type: 'object', keys: 1 }],
      statistics: { type: 'object', properties: 1 },
      insights: ['analysis ok'],
    }));

    strategy.registerTaskProcessor('validate', async (task: ParallelTask) => {
      const constraint = task.input['constraint'] as ReasoningConstraint;
      return {
        constraintId: constraint.id,
        passed: true,
        confidence: 0.8,
        details: `validated ${constraint.id}`,
      };
    });

    strategy.registerTaskProcessor('synthesize', async () => ({
      summary: 'synthesized',
      confidence: 0.95,
    }));

    const result = await strategy.execute(createContext({ constraints }));

    const validationSteps = result.steps.filter((step) => step.type === 'validate');
    expect(validationSteps).toHaveLength(2);

    const inputConstraintIds: string[] = [];
    for (const step of validationSteps) {
      const output = expectValidationOutput(step);
      const stepInput = step.input as { constraints?: ReasoningConstraint[] };
      expect(stepInput.constraints).toHaveLength(1);
      inputConstraintIds.push(String(stepInput.constraints?.[0]?.id ?? ''));
      expect(output.results).toHaveLength(1);
      expect(output.results[0]?.passed).toBe(true);
    }
    expect(new Set(inputConstraintIds)).toEqual(new Set(constraints.map((constraint) => String(constraint.id))));
  });
});
