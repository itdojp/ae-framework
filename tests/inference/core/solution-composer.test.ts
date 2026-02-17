import { beforeEach, describe, expect, test } from 'vitest';
import {
  SolutionComposer,
  type SubSolution,
  type ValidationResult,
} from '../../../src/inference/core/solution-composer.js';
import type {
  DecompositionResult,
  Problem,
  SubProblem,
} from '../../../src/inference/core/problem-decomposer.js';

type SubSolutionOverrides = Partial<Omit<SubSolution, 'metrics'>> & {
  metrics?: Partial<SubSolution['metrics']>;
};

function createProblem(problemId: string): Problem {
  return {
    id: problemId,
    title: `${problemId} title`,
    description: `${problemId} description`,
    domain: 'software_development',
    complexity: 'medium',
    priority: 'medium',
    constraints: [],
    context: {},
  };
}

function createSubProblem(
  problemId: string,
  subProblemId: string,
  type: SubProblem['type'],
  dependencies: string[] = [],
): SubProblem {
  return {
    id: subProblemId,
    parentId: problemId,
    title: `${subProblemId} title`,
    description: `${subProblemId} description`,
    type,
    dependencies,
    estimatedComplexity: 1,
    estimatedTime: 1,
    requiredResources: [],
    constraints: [],
    successCriteria: [],
    fallbackStrategies: [],
  };
}

function createDecompositionResult(
  problemId: string,
  subProblems: SubProblem[],
): DecompositionResult {
  const originalProblem = createProblem(problemId);
  const executionPlan = subProblems.map((subProblem, index) => ({
    id: `node-${index}`,
    subProblemId: subProblem.id,
    phase: index,
    canRunInParallel: subProblem.type === 'parallel',
    dependencies: subProblem.dependencies,
    estimatedStartTime: index,
    estimatedEndTime: index + 1,
  }));

  return {
    originalProblem,
    subProblems,
    executionPlan,
    estimatedTotalTime: subProblems.length,
    criticalPath: subProblems.map((subProblem) => subProblem.id),
    riskAssessment: {
      overallRisk: 'low',
      riskFactors: [],
      mitigationStrategies: [],
      contingencyPlan: [],
    },
    recommendations: [],
  };
}

function createSubSolution(
  subProblemId: string,
  overrides: SubSolutionOverrides = {},
): SubSolution {
  const defaultMetrics: SubSolution['metrics'] = {
    executionTime: 1,
    resourcesUsed: ['cpu'],
    qualityScore: 0.8,
  };

  return {
    subProblemId,
    success: true,
    confidence: 0.9,
    result: { subProblemId },
    metrics: {
      ...defaultMetrics,
      ...overrides.metrics,
    },
    validationResults: [],
    dependencies: {},
    ...overrides,
  };
}

describe('SolutionComposer', () => {
  let composer: SolutionComposer;

  beforeEach(() => {
    composer = new SolutionComposer();
  });

  test('parallel composition keeps averageConfidence at 0 when phase has no successful solutions', async () => {
    const problemId = 'parallel-empty-phase';
    const subProblem = createSubProblem(problemId, 'task-a', 'parallel');
    const decomposition = createDecompositionResult(problemId, [subProblem]);
    const subSolutions = [
      createSubSolution(subProblem.id, {
        success: false,
        confidence: 0,
        result: null,
        error: new Error('forced failure'),
      }),
    ];

    const composed = await composer.compose(subSolutions, decomposition);

    expect(composed.compositeResult.type).toBe('parallel_composition');
    if (composed.compositeResult.type !== 'parallel_composition') {
      throw new Error('parallel composition was expected');
    }

    expect(composed.compositeResult.phases).toHaveLength(1);
    expect(composed.compositeResult.phases[0]?.results).toHaveLength(0);
    expect(composed.compositeResult.phases[0]?.averageConfidence).toBe(0);
  });

  test('registerValidator supports reserved key names with explicit aspect mapping', async () => {
    const customDetail = 'reserved-name-validator';
    const customResult: ValidationResult = {
      criterion: 'reserved_name',
      passed: true,
      score: 0.91,
      details: customDetail,
      importance: 'high',
    };

    composer.registerValidator(
      'toString',
      async () => [customResult],
      'security',
    );

    const problemId = 'reserved-validator-name';
    const subProblem = createSubProblem(problemId, 'task-b', 'sequential');
    const decomposition = createDecompositionResult(problemId, [subProblem]);
    const subSolutions = [createSubSolution(subProblem.id)];

    const composed = await composer.compose(subSolutions, decomposition);
    const customValidation = composed.validationResults.find(
      (result) => result.details === customDetail,
    );

    expect(customValidation).toBeDefined();
    expect(customValidation?.aspect).toBe('security');
    expect(customValidation?.passed).toBe(true);
  });
});
