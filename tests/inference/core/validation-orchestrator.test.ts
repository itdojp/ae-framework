import { describe, expect, test } from 'vitest';

import {
  ValidationOrchestrator,
  type ValidationContext,
} from '../../../src/inference/core/validation-orchestrator.js';

function createContext(overrides: Partial<ValidationContext> = {}): ValidationContext {
  return {
    constraints: [],
    metadata: {},
    ...overrides,
  };
}

describe('ValidationOrchestrator', () => {
  test('createValidationPlan accepts primitive target values', async () => {
    const orchestrator = new ValidationOrchestrator();
    const plan = await orchestrator.createValidationPlan('raw-input', createContext());

    expect(plan.description).toBe('Validation plan for string value');
    expect(plan.totalValidators).toBeGreaterThan(0);
  });

  test('executeValidationPlan completes with unknown-friendly context metadata', async () => {
    const orchestrator = new ValidationOrchestrator();
    const context = createContext({
      metadata: { includePerformance: true, retryPolicy: { backoffStrategy: 'linear' } },
    });
    const target = { id: 'sample', status: 'ok' };

    const plan = await orchestrator.createValidationPlan(target, context, {
      categories: ['structural', 'functional', 'security', 'performance'],
    });
    const execution = await orchestrator.executeValidationPlan(plan.id, target, context);

    expect(execution.status).toBe('completed');
    expect(execution.overallResult.totalValidations).toBeGreaterThan(0);
  });
});
