import { describe, expect, it } from 'vitest';

import { finalizeTaskResponse, type Phase } from '../../../src/agents/codex-task-adapter';
import type { TaskRequest, TaskResponse } from '../../../src/agents/task-types';

const request: TaskRequest = {
  description: 'test request',
  prompt: 'test request',
  subagent_type: 'intent',
  context: {},
};

function createBaseResponse(overrides: Partial<TaskResponse> = {}): TaskResponse {
  return {
    summary: 'ok',
    analysis: 'analysis',
    recommendations: ['r1'],
    nextActions: ['a1'],
    warnings: [],
    shouldBlockProgress: false,
    ...overrides,
  };
}

describe('finalizeTaskResponse', () => {
  it('fills default nextActions for unblocked responses in all phases', () => {
    const phases: Phase[] = ['intent', 'formal', 'stories', 'validation', 'modeling', 'ui'];
    for (const phase of phases) {
      const response = finalizeTaskResponse(
        phase,
        request,
        createBaseResponse({
          nextActions: [],
          shouldBlockProgress: false,
          warnings: [],
        }),
      );
      expect(response.shouldBlockProgress).toBe(false);
      expect(response.nextActions.length).toBeGreaterThan(0);
      expect(response.nextActions.every((item) => item.trim().length > 0)).toBe(true);
    }
  });

  it('normalizes blocked responses with missing warnings/actions into deterministic payload', () => {
    const response = finalizeTaskResponse(
      'formal',
      request,
      createBaseResponse({
        summary: 'formal check failed',
        shouldBlockProgress: true,
        nextActions: [],
        warnings: [],
      }),
    );

    expect(response.shouldBlockProgress).toBe(true);
    expect(response.summary.startsWith('Blocked:')).toBe(true);
    expect(response.nextActions.length).toBeGreaterThan(0);
    expect(response.warnings.length).toBeGreaterThan(0);
    expect(response.warnings[0]).toContain('INTERNAL CONTRACT VIOLATION');
    expect(response.blockingReason).toBe('human-input-required');
    expect(response.requiredHumanInput).toBe('resolve-human-input-required');
  });

  it('preserves explicit blocked metadata and strips empty entries', () => {
    const response = finalizeTaskResponse(
      'intent',
      request,
      createBaseResponse({
        shouldBlockProgress: true,
        summary: 'Blocked: waiting approval',
        nextActions: ['  gh pr review --approve 1234  ', ''],
        warnings: [' REQUIRED_INPUT: approval=1 ', ''],
        blockingReason: 'missing-approval',
        requiredHumanInput: 'approval=1',
      }),
    );

    expect(response.summary).toBe('Blocked: waiting approval');
    expect(response.nextActions).toEqual(['gh pr review --approve 1234']);
    expect(response.warnings).toEqual(['REQUIRED_INPUT: approval=1']);
    expect(response.blockingReason).toBe('missing-approval');
    expect(response.requiredHumanInput).toBe('approval=1');
  });

  it('infers requiredHumanInput from warnings when not explicitly set', () => {
    const response = finalizeTaskResponse(
      'stories',
      request,
      createBaseResponse({
        shouldBlockProgress: true,
        summary: 'approval needed',
        nextActions: [],
        warnings: ['required_input: approval-token=abc'],
      }),
    );

    expect(response.shouldBlockProgress).toBe(true);
    expect(response.requiredHumanInput).toBe('approval-token=abc');
    expect(response.nextActions[0]).toContain('approval-token=abc');
  });
});
