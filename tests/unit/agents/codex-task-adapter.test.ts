import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { join, resolve } from 'node:path';

import { createCodexTaskAdapter, finalizeTaskResponse, type Phase } from '../../../src/agents/codex-task-adapter';
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

describe.sequential('finalizeTaskResponse', () => {
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
    expect(response.nextActions[0]).toContain('Provide approval=1 and rerun codex task');
    expect(response.nextActions[1]).toBe('gh pr review --approve 1234');
    expect(response.warnings).toEqual(['REQUIRED_INPUT: approval=1']);
    expect(response.blockingReason).toBe('missing-approval');
    expect(response.requiredHumanInput).toBe('approval=1');
  });

  it('adds unblock action ahead of continue-oriented actions for blocked formal responses', () => {
    const response = finalizeTaskResponse(
      'formal',
      request,
      createBaseResponse({
        shouldBlockProgress: true,
        blockingReason: 'formal-validation-invalid',
        requiredHumanInput: 'resolve formal specification warnings and rerun formal phase',
        nextActions: [
          'pnpm -s run verify:lite',
          'pnpm run codex:generate:tests -- --use-operation-id',
        ],
        warnings: ['Invariant violation detected'],
      }),
    );

    expect(response.nextActions[0]).toContain('Provide resolve formal specification warnings and rerun formal phase and rerun codex task');
    expect(response.nextActions[1]).toBe('pnpm -s run verify:lite');
  });

  it('infers requiredHumanInput from REQUIRED_INPUT warning when explicit field is missing', () => {
    const response = finalizeTaskResponse(
      'validation',
      request,
      createBaseResponse({
        shouldBlockProgress: true,
        summary: 'validation needs policy exception',
        nextActions: ['rerun validation after policy check'],
        warnings: [' REQUIRED_INPUT: policy_exception_ticket=SEC-123 '],
        blockingReason: 'policy-exception-required',
      }),
    );

    expect(response.requiredHumanInput).toBe('policy_exception_ticket=SEC-123');
    expect(response.nextActions[0]).toBe('Provide policy_exception_ticket=SEC-123 and rerun codex task (validation)');
    expect(response.nextActions[1]).toBe('rerun validation after policy check');
  });

  it('does not duplicate unblock action when same action already exists (case-insensitive)', () => {
    const response = finalizeTaskResponse(
      'intent',
      request,
      createBaseResponse({
        shouldBlockProgress: true,
        summary: 'blocked',
        nextActions: [
          '  provide approval=1 and rerun codex task (intent)  ',
          'gh pr review --approve 1234',
        ],
        warnings: ['REQUIRED_INPUT: approval=1'],
        blockingReason: 'missing-approval',
      }),
    );

    const unblockActions = response.nextActions.filter((item) => item.toLowerCase().includes('rerun codex task'));
    expect(unblockActions).toHaveLength(1);
    expect(response.nextActions[0]).toBe('provide approval=1 and rerun codex task (intent)');
    expect(response.nextActions[1]).toBe('gh pr review --approve 1234');
  });

  it('uses deterministic blocked summary when summary is empty', () => {
    const response = finalizeTaskResponse(
      'ui',
      request,
      createBaseResponse({
        summary: '   ',
        shouldBlockProgress: true,
        nextActions: ['Provide approval=1 and rerun codex task (ui)'],
        warnings: ['REQUIRED_INPUT: approval=1'],
      }),
    );

    expect(response.summary).toBe('Blocked: ui task requires human input');
  });

  it('reports scaffold generation separately and does not create model-check success evidence', async () => {
    const tmpRoot = resolve('.codex-local/tmp');
    mkdirSync(tmpRoot, { recursive: true });
    const artifactDir = mkdtempSync(join(tmpRoot, 'codex-formal-scaffold-'));
    const previousArtifactDir = process.env['CODEX_ARTIFACTS_DIR'];
    process.env['CODEX_ARTIFACTS_DIR'] = artifactDir;

    try {
      const adapter = createCodexTaskAdapter();
      const response = await adapter.handleTask({
        description: 'Generate a formal scaffold for inventory reservation safety.',
        prompt: 'Inventory reservation must never make onHand negative.',
        subagent_type: 'formal',
        context: {},
      });

      expect(response.summary).toContain('Formal scaffold generated');
      expect(response.summary).not.toMatch(/model.check.*(?:ok|pass|success)/i);
      expect(response.formal).toMatchObject({
        scaffold: {
          status: 'generated',
          artifactStatus: 'draft',
          artifactPath: expect.any(String),
        },
        modelChecking: {
          status: 'not-run',
          evidenceArtifact: null,
          runnerCommands: expect.arrayContaining(['pnpm run verify:tla -- --engine=tlc']),
        },
      });
      expect(existsSync(join(artifactDir, 'formal.tla'))).toBe(true);
      expect(existsSync(join(artifactDir, 'openapi.yaml'))).toBe(true);
      expect(existsSync(join(artifactDir, 'model-check.json'))).toBe(false);

      const persisted = JSON.parse(readFileSync(join(artifactDir, 'result-formal.json'), 'utf8'));
      expect(persisted.response.formal.modelChecking).toMatchObject({
        status: 'not-run',
        evidenceArtifact: null,
      });
    } finally {
      if (previousArtifactDir === undefined) {
        delete process.env['CODEX_ARTIFACTS_DIR'];
      } else {
        process.env['CODEX_ARTIFACTS_DIR'] = previousArtifactDir;
      }
      rmSync(artifactDir, { recursive: true, force: true });
    }
  });
});
