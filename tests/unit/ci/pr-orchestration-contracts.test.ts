import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  buildExecutionPlanV1,
  buildPrStateV1,
  inferActionTaskKind,
  resolvePrState,
  resolveReasonCode,
  writePrOrchestrationContracts,
} from '../../../scripts/ci/lib/pr-orchestration-contracts.mjs';

describe('pr-orchestration-contracts', () => {
  it('maps lane status/reason to state and reason code', () => {
    expect(resolvePrState('done', 'already merged')).toBe('merged');
    expect(resolvePrState('done', 'checks healthy, waiting for required checks/merge queue')).toBe('merge_eligible');
    expect(resolvePrState('skip', 'draft PR')).toBe('draft');
    expect(resolvePrState('skip', 'missing label autopilot:on')).toBe('ready_for_review');
    expect(resolvePrState('blocked', 'merge conflict')).toBe('blocked');

    expect(resolveReasonCode('merge conflict')).toBe('vcs.merge_conflict');
    expect(resolveReasonCode('missing policy labels: run-security')).toBe('policy.required_labels_missing');
    expect(resolveReasonCode('actionable execution failed: 1/2 failed')).toBe('review.actionable_execution_failed');
    expect(resolveReasonCode('')).toBe('autopilot.unknown');
  });

  it('infers action task kinds deterministically', () => {
    expect(inferActionTaskKind('round1: auto-label policy labels (run-security)')).toBe('label_sync');
    expect(inferActionTaskKind('round1: apply copilot auto-fix (force mode)')).toBe('suggestion_apply');
    expect(inferActionTaskKind('round1: dispatch copilot review gate')).toBe('workflow_dispatch');
    expect(inferActionTaskKind('round1: evaluate auto-merge eligibility')).toBe('gate_recheck');
    expect(inferActionTaskKind('round1: unknown message')).toBe('artifact_collect');
  });

  it('builds pr-state and execution-plan contracts', () => {
    const result = {
      status: 'blocked',
      reason: 'missing policy labels: run-security',
      actions: [
        'round1: auto-label policy labels (run-security)',
        'round1: dispatch copilot review gate',
      ],
      gateStatus: 'pending',
      number: 2405,
    };
    const now = '2026-03-04T04:00:00Z';
    const prState = buildPrStateV1({
      repository: 'itdojp/ae-framework',
      prNumber: 2405,
      headRefName: 'feat/demo',
      headRefOid: '1234567890abcdef',
      result,
      requiredChecks: ['gate', 'verify-lite'],
      workflow: 'Codex Autopilot Lane',
      runId: '12345',
      now,
    });
    expect(prState.contractId).toBe('pr-state.v1');
    expect(prState.state).toBe('blocked');
    expect(prState.blocked.reasonCode).toBe('policy.required_labels_missing');
    expect(prState.checkResults).toEqual([
      { name: 'gate', status: 'pending' },
      { name: 'verify-lite', status: 'missing' },
    ]);

    const executionPlan = buildExecutionPlanV1({
      repository: 'itdojp/ae-framework',
      prNumber: 2405,
      headRefOid: '1234567890abcdef',
      result,
      workflow: 'Codex Autopilot Lane',
      runId: '12345',
      now,
    });
    expect(executionPlan.contractId).toBe('execution-plan.v1');
    expect(executionPlan.targetState).toBe('blocked');
    expect(executionPlan.tasks[0]).toMatchObject({
      id: 't1',
      kind: 'label_sync',
      status: 'completed',
    });
    expect(executionPlan.tasks[executionPlan.tasks.length - 1]).toMatchObject({
      kind: 'block_emit',
      status: 'completed',
    });
  });

  it('writes contracts when enabled and skips otherwise', () => {
    const tempDir = mkdtempSync(path.join(os.tmpdir(), 'ae-pr-contracts-'));
    try {
      const dry = writePrOrchestrationContracts({
        enabled: false,
        prState: { a: 1 },
        executionPlan: { b: 2 },
        prStatePath: path.join(tempDir, 'pr-state.json'),
        executionPlanPath: path.join(tempDir, 'execution-plan.json'),
      });
      expect(dry.written).toBe(false);

      const written = writePrOrchestrationContracts({
        enabled: true,
        prState: { schemaVersion: '1.0.0' },
        executionPlan: { schemaVersion: '1.0.0' },
        prStatePath: path.join(tempDir, 'pr-state.json'),
        executionPlanPath: path.join(tempDir, 'execution-plan.json'),
      });
      expect(written.written).toBe(true);
      const prStateRaw = readFileSync(written.prStatePath, 'utf8');
      const executionPlanRaw = readFileSync(written.executionPlanPath, 'utf8');
      expect(JSON.parse(prStateRaw)).toEqual({ schemaVersion: '1.0.0' });
      expect(JSON.parse(executionPlanRaw)).toEqual({ schemaVersion: '1.0.0' });
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });
});
