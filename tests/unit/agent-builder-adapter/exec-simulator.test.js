import { describe, it, expect } from 'vitest';
import { simulateFlow } from '../../../packages/agent-builder-adapter/src/exec-simulator.js';

const flow = {
  schemaVersion: '0.1.0',
  nodes: [
    { id: 'n1', kind: 'intent2formal' },
    { id: 'n2', kind: 'code2verify' },
  ],
  edges: [{ from: 'n1', to: 'n2' }],
  metadata: { name: 'demo' },
};

describe('simulateFlow', () => {
  it('returns deterministic simulation output', () => {
    const result = simulateFlow(flow, { runId: 'run-1', startedAt: '2000-01-01T00:00:00Z' });

    expect(result.schemaVersion).toBe('0.1.0');
    expect(result.runId).toBe('run-1');
    expect(result.startedAt).toBe('2000-01-01T00:00:00Z');
    expect(result.nodes).toEqual([
      { id: 'n1', kind: 'intent2formal', status: 'simulated', order: 1 },
      { id: 'n2', kind: 'code2verify', status: 'simulated', order: 2 },
    ]);
    expect(result.edges).toEqual([{ from: 'n1', to: 'n2' }]);
    expect(result.metadata).toEqual({ name: 'demo' });
  });
});
