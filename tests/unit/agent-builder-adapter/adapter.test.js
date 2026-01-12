import { describe, it, expect } from 'vitest';
import { adaptAgentBuilderFlow } from '../../../packages/agent-builder-adapter/src/adapter.js';

const sample = {
  nodes: [
    {
      name: 'node-1',
      type: 'intent2formal',
      parameters: { foo: 'bar' },
      inputs: ['input-a'],
      outputs: ['output-a'],
    },
  ],
  edges: [
    { source: 'node-1', target: 'node-2' },
  ],
  meta: { name: 'sample-flow' },
  context: { correlation: { runId: 'run-1' } },
};

describe('adaptAgentBuilderFlow', () => {
  it('normalizes Agent Builder shapes into flow schema', () => {
    const adapted = adaptAgentBuilderFlow(sample);

    expect(adapted.schemaVersion).toBe('0.1.0');
    expect(adapted.nodes[0]).toMatchObject({
      id: 'node-1',
      kind: 'intent2formal',
      params: { foo: 'bar' },
      input: ['input-a'],
      output: ['output-a'],
    });
    expect(adapted.edges[0]).toEqual({ source: 'node-1', target: 'node-2', from: 'node-1', to: 'node-2' });
    expect(adapted.metadata).toEqual({ name: 'sample-flow' });
    expect(adapted.correlation).toEqual({ runId: 'run-1' });
  });
});
