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

  it('returns non-object inputs as-is', () => {
    expect(adaptAgentBuilderFlow(null)).toBeNull();
    expect(adaptAgentBuilderFlow('flow')).toBe('flow');
  });

  it('handles empty arrays and missing metadata/correlation', () => {
    const adapted = adaptAgentBuilderFlow({ nodes: [], edges: [] });

    expect(adapted.nodes).toEqual([]);
    expect(adapted.edges).toEqual([]);
    expect(adapted.metadata).toBeUndefined();
    expect(adapted.correlation).toBeUndefined();
  });

  it('prefers alternate field names and omits empty input/output', () => {
    const adapted = adaptAgentBuilderFlow({
      nodes: [
        {
          key: 'node-key',
          action: 'tests2code',
          config: { alpha: true },
          inputs: [],
        },
      ],
      edges: [
        { source: 'node-key', target: 'node-next' },
      ],
    });

    expect(adapted.nodes[0]).toMatchObject({
      id: 'node-key',
      kind: 'tests2code',
      params: { alpha: true },
    });
    expect(adapted.nodes[0].input).toBeUndefined();
    expect(adapted.nodes[0].output).toBeUndefined();
    expect(adapted.edges[0]).toMatchObject({ from: 'node-key', to: 'node-next' });
  });
});
