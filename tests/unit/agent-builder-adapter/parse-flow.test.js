import { describe, it, expect } from 'vitest';
import { parseFlow } from '../../../packages/agent-builder-adapter/src/parse-flow.js';

const baseFlow = {
  schemaVersion: '0.1.0',
  nodes: [
    { id: ' step-1 ', kind: 'intent2formal' },
    { id: 'step-2', kind: 'tests2code' },
  ],
  edges: [
    { from: ' step-1 ', to: ' step-2 ' },
  ],
};

describe('parseFlow', () => {
  it('trims node ids and edge endpoints', () => {
    const parsed = parseFlow(baseFlow);

    expect(parsed.nodes.map((node) => node.id)).toEqual(['step-1', 'step-2']);
    expect(parsed.edges).toEqual([{ from: 'step-1', to: 'step-2' }]);
  });

  it('rejects unknown kinds when enforceKnownKinds is true', () => {
    const flow = {
      ...baseFlow,
      nodes: [{ id: 'n1', kind: 'unknown-kind' }],
      edges: [],
    };

    expect(() => parseFlow(flow, { enforceKnownKinds: true })).toThrow(
      'Unknown flow node kind(s): unknown-kind',
    );
  });
});
