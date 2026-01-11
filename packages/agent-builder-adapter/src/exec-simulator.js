import { parseFlow } from './parse-flow.js';
import { FLOW_SCHEMA_VERSION } from './types.js';

const DEFAULT_RUN_ID = 'sim-run';

export const simulateFlow = (flow, options = {}) => {
  const parsed = parseFlow(flow, options);
  const runId = options.runId ?? DEFAULT_RUN_ID;
  const startedAt = options.startedAt ?? '1970-01-01T00:00:00Z';

  const nodeResults = parsed.nodes.map((node, index) => ({
    id: node.id,
    kind: node.kind,
    status: 'simulated',
    order: index + 1,
  }));

  return {
    schemaVersion: parsed.schemaVersion ?? FLOW_SCHEMA_VERSION,
    runId,
    startedAt,
    nodes: nodeResults,
    edges: parsed.edges,
    metadata: parsed.metadata,
  };
};
