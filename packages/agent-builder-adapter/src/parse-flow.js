import { FLOW_SCHEMA_VERSION, NODE_KINDS } from './types.js';

const isNonEmptyString = (value) => typeof value === 'string' && value.trim().length > 0;

const normalizeArray = (value) => (Array.isArray(value) ? value : []);

const assertValidNode = (node, index) => {
  if (!node || typeof node !== 'object') {
    throw new Error(`Flow node at index ${index} must be an object.`);
  }
  if (!isNonEmptyString(node.id)) {
    throw new Error(`Flow node at index ${index} is missing a valid id.`);
  }
  if (!isNonEmptyString(node.kind)) {
    throw new Error(`Flow node ${node.id} is missing a valid kind.`);
  }
  return {
    id: node.id.trim(),
    kind: node.kind.trim(),
    params: node.params ?? {},
    input: normalizeArray(node.input),
    output: normalizeArray(node.output),
  };
};

const assertValidEdge = (edge, index, nodeIds) => {
  if (!edge || typeof edge !== 'object') {
    throw new Error(`Flow edge at index ${index} must be an object.`);
  }
  if (!isNonEmptyString(edge.from) || !isNonEmptyString(edge.to)) {
    throw new Error(`Flow edge at index ${index} must include from/to.`);
  }
  const from = edge.from.trim();
  const to = edge.to.trim();
  if (!nodeIds.has(from)) {
    throw new Error(`Flow edge from=${from} does not match a node id.`);
  }
  if (!nodeIds.has(to)) {
    throw new Error(`Flow edge to=${to} does not match a node id.`);
  }
  return {
    from,
    to,
  };
};

export const parseFlow = (flow, options = {}) => {
  if (!flow || typeof flow !== 'object') {
    throw new Error('Flow must be an object.');
  }

  const schemaVersion = isNonEmptyString(flow.schemaVersion)
    ? flow.schemaVersion.trim()
    : FLOW_SCHEMA_VERSION;
  const nodes = normalizeArray(flow.nodes).map(assertValidNode);
  const nodeIds = new Set(nodes.map((node) => node.id));
  const edges = normalizeArray(flow.edges).map((edge, index) =>
    assertValidEdge(edge, index, nodeIds),
  );

  if (options.enforceKnownKinds) {
    const unknownKinds = nodes
      .map((node) => node.kind)
      .filter((kind) => !NODE_KINDS.includes(kind));
    if (unknownKinds.length > 0) {
      throw new Error(`Unknown flow node kind(s): ${unknownKinds.join(', ')}`);
    }
  }

  return {
    schemaVersion,
    nodes,
    edges,
    metadata: flow.metadata ?? {},
    correlation: flow.correlation ?? null,
  };
};
