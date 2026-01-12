const normalizeNameList = (value, fallback) => {
  if (Array.isArray(value) && value.length > 0) {
    return value;
  }
  return Array.isArray(fallback) && fallback.length > 0 ? fallback : [];
};

export function adaptAgentBuilderFlow(rawFlow) {
  if (!rawFlow || typeof rawFlow !== 'object') {
    return rawFlow;
  }

  const nodes = Array.isArray(rawFlow.nodes) ? rawFlow.nodes : [];
  const edges = Array.isArray(rawFlow.edges) ? rawFlow.edges : [];

  const adaptedNodes = nodes.map((node) => {
    if (!node || typeof node !== 'object') {
      return node;
    }
    const id = node.id ?? node.name ?? node.key;
    const kind = node.kind ?? node.type ?? node.action ?? node.role;
    const params = node.params ?? node.parameters ?? node.config ?? node.settings;
    const input = normalizeNameList(node.input, node.inputs);
    const output = normalizeNameList(node.output, node.outputs);
    return {
      ...node,
      ...(id ? { id } : {}),
      ...(kind ? { kind } : {}),
      ...(params ? { params } : {}),
      ...(input.length > 0 ? { input } : {}),
      ...(output.length > 0 ? { output } : {}),
    };
  });

  const adaptedEdges = edges.map((edge) => {
    if (!edge || typeof edge !== 'object') {
      return edge;
    }
    const from = edge.from ?? edge.source;
    const to = edge.to ?? edge.target;
    return {
      ...edge,
      ...(from ? { from } : {}),
      ...(to ? { to } : {}),
    };
  });

  const metadata = rawFlow.metadata ?? rawFlow.meta ?? rawFlow.info;
  const correlation =
    rawFlow.correlation ??
    (rawFlow.context && typeof rawFlow.context === 'object' ? rawFlow.context.correlation : undefined);

  return {
    ...rawFlow,
    schemaVersion: rawFlow.schemaVersion ?? '0.1.0',
    nodes: adaptedNodes,
    edges: adaptedEdges,
    ...(metadata ? { metadata } : {}),
    ...(correlation ? { correlation } : {}),
  };
}
