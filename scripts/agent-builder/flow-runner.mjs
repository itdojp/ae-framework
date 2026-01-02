#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { fromVerifyLite } from '@ae-framework/envelope';

const DEFAULT_FLOW_SCHEMA = 'schema/flow.schema.json';

const ajvCache = new Map();

function readJson(filePath) {
  const resolved = path.resolve(filePath);
  return JSON.parse(fs.readFileSync(resolved, 'utf8'));
}

function getValidator(schemaPath) {
  const resolvedSchema = path.resolve(schemaPath);
  if (ajvCache.has(resolvedSchema)) {
    return ajvCache.get(resolvedSchema);
  }
  const schema = readJson(resolvedSchema);
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  ajvCache.set(resolvedSchema, validate);
  return validate;
}

export function loadFlowDefinition(
  flowPath,
  { schemaPath = DEFAULT_FLOW_SCHEMA, validate = true, adapter = null } = {},
) {
  const resolvedFlow = path.resolve(flowPath);
  if (!fs.existsSync(resolvedFlow)) {
    throw new Error(`Flow definition not found: ${resolvedFlow}`);
  }

  const raw = readJson(resolvedFlow);
  const flow = adapter ? adapter(raw) : raw;

  if (validate) {
    const validateFn = getValidator(schemaPath);
    const ok = validateFn(flow);
    if (!ok) {
      const error = new Error('Flow definition failed schema validation');
      error.validationErrors = validateFn.errors ?? [];
      throw error;
    }
  }

  return {
    flow,
    path: resolvedFlow,
    raw,
  };
}

function normalizeNameList(value, fallback) {
  if (Array.isArray(value) && value.length > 0) {
    return value;
  }
  return Array.isArray(fallback) && fallback.length > 0 ? fallback : [];
}

function adaptAgentBuilderFlow(rawFlow) {
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

function resolveAdapter(name) {
  if (!name) return null;
  if (name === 'agent-builder') return adaptAgentBuilderFlow;
  throw new Error(`[agent-builder] Unknown adapter: ${name}`);
}

function deriveExecutionPlan(flow) {
  const nodes = Array.isArray(flow?.nodes) ? flow.nodes : [];
  if (nodes.length === 0) {
    return [];
  }

  const nodeIndex = new Map();
  nodes.forEach((node, idx) => {
    const id = node?.id;
    if (!id) {
      throw new Error(`Flow node at index ${idx} is missing an "id"`);
    }
    if (nodeIndex.has(id)) {
      throw new Error(`Duplicate flow node id detected: ${id}`);
    }
    nodeIndex.set(id, { node, index: idx });
  });

  const edges = Array.isArray(flow?.edges) ? flow.edges : [];
  if (edges.length === 0) {
    return nodes;
  }

  const adjacency = new Map();
  const indegree = new Map();
  nodes.forEach((node) => {
    adjacency.set(node.id, []);
    indegree.set(node.id, 0);
  });

  edges.forEach((edge, idx) => {
    const from = edge?.from;
    const to = edge?.to;
    if (!from || !to) {
      throw new Error(`Flow edge at index ${idx} is missing "from" or "to"`);
    }
    if (!nodeIndex.has(from) || !nodeIndex.has(to)) {
      throw new Error(`Flow edge references unknown node: ${from ?? 'undefined'} -> ${to ?? 'undefined'}`);
    }
    adjacency.get(from).push(to);
    indegree.set(to, (indegree.get(to) ?? 0) + 1);
  });

  const queue = nodes
    .filter((node) => (indegree.get(node.id) ?? 0) === 0)
    .map((node) => ({ node, index: nodeIndex.get(node.id).index }))
    .sort((a, b) => a.index - b.index);

  const plan = [];
  while (queue.length > 0) {
    const current = queue.shift();
    plan.push(current.node);
    const neighbours = adjacency.get(current.node.id) ?? [];
    neighbours.forEach((neighbourId) => {
      const nextDegree = (indegree.get(neighbourId) ?? 0) - 1;
      indegree.set(neighbourId, nextDegree);
      if (nextDegree === 0) {
        const neighbourMeta = nodeIndex.get(neighbourId);
        queue.push({ node: neighbourMeta.node, index: neighbourMeta.index });
        queue.sort((a, b) => a.index - b.index);
      }
    });
  }

  if (plan.length !== nodes.length) {
    throw new Error('Flow graph contains a cycle or disconnected dependency');
  }

  return plan;
}

function buildCorrelation(flow, options) {
  const fromFlow = flow?.correlation ?? {};
  const provided = options.correlation ?? {};
  const merged = { ...fromFlow, ...provided };
  const name = flow?.metadata?.name ?? 'agent-builder-flow';
  return {
    runId: merged.runId ?? `flow-${name}`,
    workflow: merged.workflow ?? name,
    commit: merged.commit ?? process.env.GITHUB_SHA ?? 'local',
    branch: merged.branch ?? process.env.GITHUB_REF ?? 'local',
    ...(merged.traceIds ? { traceIds: merged.traceIds } : {}),
  };
}

function simulateNode(node, flow, inputs, options, state) {
  const params = node?.params ?? {};
  const outputNames = normalizeNameList(node?.output, [node.id]);
  const outputs = {};
  const info = {};
  const storeOutputs = (value) => {
    outputNames.forEach((name) => {
      outputs[name] = value;
    });
  };

  switch (node?.kind) {
    case 'intent2formal': {
      const spec = {
        id: node.id,
        language: params.language ?? 'en',
        description: `Formal specification seeded for flow "${flow?.metadata?.name ?? node.id}"`,
        generatedAt: options.generatedAt ?? new Date().toISOString(),
      };
      storeOutputs(spec);
      info.type = 'spec';
      info.language = spec.language;
      break;
    }
    case 'tests2code': {
      const sourceSpec = inputs[0] ?? null;
      const code = {
        language: params.language ?? 'ts',
        generatedAt: options.generatedAt ?? new Date().toISOString(),
        basedOn: sourceSpec,
      };
      storeOutputs(code);
      info.type = 'code';
      info.language = code.language;
      break;
    }
    case 'code2verify': {
      const summary = options.verifyLiteSummary ?? null;
      let envelope = null;
      if (summary) {
        const correlation = buildCorrelation(flow, options);
        envelope = fromVerifyLite(summary, {
          correlation,
          generatedAt: options.generatedAt ?? new Date().toISOString(),
          source: options.envelopeSource ?? 'verify-lite',
          tempoLinkTemplate: options.tempoLinkTemplate,
          notes: options.notes,
          extraArtifacts: options.extraArtifacts,
        });
      }
      const result = {
        status: envelope ? 'verified' : 'simulated',
        inputs,
        envelope,
      };
      storeOutputs(result);
      if (envelope) {
        state.envelope = envelope;
      }
      info.type = 'verification';
      info.envelope = Boolean(envelope);
      break;
    }
    default: {
      const payload = {
        kind: node?.kind ?? 'unknown',
        params,
        inputs,
      };
      storeOutputs(payload);
      info.type = 'noop';
      break;
    }
  }

  return { outputs, info };
}

export function executeFlow(flow, options = {}) {
  if (!flow || typeof flow !== 'object') {
    throw new Error('Flow definition is required');
  }

  const state = {
    outputs: Object.create(null),
    steps: [],
    envelope: null,
  };

  const nodes = deriveExecutionPlan(flow);
  for (const node of nodes) {
    const inputNames = normalizeNameList(node?.input, []);
    const inputs = inputNames.map((name) => {
      if (!(name in state.outputs)) {
        throw new Error(
          `Flow node "${node?.id ?? 'unknown'}" requires input "${name}" that has not been produced yet`,
        );
      }
      return state.outputs[name];
    });
    const { outputs, info } = simulateNode(node, flow, inputs, options, state);
    Object.entries(outputs).forEach(([name, value]) => {
      state.outputs[name] = value;
    });
    state.steps.push({
      nodeId: node?.id ?? 'unknown',
      kind: node?.kind ?? 'unknown',
      outputs: Object.keys(outputs),
      info,
    });
  }

  return {
    flow,
    envelope: state.envelope,
    outputs: state.outputs,
    steps: state.steps,
  };
}

const ARG_PREFIX = '--';

function printUsage() {
  console.log(`
Usage:
  node scripts/agent-builder/flow-runner.mjs --flow <path> [options]

Options:
  --flow <path>     Flow JSON path (required)
  --summary <path>  Verify-lite summary JSON path (optional)
  --output <path>   Output path for generated envelope JSON (optional)
  --adapter <name>  Flow adapter (agent-builder)
  --schema <path>   Flow schema path (default: schema/flow.schema.json)
  --runId <id>      Trace correlation run id override (optional)
  --workflow <name> Trace correlation workflow name override (optional)
  --commit <sha>    Trace correlation commit override (optional)
  --branch <name>   Trace correlation branch override (optional)
  --tempoLinkTemplate <url> Tempo link template (e.g. https://tempo/{traceId})
  --note <text>     Attach a note to the envelope (repeatable)
  --help, -h        Show this help
`);
}

function parseArgs(argv) {
  const args = {
    flow: null,
    summary: null,
    output: null,
    adapter: null,
    schema: DEFAULT_FLOW_SCHEMA,
    runId: null,
    workflow: null,
    commit: null,
    branch: null,
    tempoLinkTemplate: null,
    notes: [],
    help: false,
  };
  const tokens = argv.slice(2);
  const consumed = new Set();
  for (let i = 0; i < tokens.length; i += 1) {
    if (consumed.has(i)) continue;
    const token = tokens[i];
    if (token === '-h') {
      args.help = true;
      continue;
    }
    if (!token.startsWith(ARG_PREFIX)) continue;
    const key = token.slice(ARG_PREFIX.length);
    const nextIndex = i + 1;
    const value = tokens[nextIndex];
    if (key === 'note') {
      if (value && !value.startsWith(ARG_PREFIX)) {
        args.notes.push(value);
        consumed.add(nextIndex);
      } else {
        throw new Error('Missing value for --note flag');
      }
      continue;
    }
    if (value && !value.startsWith(ARG_PREFIX)) {
      if (key in args) {
        args[key] = value;
      }
      consumed.add(nextIndex);
    } else if (key in args) {
      args[key] = true;
    }
  }
  return args;
}

export async function main(argv = process.argv) {
  const args = parseArgs(argv);
  if (args.help) {
    printUsage();
    process.exit(0);
  }
  const flowPath = args.flow;
  if (!flowPath) {
    console.error('[agent-builder] --flow <path> is required');
    printUsage();
    process.exit(1);
  }

  let verifyLiteSummary = null;
  if (args.summary) {
    verifyLiteSummary = readJson(args.summary);
  }

  let correlation = null;
  if (args.runId || args.workflow || args.commit || args.branch) {
    correlation = {
      ...(args.runId ? { runId: args.runId } : {}),
      ...(args.workflow ? { workflow: args.workflow } : {}),
      ...(args.commit ? { commit: args.commit } : {}),
      ...(args.branch ? { branch: args.branch } : {}),
    };
  }

  const adapter = resolveAdapter(args.adapter);
  const { flow } = loadFlowDefinition(flowPath, { schemaPath: args.schema, adapter });
  const result = executeFlow(flow, {
    verifyLiteSummary,
    correlation,
    ...(args.tempoLinkTemplate ? { tempoLinkTemplate: args.tempoLinkTemplate } : {}),
    ...(args.notes.length > 0 ? { notes: args.notes } : {}),
  });

  if (args.output && result.envelope) {
    const resolvedOutput = path.resolve(args.output);
    fs.mkdirSync(path.dirname(resolvedOutput), { recursive: true });
    fs.writeFileSync(resolvedOutput, JSON.stringify(result.envelope, null, 2));
    console.log(`[agent-builder] envelope written to ${resolvedOutput}`);
  }

  console.log(
    JSON.stringify(
      {
        flow: flow?.metadata ?? {},
        steps: result.steps.map((step) => ({
          nodeId: step.nodeId,
          kind: step.kind,
          info: step.info,
        })),
        hasEnvelope: Boolean(result.envelope),
      },
      null,
      2,
    ),
  );
}

function isInvokedDirectly() {
  try {
    const entry = process.argv[1];
    if (!entry) return false;
    return path.resolve(entry) === fileURLToPath(import.meta.url);
  } catch {
    return false;
  }
}

if (isInvokedDirectly()) {
  main().catch((error) => {
    console.error('[agent-builder] execution failed:', error);
    if (error?.validationErrors) {
      console.error(JSON.stringify(error.validationErrors, null, 2));
    }
    process.exit(1);
  });
}
