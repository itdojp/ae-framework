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

export function loadFlowDefinition(flowPath, { schemaPath = DEFAULT_FLOW_SCHEMA, validate = true } = {}) {
  const resolvedFlow = path.resolve(flowPath);
  if (!fs.existsSync(resolvedFlow)) {
    throw new Error(`Flow definition not found: ${resolvedFlow}`);
  }

  const data = readJson(resolvedFlow);

  if (validate) {
    const validateFn = getValidator(schemaPath);
    const ok = validateFn(data);
    if (!ok) {
      const error = new Error('Flow definition failed schema validation');
      error.validationErrors = validateFn.errors ?? [];
      throw error;
    }
  }

  return {
    flow: data,
    path: resolvedFlow,
  };
}

function normalizeNameList(value, fallback) {
  if (Array.isArray(value) && value.length > 0) {
    return value;
  }
  return Array.isArray(fallback) && fallback.length > 0 ? fallback : [];
}

function buildCorrelation(flow, options) {
  const provided = options.correlation ?? {};
  const name = flow?.metadata?.name ?? 'agent-builder-flow';
  return {
    runId: provided.runId ?? `flow-${name}`,
    workflow: provided.workflow ?? name,
    commit: provided.commit ?? process.env.GITHUB_SHA ?? 'local',
    branch: provided.branch ?? process.env.GITHUB_REF ?? 'local',
    ...(provided.traceIds ? { traceIds: provided.traceIds } : {}),
  };
}

function simulateNode(node, flow, inputs, options, state) {
  const params = node?.params ?? {};
  const outputNames = normalizeNameList(node?.output, [node.id]);
  const outputs = {};
  const info = {};

  switch (node?.kind) {
    case 'intent2formal': {
      const spec = {
        id: node.id,
        language: params.language ?? 'en',
        description: `Formal specification seeded for flow "${flow?.metadata?.name ?? node.id}"`,
        generatedAt: options.generatedAt ?? new Date().toISOString(),
      };
      outputs[outputNames[0]] = spec;
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
      outputs[outputNames[0]] = code;
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
      outputs[outputNames[0]] = result;
      if (envelope) {
        state.envelope = envelope;
      }
      info.type = 'verification';
      info.envelope = Boolean(envelope);
      break;
    }
    default: {
      outputs[outputNames[0]] = {
        kind: node?.kind ?? 'unknown',
        params,
        inputs,
      };
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

  const nodes = Array.isArray(flow.nodes) ? flow.nodes : [];
  for (const node of nodes) {
    const inputs = normalizeNameList(node?.input, []).map((name) => state.outputs[name]);
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

function parseArgs(argv) {
  const args = {
    flow: null,
    summary: null,
    output: null,
    schema: DEFAULT_FLOW_SCHEMA,
    runId: null,
    workflow: null,
    commit: null,
    branch: null,
  };
  const tokens = argv.slice(2);
  const consumed = new Set();
  for (let i = 0; i < tokens.length; i += 1) {
    if (consumed.has(i)) continue;
    const token = tokens[i];
    if (!token.startsWith(ARG_PREFIX)) continue;
    const key = token.slice(ARG_PREFIX.length);
    const nextIndex = i + 1;
    const value = tokens[nextIndex];
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
  const flowPath = args.flow;
  if (!flowPath) {
    console.error('[agent-builder] --flow <path> is required');
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

  const { flow } = loadFlowDefinition(flowPath, { schemaPath: args.schema });
  const result = executeFlow(flow, {
    verifyLiteSummary,
    correlation,
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
