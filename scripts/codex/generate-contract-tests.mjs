#!/usr/bin/env node
// Generate Vitest contract/E2E test templates from an OpenAPI spec.
// - Default mode creates skipped test templates (safe for CI)
// - Writes a machine-readable summary to artifacts/codex/openapi-contract-tests.json

import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import yaml from 'yaml';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

function parseArgs(argv) {
  const args = { outDir: 'tests/api/generated', mode: 'templates' };
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--openapi') args.openapi = argv[++i];
    else if (a === '--outDir') args.outDir = argv[++i];
    else if (a === '--mode') args.mode = argv[++i];
  }
  if (!args.openapi) throw new Error('Missing --openapi <path/to/openapi.yaml>');
  return args;
}

function ensureDir(p) {
  fs.mkdirSync(p, { recursive: true });
}

function readOpenAPI(p) {
  const raw = fs.readFileSync(p, 'utf8');
  const doc = /\.(ya?ml)$/i.test(p) ? yaml.parse(raw) : JSON.parse(raw);
  if (!doc || !doc.paths || typeof doc.paths !== 'object') {
    throw new Error('Invalid OpenAPI: missing paths');
  }
  return doc;
}

function sanitize(name) {
  return name.replace(/[^a-zA-Z0-9_-]+/g, '_');
}

function inferOperationId(pathKey, method, op) {
  return op.operationId || `${method}_${pathKey}`.replace(/[^a-zA-Z0-9]+/g, '_');
}

function genTestTemplate({ operationId, method, pathKey, summary, hasRequestBody, hasResponses }) {
  const title = summary ? `${operationId} - ${summary}` : operationId;
  // Use skipped tests to avoid failing CI until developers implement them.
  return `import { describe, it, expect } from 'vitest';

describe('${title}', () => {
  it.skip('contract: request/response schema validation', async () => {
    // TODO: Implement contract validation against OpenAPI schemas
    // - Validate request shape${hasRequestBody ? ' (requestBody is defined)' : ''}
    // - Validate response shape${hasResponses ? ' (responses are defined)' : ''}
    // Suggested approach: use Ajv with JSON Schema or zod adapters.
    expect(true).toBe(true);
  });

  it.skip('e2e: endpoint behavior (integration)', async () => {
    // TODO: Implement E2E/integration test
    // - Start app/server
    // - Perform ${method.toUpperCase()} ${pathKey}
    // - Assert status code and payload
    expect(true).toBe(true);
  });
});
`;
}

function writeSummary(summary) {
  const root = process.cwd();
  const outDir = path.join(root, 'artifacts', 'codex');
  ensureDir(outDir);
  const p = path.join(outDir, 'openapi-contract-tests.json');
  fs.writeFileSync(p, JSON.stringify(summary, null, 2), 'utf8');
  return p;
}

async function main() {
  const args = parseArgs(process.argv);
  const root = process.cwd();
  const specPath = path.resolve(args.openapi);
  const outDir = path.resolve(args.outDir);

  const oas = readOpenAPI(specPath);
  ensureDir(outDir);

  let files = 0;
  const operations = [];
  for (const [pathKey, pathItem] of Object.entries(oas.paths)) {
    if (!pathItem || typeof pathItem !== 'object') continue;
    for (const method of ['get','post','put','patch','delete','options','head','trace']) {
      const op = pathItem[method];
      if (!op) continue;
      const operationId = inferOperationId(pathKey, method, op);
      const testName = sanitize(operationId) + '.test.ts';
      const hasRequestBody = !!op.requestBody;
      const hasResponses = !!op.responses && Object.keys(op.responses).length > 0;
      const content = genTestTemplate({ operationId, method, pathKey, summary: op.summary, hasRequestBody, hasResponses });
      const target = path.join(outDir, testName);
      fs.writeFileSync(target, content, 'utf8');
      files += 1;
      operations.push({ operationId, method, path: pathKey, file: path.relative(root, target) });
    }
  }

  const summary = {
    openapi: path.relative(root, specPath),
    outDir: path.relative(root, outDir),
    files, operations,
    mode: args.mode,
    ts: new Date().toISOString(),
  };
  const summaryPath = writeSummary(summary);
  console.log(`Generated ${files} contract/E2E test templates → ${path.relative(root, outDir)}`);
  console.log(`Summary: ${path.relative(root, summaryPath)}`);
}

main().catch(err => {
  console.error('[codex] generate-contract-tests failed:', err);
  process.exit(1);
});

