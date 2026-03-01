#!/usr/bin/env node
// CodeX stdio adapter: JSON-in/JSON-out bridge to CodeX Task Adapter
// Usage:
//   echo '{"description":"Generate UI","subagent_type":"ui","context":{}}' | node scripts/codex/adapter-stdio.mjs

import fs from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';

const EXIT_CODES = Object.freeze({
  SUCCESS: 0,
  BLOCKED: 2,
  INVALID_INPUT: 3,
  INTERNAL_ERROR: 1,
});

function readAllStdin() {
  return new Promise((resolve, reject) => {
    let data = '';
    process.stdin.setEncoding('utf8');
    process.stdin.on('data', (chunk) => {
      data += chunk;
    });
    process.stdin.on('end', () => resolve(data));
    process.stdin.on('error', reject);
  });
}

function writeJSON(obj) {
  process.stdout.write(`${JSON.stringify(obj)}\n`);
}

function writeError({ code, message, details, exitCode }) {
  writeJSON({
    error: true,
    code,
    message,
    details: details ?? null,
    ts: new Date().toISOString(),
  });
  process.exitCode = exitCode;
}

function formatValidationErrors(errors = []) {
  return errors.map((entry) => ({
    path: entry.instancePath || '/',
    message: entry.message || 'invalid value',
    keyword: entry.keyword,
    params: entry.params,
  }));
}

function loadJsonSchema(schemaPath) {
  const content = fs.readFileSync(schemaPath, 'utf8');
  return JSON.parse(content);
}

function resolveSchemaPath(envKey, fallback) {
  const fromEnv = process.env[envKey];
  if (fromEnv && fromEnv.trim()) {
    return path.resolve(fromEnv.trim());
  }
  return path.resolve(fallback);
}

function buildValidators() {
  const requestSchemaPath = resolveSchemaPath('CODEX_TASK_REQUEST_SCHEMA', 'schema/codex-task-request.schema.json');
  const responseSchemaPath = resolveSchemaPath('CODEX_TASK_RESPONSE_SCHEMA', 'schema/codex-task-response.schema.json');

  const ajv = new Ajv2020({
    allErrors: true,
    strict: false,
  });

  const requestSchema = loadJsonSchema(requestSchemaPath);
  const responseSchema = loadJsonSchema(responseSchemaPath);

  return {
    requestSchemaPath,
    responseSchemaPath,
    validateRequest: ajv.compile(requestSchema),
    validateResponse: ajv.compile(responseSchema),
  };
}

function normalizeTaskRequest(request) {
  const description = typeof request.description === 'string' && request.description.length > 0
    ? request.description
    : request.prompt;
  const prompt = typeof request.prompt === 'string' && request.prompt.length > 0
    ? request.prompt
    : request.description;

  return {
    ...request,
    description,
    prompt,
  };
}

function normalizeBlockedWarnings(response) {
  if (!response || typeof response !== 'object' || response.shouldBlockProgress !== true) {
    return response;
  }

  const warnings = Array.isArray(response.warnings)
    ? response.warnings
      .filter((item) => typeof item === 'string')
      .map((item) => item.trim())
      .filter((item) => item.length > 0)
    : [];

  if (warnings.length > 0) {
    return {
      ...response,
      warnings,
    };
  }

  const requiredHumanInput = typeof response.requiredHumanInput === 'string'
    ? response.requiredHumanInput.trim()
    : '';
  const fallbackAction = Array.isArray(response.nextActions)
    ? response.nextActions.find((item) => typeof item === 'string' && item.trim().length > 0)?.trim()
    : '';
  const blockingReason = typeof response.blockingReason === 'string'
    ? response.blockingReason.trim()
    : '';
  const warningMessage = requiredHumanInput
    ? `Human action: provide ${requiredHumanInput}`
    : fallbackAction
      ? `Human action: ${fallbackAction}`
      : blockingReason
        ? `Human action: resolve ${blockingReason}`
        : 'Human action: provide required input and rerun codex task';

  return {
    ...response,
    warnings: [warningMessage],
  };
}

async function loadAdapter() {
  const candidates = [
    path.resolve('dist/src/agents/codex-task-adapter.js'),
    path.resolve('dist/agents/codex-task-adapter.js'),
  ];
  for (const candidate of candidates) {
    if (fs.existsSync(candidate)) {
      return await import(candidate);
    }
  }
  throw new Error('Adapter not found. Build first: pnpm run build');
}

async function main() {
  const raw = await readAllStdin();
  if (!raw.trim()) {
    writeError({
      code: 'EMPTY_STDIN',
      message: 'No input provided on stdin',
      exitCode: EXIT_CODES.INVALID_INPUT,
    });
    return;
  }

  let request;
  try {
    request = JSON.parse(raw);
  } catch (error) {
    writeError({
      code: 'INVALID_JSON',
      message: `Invalid JSON: ${error instanceof Error ? error.message : String(error)}`,
      exitCode: EXIT_CODES.INVALID_INPUT,
    });
    return;
  }

  let validators;
  try {
    validators = buildValidators();
  } catch (error) {
    writeError({
      code: 'SCHEMA_LOAD_FAILED',
      message: `Failed to load schema: ${error instanceof Error ? error.message : String(error)}`,
      exitCode: EXIT_CODES.INTERNAL_ERROR,
    });
    return;
  }

  if (!validators.validateRequest(request)) {
    writeError({
      code: 'INVALID_REQUEST_SCHEMA',
      message: 'Request does not match codex task request schema',
      details: {
        schema: path.relative(process.cwd(), validators.requestSchemaPath),
        errors: formatValidationErrors(validators.validateRequest.errors),
      },
      exitCode: EXIT_CODES.INVALID_INPUT,
    });
    return;
  }

  let response;
  try {
    const { createCodexTaskAdapter } = await loadAdapter();
    const adapter = createCodexTaskAdapter();
    response = await adapter.handleTask(normalizeTaskRequest(request));
    response = normalizeBlockedWarnings(response);
  } catch (error) {
    writeError({
      code: 'ADAPTER_ERROR',
      message: `Adapter error: ${error instanceof Error ? error.message : String(error)}`,
      exitCode: EXIT_CODES.INTERNAL_ERROR,
    });
    return;
  }

  if (!validators.validateResponse(response)) {
    writeError({
      code: 'INVALID_RESPONSE_SCHEMA',
      message: 'Adapter response does not match codex task response schema',
      details: {
        schema: path.relative(process.cwd(), validators.responseSchemaPath),
        errors: formatValidationErrors(validators.validateResponse.errors),
      },
      exitCode: EXIT_CODES.INTERNAL_ERROR,
    });
    return;
  }

  writeJSON(response);
  process.exitCode = response.shouldBlockProgress ? EXIT_CODES.BLOCKED : EXIT_CODES.SUCCESS;
}

main().catch((error) => {
  writeError({
    code: 'UNEXPECTED_ERROR',
    message: error instanceof Error ? error.message : String(error),
    exitCode: EXIT_CODES.INTERNAL_ERROR,
  });
});
