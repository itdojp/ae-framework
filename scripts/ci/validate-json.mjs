#!/usr/bin/env node
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..', '..');

const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);

function loadJson(relativePath) {
  const resolved = path.resolve(repoRoot, relativePath);
  return JSON.parse(readFileSync(resolved, 'utf8'));
}

function validateSchema(schemaPath, fixturePaths) {
  const schema = loadJson(schemaPath);
  const validate = ajv.compile(schema);
  const failures = [];
  for (const fixture of fixturePaths) {
    const data = loadJson(fixture);
    const ok = validate(data);
    if (!ok) {
      failures.push({ fixture, errors: validate.errors ?? [] });
    }
  }
  return failures;
}

const checks = [
  {
    schema: 'schema/envelope.schema.json',
    fixtures: ['fixtures/envelope/sample.envelope.json'],
    label: 'Envelope schema validation'
  },
  {
    schema: 'schema/flow.schema.json',
    fixtures: ['fixtures/flow/sample.flow.json'],
    label: 'Flow schema validation'
  },
  {
    schema: 'schema/context-bundle.schema.json',
    fixtures: ['fixtures/context-bundle/sample.context-bundle.json'],
    label: 'Context Bundle schema validation'
  },
  {
    schema: 'schema/execplan.schema.json',
    fixtures: ['fixtures/execplan/sample.execplan.json'],
    label: 'ExecPlan schema validation'
  }
];

let hasFailures = false;
for (const check of checks) {
  const failures = validateSchema(check.schema, check.fixtures);
  if (failures.length === 0) {
    console.log(`${check.label}: OK`);
  } else {
    hasFailures = true;
    console.error(`${check.label}: FAILED`);
    for (const failure of failures) {
      console.error(`- fixture: ${failure.fixture}`);
      console.error(JSON.stringify(failure.errors, null, 2));
    }
  }
}

if (hasFailures) {
  process.exitCode = 1;
}
