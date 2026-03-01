#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import Ajv2020 from 'ajv/dist/2020.js';

const rootDir = process.cwd();
const schemaPath = path.resolve(rootDir, 'schema/codex-task-response.schema.json');
const validExamplePaths = [
  path.resolve(rootDir, 'schema/examples/codex-task-response.unblocked.json'),
  path.resolve(rootDir, 'schema/examples/codex-task-response.blocked.json'),
];

function loadJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function formatErrors(errors = []) {
  return errors
    .map((entry) => `${entry.instancePath || '/'} ${entry.message || 'invalid value'}`.trim())
    .join('; ');
}

function assertValid(name, validate, payload) {
  if (!validate(payload)) {
    throw new Error(`${name} should be valid, but failed: ${formatErrors(validate.errors)}`);
  }
}

function assertInvalid(name, validate, payload) {
  const ok = validate(payload);
  if (ok) {
    throw new Error(`${name} should be invalid, but passed`);
  }
}

function main() {
  const ajv = new Ajv2020({
    allErrors: true,
    strict: false,
  });
  const schema = loadJson(schemaPath);
  const validate = ajv.compile(schema);

  const validExamples = validExamplePaths.map((filePath) => ({
    name: path.relative(rootDir, filePath),
    payload: loadJson(filePath),
  }));

  for (const example of validExamples) {
    assertValid(example.name, validate, example.payload);
  }

  const blockedBase = loadJson(path.resolve(rootDir, 'schema/examples/codex-task-response.blocked.json'));
  const unblockedBase = loadJson(path.resolve(rootDir, 'schema/examples/codex-task-response.unblocked.json'));

  const invalidCases = [
    {
      name: 'unblocked-nextActions-empty',
      payload: { ...unblockedBase, nextActions: [] },
    },
    {
      name: 'unblocked-nextActions-empty-string',
      payload: { ...unblockedBase, nextActions: [''] },
    },
    {
      name: 'blocked-nextActions-empty',
      payload: { ...blockedBase, nextActions: [] },
    },
    {
      name: 'blocked-warnings-empty',
      payload: { ...blockedBase, warnings: [] },
    },
    {
      name: 'blocked-warnings-empty-string',
      payload: { ...blockedBase, warnings: [''] },
    },
  ];

  for (const sample of invalidCases) {
    assertInvalid(sample.name, validate, sample.payload);
  }

  console.log('Codex TaskResponse schema validation: OK');
  console.log(`- schema: ${path.relative(rootDir, schemaPath)}`);
  console.log(`- valid examples: ${validExamples.length}`);
  console.log(`- invalid cases: ${invalidCases.length}`);
}

try {
  main();
} catch (error) {
  const message = error instanceof Error ? error.message : String(error);
  console.error(`Codex TaskResponse schema validation: FAILED\n${message}`);
  process.exit(1);
}
