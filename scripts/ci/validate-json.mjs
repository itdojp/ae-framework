#!/usr/bin/env node
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { runSchemaIdPolicyCheck } from './check-schema-id-policy.mjs';

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
    schema: 'schema/context-pack-v1.schema.json',
    fixtures: ['fixtures/context-pack/sample.context-pack.json'],
    label: 'Context Pack v1 schema validation'
  },
  {
    schema: 'schema/context-pack-functor-map.schema.json',
    fixtures: ['fixtures/context-pack/sample.functor-map.json'],
    label: 'Context Pack functor map schema validation'
  },
  {
    schema: 'schema/context-pack-natural-transformation.schema.json',
    fixtures: ['fixtures/context-pack/sample.natural-transformations.json'],
    label: 'Context Pack natural transformation schema validation'
  },
  {
    schema: 'schema/execplan.schema.json',
    fixtures: ['fixtures/execplan/sample.execplan.json'],
    label: 'ExecPlan schema validation'
  },
  {
    schema: 'schema/counterexample.schema.json',
    fixtures: ['fixtures/counterexample/sample.counterexample.json'],
    label: 'Counterexample schema validation'
  },
  {
    schema: 'schema/agentic-metrics.schema.json',
    fixtures: ['fixtures/agentic-metrics/sample.agentic-metrics.json'],
    label: 'Agentic metrics schema validation'
  },
  {
    schema: 'schema/formal-plan.schema.json',
    fixtures: ['fixtures/formal-plan/sample.formal-plan.json'],
    label: 'Formal plan schema validation'
  },
  {
    schema: 'schema/trace-map.schema.json',
    fixtures: ['fixtures/trace-map/sample.trace-map.json'],
    label: 'Trace map schema validation'
  },
  {
    schema: 'schema/quality-report.schema.json',
    fixtures: ['fixtures/quality-report/sample.quality-report.json'],
    label: 'Quality report schema validation'
  },
  {
    schema: 'schema/conformance-verify-result.schema.json',
    fixtures: ['fixtures/conformance/sample.conformance-verify-result.json'],
    label: 'Conformance verify result schema validation'
  },
  {
    schema: 'schema/conformance-metrics.schema.json',
    fixtures: ['fixtures/conformance/sample.conformance-metrics.json'],
    label: 'Conformance metrics schema validation'
  },
  {
    schema: 'schema/conformance-report.schema.json',
    fixtures: ['fixtures/conformance/sample.conformance-report.json'],
    label: 'Conformance report schema validation'
  }
];

let hasFailures = false;

const schemaIdPolicyCheck = runSchemaIdPolicyCheck([
  'node',
  'check-schema-id-policy.mjs',
  `--root=${repoRoot}`,
]);
if (schemaIdPolicyCheck.exitCode !== 0) {
  hasFailures = true;
}

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
