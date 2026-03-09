#!/usr/bin/env node
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import yaml from 'yaml';
import { runSchemaIdPolicyCheck } from './check-schema-id-policy.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..', '..');

const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);

function loadJson(relativePath) {
  const resolved = path.resolve(repoRoot, relativePath);
  return JSON.parse(readFileSync(resolved, 'utf8'));
}

function loadFixture(relativePath) {
  const resolved = path.resolve(repoRoot, relativePath);
  const raw = readFileSync(resolved, 'utf8');
  const extension = path.extname(relativePath).toLowerCase();
  if (extension === '.yaml' || extension === '.yml') {
    return yaml.parse(raw);
  }
  return JSON.parse(raw);
}

function validateSchema(schemaPath, fixturePaths) {
  const schema = loadJson(schemaPath);
  const validate = ajv.compile(schema);
  const failures = [];
  for (const fixture of fixturePaths) {
    const data = loadFixture(fixture);
    const ok = validate(data);
    if (!ok) {
      failures.push({ fixture, errors: validate.errors ?? [] });
    }
  }
  return failures;
}

function preloadSharedSchemas() {
  const sharedSchemas = [
    'schema/artifact-metadata.schema.json',
  ];
  for (const schemaPath of sharedSchemas) {
    const schema = loadJson(schemaPath);
    ajv.addSchema(schema);
  }
}

preloadSharedSchemas();

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
    schema: 'schema/assurance-profile.schema.json',
    fixtures: ['fixtures/assurance/sample.assurance-profile.json'],
    label: 'Assurance profile schema validation'
  },
  {
    schema: 'schema/assurance-summary.schema.json',
    fixtures: ['fixtures/assurance/sample.assurance-summary.json'],
    label: 'Assurance summary schema validation'
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
    schema: 'schema/context-pack-product-coproduct.schema.json',
    fixtures: ['fixtures/context-pack/sample.product-coproduct-map.json'],
    label: 'Context Pack product/coproduct schema validation'
  },
  {
    schema: 'schema/context-pack-phase5-templates.schema.json',
    fixtures: ['fixtures/context-pack/sample.phase5-templates.json'],
    label: 'Context Pack phase5 templates schema validation'
  },
  {
    schema: 'schema/context-pack-suggestions.schema.json',
    fixtures: ['fixtures/context-pack/sample.context-pack-suggestions.json'],
    label: 'Context Pack suggestions schema validation'
  },
  {
    schema: 'schema/execplan.schema.json',
    fixtures: ['fixtures/execplan/sample.execplan.json'],
    label: 'ExecPlan schema validation'
  },
  {
    schema: 'schema/pr-state-v1.schema.json',
    fixtures: [
      'fixtures/pr-state/sample.pr-state.blocked.json',
      'fixtures/pr-state/sample.pr-state.merge-eligible.json'
    ],
    label: 'PR state v1 schema validation'
  },
  {
    schema: 'schema/execution-plan-v1.schema.json',
    fixtures: ['fixtures/execution-plan/sample.execution-plan.autopilot.json'],
    label: 'Execution plan v1 schema validation'
  },
  {
    schema: 'schema/policy-input-v1.schema.json',
    fixtures: ['fixtures/policy/sample.policy-input-v1.json'],
    label: 'Policy input v1 schema validation'
  },
  {
    schema: 'schema/policy-decision-v1.schema.json',
    fixtures: ['fixtures/policy/sample.policy-decision-v1.json'],
    label: 'Policy decision v1 schema validation'
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
  },
  {
    schema: 'schema/change-package.schema.json',
    fixtures: ['fixtures/change-package/sample.change-package.json'],
    label: 'Change Package schema validation'
  },
  {
    schema: 'schema/change-package-v2.schema.json',
    fixtures: ['fixtures/change-package/sample.change-package-v2.json'],
    label: 'Change Package v2 schema validation'
  },
  {
    schema: 'schema/ae-handoff.schema.json',
    fixtures: ['fixtures/agents/sample.ae-handoff.json'],
    label: 'AE-HANDOFF schema validation'
  },
  {
    schema: 'schema/ui-e2e-summary.schema.json',
    fixtures: ['fixtures/e2e/sample.ui-e2e-summary.json'],
    label: 'UI E2E summary schema validation'
  },
  {
    schema: 'schema/plan-artifact.schema.json',
    fixtures: ['fixtures/plan/sample.plan-artifact.json'],
    label: 'Plan Artifact schema validation'
  },
  {
    schema: 'schema/release-policy.schema.json',
    fixtures: ['fixtures/release/sample.release-policy.json', 'policy/release-policy.yml'],
    label: 'Release policy schema validation'
  },
  {
    schema: 'schema/policy-gate-summary-v1.schema.json',
    fixtures: ['fixtures/policy-gate/sample.policy-gate-summary-v1.json'],
    label: 'Policy gate summary v1 schema validation'
  },
  {
    schema: 'schema/automation-observability-v1.schema.json',
    fixtures: ['fixtures/automation/sample.automation-observability-v1.json'],
    label: 'Automation report v1 schema validation'
  },
  {
    schema: 'schema/formal-summary-v2.schema.json',
    fixtures: ['fixtures/formal/sample.formal-summary-v2.json'],
    label: 'Formal summary v2 schema validation'
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
