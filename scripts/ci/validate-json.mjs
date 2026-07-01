#!/usr/bin/env node
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import yaml from 'yaml';
import { runSchemaIdPolicyCheck } from './check-schema-id-policy.mjs';
import { validateAgenticMetricsSemantics } from './lib/agentic-metrics-contract.mjs';
import { validateClaimEvidenceManifestSemantics } from './lib/claim-evidence-manifest-contract.mjs';
import {
  validateSecurityAuditTaskBundleSemantics,
  validateSecurityAuditPromptPackSemantics,
  validateSecurityCodeMapSemantics,
  validateSecurityEntrypointMapSemantics,
  validateSecurityFindingSemantics,
  validateSecurityReviewSemantics,
  validateSymbolIndexSemantics,
} from './lib/security-assurance-contract.mjs';

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

function validateSchema(schemaPath, fixturePaths, semanticValidate = null) {
  const schema = loadJson(schemaPath);
  const validate = ajv.compile(schema);
  const failures = [];
  for (const fixture of fixturePaths) {
    const data = loadFixture(fixture);
    const ok = validate(data);
    if (!ok) {
      failures.push({ fixture, errors: validate.errors ?? [] });
      continue;
    }
    if (typeof semanticValidate === 'function') {
      const semanticErrors = semanticValidate(data);
      if (semanticErrors.length > 0) {
        failures.push({ fixture, errors: semanticErrors });
      }
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
    schema: 'schema/discovery-pack-v1.schema.json',
    fixtures: [
      'fixtures/discovery-pack/minimal.yaml',
      'fixtures/discovery-pack/rdra-lite-sample.yaml',
    ],
    label: 'Discovery Pack v1 schema validation'
  },
  {
    schema: 'schema/context-pack-v1.schema.json',
    fixtures: [
      'fixtures/context-pack/sample.context-pack.json',
      'fixtures/context-pack/sample.context-pack.discovery-upstream.json',
      'fixtures/spec-kit/greenfield/expected/context-pack.import.json',
      'fixtures/spec-kit/brownfield/expected/context-pack.import.json',
    ],
    label: 'Context Pack v1 schema validation'
  },
  {
    schema: 'schema/assurance-profile.schema.json',
    fixtures: [
      'fixtures/assurance/sample.assurance-profile.json',
      'fixtures/security-assurance/cache-key/inputs/assurance-profile.json',
      'spec/assurance-profile/upstream-context-promotion-v1.json',
    ],
    label: 'Assurance profile schema validation'
  },
  {
    schema: 'schema/assurance-summary.schema.json',
    fixtures: [
      'fixtures/assurance/sample.assurance-summary.json',
      'fixtures/assurance-e2e/inventory-waiver/expected/assurance-summary.json',
      'fixtures/security-assurance/cache-key/expected/assurance-summary.json',
    ],
    label: 'Assurance summary schema validation'
  },
  {
    schema: 'schema/verify-lite-run-summary.schema.json',
    fixtures: [
      'fixtures/assurance-e2e/inventory-waiver/expected/verify-lite-run-summary.json',
    ],
    label: 'Verify lite run summary schema validation'
  },
  {
    schema: 'schema/claim-evidence-manifest.schema.json',
    fixtures: [
      'fixtures/assurance/sample.claim-evidence-manifest.json',
      'fixtures/assurance-e2e/inventory-waiver/expected/claim-evidence-manifest.json',
      'fixtures/security-assurance/cache-key/expected/claim-evidence-manifest.json',
      'fixtures/assurance/claim-level-summary/inputs/claim-evidence-manifest.json',
    ],
    label: 'Claim evidence manifest schema validation',
    semanticValidate: validateClaimEvidenceManifestSemantics
  },
  {
    schema: 'schema/claim-level-summary-v1.schema.json',
    fixtures: [
      'fixtures/assurance/sample.claim-level-summary-v1.json',
      'fixtures/assurance/claim-level-summary/expected/claim-level-summary.json',
    ],
    label: 'Claim level summary v1 schema validation'
  },
  {
    schema: 'schema/temporary-override-v1.schema.json',
    fixtures: [
      'fixtures/assurance/sample.temporary-override-v1.json',
      'fixtures/assurance/claim-level-summary/inputs/temporary-overrides/override-manual-waiver-2026-06.json',
    ],
    label: 'Temporary override v1 schema validation'
  },
  {
    schema: 'schema/security-claim-v1.schema.json',
    fixtures: [
      'fixtures/security-assurance/sample.security-claims.json',
      'fixtures/security-assurance/cache-key/expected/security-claims.json',
    ],
    label: 'Security claim v1 schema validation'
  },
  {
    schema: 'schema/security-threat-model-v1.schema.json',
    fixtures: [
      'fixtures/security-assurance/sample.security-threat-model.json',
      'fixtures/security-assurance/cache-key/expected/security-threat-model.json',
    ],
    label: 'Security threat model v1 schema validation'
  },
  {
    schema: 'schema/security-audit-scope-v1.schema.json',
    fixtures: [
      'fixtures/security-assurance/sample.security-audit-scope.json',
      'fixtures/security-assurance/cache-key/expected/security-audit-scope.json',
    ],
    label: 'Security audit scope v1 schema validation'
  },
  {
    schema: 'schema/security-code-map-v1.schema.json',
    fixtures: [
      'fixtures/security-assurance/sample.security-code-map.json',
      'fixtures/security-assurance/cache-key/expected/security-code-map.json',
    ],
    label: 'Security code map v1 schema validation',
    semanticValidate: validateSecurityCodeMapSemantics
  },
  {
    schema: 'schema/symbol-index-v1.schema.json',
    fixtures: [
      'fixtures/security-assurance/sample.symbol-index.json',
    ],
    label: 'Symbol index v1 schema validation',
    semanticValidate: validateSymbolIndexSemantics
  },
  {
    schema: 'schema/security-entrypoint-map-v1.schema.json',
    fixtures: [
      'fixtures/security-assurance/sample.security-entrypoint-map.json',
    ],
    label: 'Security entrypoint map v1 schema validation',
    semanticValidate: validateSecurityEntrypointMapSemantics
  },
  {
    schema: 'schema/security-audit-task-bundle-v1.schema.json',
    fixtures: [
      'fixtures/security-assurance/sample.security-audit-tasks.json',
      'fixtures/security-assurance/cache-key/expected/security-audit-tasks.json',
    ],
    label: 'Security audit task bundle v1 schema validation',
    semanticValidate: validateSecurityAuditTaskBundleSemantics
  },
  {
    schema: 'schema/security-audit-prompt-pack-v1.schema.json',
    fixtures: [
      'fixtures/security-assurance/sample.security-audit-prompt-pack.json',
    ],
    label: 'Security audit prompt pack v1 schema validation',
    semanticValidate: validateSecurityAuditPromptPackSemantics
  },
  {
    schema: 'schema/security-finding-v1.schema.json',
    fixtures: [
      'fixtures/security-assurance/sample.security-findings.json',
      'fixtures/security-assurance/cache-key/expected/security-findings.json',
    ],
    label: 'Security finding v1 schema validation',
    semanticValidate: validateSecurityFindingSemantics
  },
  {
    schema: 'schema/security-review-v1.schema.json',
    fixtures: [
      'fixtures/security-assurance/sample.security-review.json',
      'fixtures/security-assurance/cache-key/expected/security-review.json',
    ],
    label: 'Security review v1 schema validation',
    semanticValidate: validateSecurityReviewSemantics
  },
  {
    schema: 'schema/temporal-run-summary.schema.json',
    fixtures: ['fixtures/temporal/sample.temporal-run-summary.json'],
    label: 'Temporal run summary schema validation'
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
    schema: 'schema/context-pack-boundary-map.schema.json',
    fixtures: ['fixtures/context-pack/sample.boundary-map.json'],
    label: 'Context Pack boundary map schema validation'
  },
  {
    schema: 'schema/context-pack-boundary-map-summary.schema.json',
    fixtures: ['fixtures/context-pack/sample.boundary-map-summary.json'],
    label: 'Context Pack boundary map summary schema validation'
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
    schema: 'schema/exec-plan.v2.schema.json',
    fixtures: [
      'fixtures/exec-plan/baseline.exec-plan.v2.json',
      'fixtures/exec-plan/structured-assurance.exec-plan.v2.json',
      'fixtures/exec-plan/high-risk-selected-claims.exec-plan.v2.json',
      'fixtures/spec-kit/greenfield/expected/exec-plan.v2.json',
      'fixtures/spec-kit/brownfield/expected/exec-plan.v2.json',
    ],
    label: 'ExecPlan v2 schema validation'
  },
  {
    schema: 'schema/spec-kit-bridge-report.schema.json',
    fixtures: [
      'fixtures/spec-kit/greenfield/expected/spec-kit-bridge-report.json',
      'fixtures/spec-kit/brownfield/expected/spec-kit-bridge-report.json',
    ],
    label: 'Spec Kit bridge report schema validation'
  },
  {
    schema: 'schema/loop-run-input.schema.json',
    fixtures: [
      'examples/loop-engineering/success/loop-input.json',
      'examples/loop-engineering/blocked/loop-input.json',
      'examples/loop-engineering/safety/loop-input.json',
    ],
    label: 'Loop run input schema validation'
  },
  {
    schema: 'schema/loop-policy.schema.json',
    fixtures: [
      'fixtures/loop/report-only-default.loop-policy.json',
      'fixtures/loop/strict-safety.loop-policy.json',
    ],
    label: 'Loop policy schema validation'
  },
  {
    schema: 'schema/loop-run-summary.schema.json',
    fixtures: [
      'fixtures/loop/success.loop-run-summary.json',
      'fixtures/loop/blocked.loop-run-summary.json',
      'fixtures/loop/safety-budget.loop-run-summary.json',
    ],
    label: 'Loop run summary schema validation'
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
    fixtures: [
      'fixtures/policy/sample.policy-input-v1.json',
      'fixtures/assurance-e2e/inventory-waiver/expected/policy-input-v1.json',
    ],
    label: 'Policy input v1 schema validation'
  },
  {
    schema: 'schema/policy-decision-v1.schema.json',
    fixtures: [
      'fixtures/policy/sample.policy-decision-v1.json',
      'fixtures/assurance-e2e/inventory-waiver/expected/policy-decision-js-v1.json',
    ],
    label: 'Policy decision v1 schema validation'
  },
  {
    schema: 'schema/ci-artifact-provenance-v1.schema.json',
    fixtures: ['fixtures/ci/sample.ci-artifact-provenance-v1.json'],
    label: 'CI artifact provenance v1 schema validation'
  },
  {
    schema: 'schema/counterexample.schema.json',
    fixtures: ['fixtures/counterexample/sample.counterexample.json'],
    label: 'Counterexample schema validation'
  },
  {
    schema: 'schema/agentic-metrics.schema.json',
    fixtures: [
      'fixtures/agentic-metrics/sample.agentic-metrics.json',
      'fixtures/agentic-metrics/agent-pr-assurance-metrics.example.json',
      'fixtures/metrics/agent-pr-assurance/expected.agent-pr-assurance-metrics.json',
    ],
    label: 'Agentic metrics schema validation',
    semanticValidate: validateAgenticMetricsSemantics
  },
  {
    schema: 'schema/req2run-metrics.schema.json',
    fixtures: ['fixtures/metrics/req2run/expected.req2run-metrics.json'],
    label: 'Req2run metrics schema validation'
  },
  {
    schema: 'schema/domain-assurance-preset.schema.json',
    fixtures: [
      'templates/domain-presets/web-api-bff/preset.json',
      'templates/domain-presets/event-driven-domain/preset.json',
      'templates/domain-presets/spec-led-brownfield/preset.json',
      'templates/domain-presets/high-assurance-critical-core/preset.json',
    ],
    label: 'Domain assurance preset schema validation'
  },
  {
    schema: 'schema/domain-assurance-preset-report.schema.json',
    fixtures: [
      'fixtures/domain-presets/web-api-bff/expected/domain-preset-report.json',
      'fixtures/domain-presets/event-driven-domain/expected/domain-preset-report.json',
    ],
    label: 'Domain assurance preset report schema validation'
  },
  {
    schema: 'schema/completion-audit-report.schema.json',
    fixtures: ['fixtures/audit/completion/expected/completion-audit-report.json'],
    label: 'Completion audit report schema validation'
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
    schema: 'schema/quality-scorecard.schema.json',
    fixtures: ['fixtures/quality/sample.quality-scorecard.json'],
    label: 'Quality scorecard schema validation'
  },
  {
    schema: 'schema/quality-baseline.schema.json',
    fixtures: ['fixtures/quality/sample.quality-baseline.json'],
    label: 'Quality baseline schema validation'
  },
  {
    schema: 'schema/variance-report.schema.json',
    fixtures: ['fixtures/variance/expected.drift.variance-report.json'],
    label: 'Variance report schema validation'
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
    fixtures: [
      'fixtures/change-package/sample.change-package-v2.json',
      'fixtures/assurance-e2e/inventory-waiver/inputs/change-package-v2.json',
      'fixtures/assurance/claim-level-summary/inputs/change-package-v2.json',
    ],
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
    schema: 'schema/hook-feedback.schema.json',
    fixtures: [
      'fixtures/agents/sample.hook-feedback.json',
      'fixtures/agents/sample.hook-feedback-partial.json',
    ],
    label: 'Hook feedback schema validation'
  },
  {
    schema: 'schema/producer-normalization-summary.schema.json',
    fixtures: [
      'fixtures/agents/producer-normalization-summary.codex.json',
      'fixtures/agents/producer-normalization-summary.ci.json',
      'fixtures/agents/producer-normalization-summary.formal.json',
    ],
    label: 'Producer normalization summary schema validation'
  },
  {
    schema: 'schema/harness-health.schema.json',
    fixtures: ['fixtures/ci/sample.harness-health.json'],
    label: 'Harness health schema validation'
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
    fixtures: [
      'fixtures/policy-gate/sample.policy-gate-summary-v1.json',
      'fixtures/assurance-e2e/inventory-waiver/expected/policy-gate-summary.json',
      'fixtures/assurance/claim-level-summary/inputs/policy-gate-summary.json',
    ],
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
  },
  {
    schema: 'schema/license-scope-audit.schema.json',
    fixtures: ['fixtures/legal/sample.license-scope-audit.json'],
    label: 'License scope audit schema validation'
  },
  {
    schema: 'schema/conditional-asset-audit.schema.json',
    fixtures: ['fixtures/legal/sample.conditional-asset-audit.json'],
    label: 'Conditional asset audit schema validation'
  },
  {
    schema: 'schema/notice-readiness-audit.schema.json',
    fixtures: ['fixtures/legal/sample.notice-readiness-audit.json'],
    label: 'Notice readiness audit schema validation'
  },
  {
    schema: 'schema/contributor-license-readiness-audit.schema.json',
    fixtures: ['fixtures/legal/sample.contributor-license-readiness-audit.json'],
    label: 'Contributor license readiness audit schema validation'
  },
  {
    schema: 'schema/third-party-notice-candidate-audit.schema.json',
    fixtures: ['fixtures/legal/sample.third-party-notice-candidate-audit.json'],
    label: 'Third-party notice candidate audit schema validation'
  },
  {
    schema: 'schema/apache-license-cutover-readiness-audit.schema.json',
    fixtures: ['fixtures/legal/sample.apache-license-cutover-readiness-audit.json'],
    label: 'Apache license cutover readiness audit schema validation'
  },
  {
    schema: 'schema/apache-license-cutover-approval-readiness-audit.schema.json',
    fixtures: ['fixtures/legal/sample.apache-license-cutover-approval-readiness-audit.json'],
    label: 'Apache license cutover approval readiness audit schema validation'
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
  const failures = validateSchema(check.schema, check.fixtures, check.semanticValidate);
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
