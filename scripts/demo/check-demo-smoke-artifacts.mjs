#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_OUTPUT_ROOT = 'artifacts';
const VERIFY_LITE_SCHEMA = 'schema/verify-lite-run-summary.schema.json';
const PRODUCER_SCHEMA = 'schema/producer-normalization-summary.schema.json';
const ASSURANCE_SCHEMA = 'schema/assurance-summary.schema.json';
const POLICY_SCHEMA = 'schema/policy-gate-summary-v1.schema.json';
const BOUNDARY_SUMMARY_SCHEMA = 'schema/context-pack-boundary-map-summary.schema.json';
const CLAIM_MANIFEST_SCHEMA = 'schema/claim-evidence-manifest.schema.json';
const PLAN_ARTIFACT_SCHEMA = 'schema/plan-artifact.schema.json';

export const AGENT_ASSURANCE_DEMO_ARTIFACTS = [
  jsonArtifact('agent-assurance', 'verify-lite/agent-assurance-demo/verify-lite-run-summary.json', VERIFY_LITE_SCHEMA),
  jsonArtifact('agent-assurance', 'agents/agent-assurance-demo/producer-normalization-summary.json', PRODUCER_SCHEMA),
  textArtifact('agent-assurance', 'agents/agent-assurance-demo/producer-normalization-summary.md'),
  jsonArtifact('agent-assurance', 'assurance/agent-assurance-demo/assurance-summary.json', ASSURANCE_SCHEMA),
  textArtifact('agent-assurance', 'assurance/agent-assurance-demo/assurance-summary.md'),
  jsonArtifact('agent-assurance', 'policy/agent-assurance-demo/policy-gate-summary.json', POLICY_SCHEMA),
  textArtifact('agent-assurance', 'policy/agent-assurance-demo/policy-gate-summary.md'),
  textArtifact('agent-assurance', 'review/agent-assurance-demo/assurance-review.md'),
];

export const DEMO_SMOKE_ARTIFACTS = [
  ...AGENT_ASSURANCE_DEMO_ARTIFACTS,
  jsonArtifact('scope-drift', 'agents/scope-drift-demo/producer-normalization-summary.json', PRODUCER_SCHEMA),
  textArtifact('scope-drift', 'agents/scope-drift-demo/producer-normalization-summary.md'),
  jsonArtifact('scope-drift', 'context-pack/scope-drift-demo/context-pack-boundary-map-report.json', null, validateBoundaryReport),
  textArtifact('scope-drift', 'context-pack/scope-drift-demo/context-pack-boundary-map-report.md'),
  jsonArtifact('scope-drift', 'context-pack/scope-drift-demo/boundary-map-summary.json', BOUNDARY_SUMMARY_SCHEMA),
  jsonArtifact('scope-drift', 'assurance/scope-drift-demo/assurance-summary.json', ASSURANCE_SCHEMA),
  textArtifact('scope-drift', 'assurance/scope-drift-demo/assurance-summary.md'),
  jsonArtifact('scope-drift', 'plan/scope-drift-demo/high-risk-plan-artifact.json', PLAN_ARTIFACT_SCHEMA),
  jsonArtifact('scope-drift', 'plan/scope-drift-demo/plan-artifact-validation.json', null, validatePlanValidation),
  textArtifact('scope-drift', 'plan/scope-drift-demo/plan-artifact-validation.md'),
  jsonArtifact('scope-drift', 'policy/scope-drift-demo/policy-gate-summary.normal.json', POLICY_SCHEMA),
  textArtifact('scope-drift', 'policy/scope-drift-demo/policy-gate-summary.normal.md'),
  jsonArtifact('scope-drift', 'policy/scope-drift-demo/policy-gate-summary.high-risk.json', POLICY_SCHEMA),
  textArtifact('scope-drift', 'policy/scope-drift-demo/policy-gate-summary.high-risk.md'),
  textArtifact('scope-drift', 'review/scope-drift-demo/assurance-review.md'),
  textArtifact('scope-drift', 'review/scope-drift-demo/assurance-review.high-risk.md'),

  jsonArtifact('high-risk-escalation', 'agents/high-risk-escalation-demo/producer-normalization-summary.json', PRODUCER_SCHEMA),
  textArtifact('high-risk-escalation', 'agents/high-risk-escalation-demo/producer-normalization-summary.md'),
  jsonArtifact('high-risk-escalation', 'assurance/high-risk-escalation-demo/claim-evidence-manifest.json', CLAIM_MANIFEST_SCHEMA),
  jsonArtifact('high-risk-escalation', 'assurance/high-risk-escalation-demo/claim-evidence-provenance.json', null, validateClaimEvidenceProvenance),
  jsonArtifact('high-risk-escalation', 'assurance/high-risk-escalation-demo/assurance-summary.json', ASSURANCE_SCHEMA),
  textArtifact('high-risk-escalation', 'assurance/high-risk-escalation-demo/assurance-summary.md'),
  jsonArtifact('high-risk-escalation', 'plan/high-risk-escalation-demo/high-risk-plan-artifact.json', PLAN_ARTIFACT_SCHEMA),
  jsonArtifact('high-risk-escalation', 'plan/high-risk-escalation-demo/plan-artifact-validation.json', null, validatePlanValidation),
  textArtifact('high-risk-escalation', 'plan/high-risk-escalation-demo/plan-artifact-validation.md'),
  jsonArtifact('high-risk-escalation', 'policy/high-risk-escalation-demo/policy-gate-summary.normal.json', POLICY_SCHEMA),
  textArtifact('high-risk-escalation', 'policy/high-risk-escalation-demo/policy-gate-summary.normal.md'),
  jsonArtifact('high-risk-escalation', 'policy/high-risk-escalation-demo/policy-gate-summary.high-risk.json', POLICY_SCHEMA),
  textArtifact('high-risk-escalation', 'policy/high-risk-escalation-demo/policy-gate-summary.high-risk.md'),
  textArtifact('high-risk-escalation', 'review/high-risk-escalation-demo/assurance-review.md'),
  textArtifact('high-risk-escalation', 'review/high-risk-escalation-demo/assurance-review.high-risk.md'),
];

function usage() {
  const demos = knownDemoNames().join(', ');
  process.stdout.write(`Usage: node scripts/demo/check-demo-smoke-artifacts.mjs [options]\n\nOptions:\n  --output-root <path>  Demo output root under the repository (default: ${DEFAULT_OUTPUT_ROOT})\n  --demo <name>        Check one demo only (currently: ${demos}).\n  --help               Show this help.\n`);
}

function jsonArtifact(demo, relativePath, schemaPath, customValidate = null) {
  return { demo, type: 'json', relativePath, schemaPath, customValidate };
}

function textArtifact(demo, relativePath) {
  return { demo, type: 'text', relativePath, schemaPath: null, customValidate: null };
}

function readRequiredValue(argv, index, flag) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`${flag} requires a value`);
  }
  return next;
}

function requireDemoValue(value, flag = '--demo') {
  const demo = String(value ?? '').trim();
  if (!demo) {
    throw new Error(`${flag} requires a non-empty demo name`);
  }
  return demo;
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    outputRoot: DEFAULT_OUTPUT_ROOT,
    demo: null,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--output-root') {
      options.outputRoot = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--demo') {
      options.demo = requireDemoValue(readRequiredValue(argv, index, arg), arg);
      index += 1;
      continue;
    }
    if (arg.startsWith('--demo=')) {
      options.demo = requireDemoValue(arg.slice('--demo='.length), '--demo');
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  return options;
}

export function knownDemoNames(artifacts = DEMO_SMOKE_ARTIFACTS) {
  return [...new Set(artifacts.map((artifact) => artifact.demo))].sort();
}

export function artifactsForDemo(demoName, artifacts = DEMO_SMOKE_ARTIFACTS) {
  if (!demoName) return artifacts;
  const selected = artifacts.filter((artifact) => artifact.demo === demoName);
  if (selected.length === 0) {
    const known = knownDemoNames(artifacts).join(', ');
    throw new Error(`unknown demo: ${demoName}; expected one of: ${known}`);
  }
  return selected;
}

function toPosixPath(filePath) {
  return filePath.split(path.sep).join('/');
}

function toRepoRelativePath(filePath, repoRoot = process.cwd()) {
  const relative = path.relative(repoRoot, path.resolve(repoRoot, filePath));
  return toPosixPath(relative || '.');
}

function ensureUnderRepoRoot(targetPath, label, repoRoot = process.cwd()) {
  const resolved = path.resolve(repoRoot, targetPath);
  const relative = path.relative(repoRoot, resolved);
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`${label} must stay under repository root: ${targetPath}`);
  }
  return resolved;
}

function readJsonFile(filePath) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`[json invalid] ${message}`);
  }
}

function createAjv(repoRoot) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const metadataSchemaPath = path.resolve(repoRoot, 'schema/artifact-metadata.schema.json');
  if (fs.existsSync(metadataSchemaPath)) {
    ajv.addSchema(readJsonFile(metadataSchemaPath));
  }
  return ajv;
}

function schemaValidatorCache(repoRoot) {
  const ajv = createAjv(repoRoot);
  const cache = new Map();
  return (schemaPath) => {
    if (!schemaPath) return null;
    if (!cache.has(schemaPath)) {
      const schemaAbsolutePath = path.resolve(repoRoot, schemaPath);
      cache.set(schemaPath, ajv.compile(readJsonFile(schemaAbsolutePath)));
    }
    return cache.get(schemaPath);
  };
}

function validateBoundaryReport(payload) {
  const errors = [];
  if (payload?.schemaVersion !== 'context-pack-boundary-map-report/v1') {
    errors.push('schemaVersion must be context-pack-boundary-map-report/v1');
  }
  if (payload?.status !== 'pass' && payload?.status !== 'review') {
    errors.push('status must be pass or review');
  }
  return errors;
}

function validateClaimEvidenceProvenance(payload) {
  const errors = [];
  if (payload?.schemaVersion !== 'verify-lite-assurance-provenance/v1') {
    errors.push('schemaVersion must be verify-lite-assurance-provenance/v1');
  }
  if (!payload?.artifact?.manifestPath || !payload?.artifact?.manifestSha256) {
    errors.push('artifact.manifestPath and artifact.manifestSha256 are required');
  }
  return errors;
}

function validatePlanValidation(payload) {
  const errors = [];
  if (payload?.result !== 'pass') {
    errors.push(`result must be pass, received ${String(payload?.result ?? 'missing')}`);
  }
  return errors;
}

function checkTextArtifact(filePath) {
  const content = fs.readFileSync(filePath, 'utf8');
  if (content.trim().length === 0) {
    return ['text artifact is empty'];
  }
  return [];
}

export function checkDemoSmokeArtifacts({
  outputRoot = DEFAULT_OUTPUT_ROOT,
  repoRoot = process.cwd(),
  artifacts = DEMO_SMOKE_ARTIFACTS,
} = {}) {
  const resolvedOutputRoot = ensureUnderRepoRoot(outputRoot, 'output-root', repoRoot);
  const getValidator = schemaValidatorCache(repoRoot);
  const failures = [];
  const checked = [];

  for (const artifact of artifacts) {
    const absolutePath = path.resolve(resolvedOutputRoot, artifact.relativePath);
    const repoRelative = toRepoRelativePath(absolutePath, repoRoot);
    const record = {
      demo: artifact.demo,
      type: artifact.type,
      path: repoRelative,
      schemaPath: artifact.schemaPath,
    };
    checked.push(record);

    if (!fs.existsSync(absolutePath)) {
      failures.push({ ...record, reason: '[artifact missing] expected artifact was not generated' });
      continue;
    }

    if (artifact.type === 'text') {
      for (const error of checkTextArtifact(absolutePath)) {
        failures.push({ ...record, reason: `[artifact invalid] ${error}` });
      }
      continue;
    }

    let payload;
    try {
      payload = readJsonFile(absolutePath);
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      failures.push({ ...record, reason: message });
      continue;
    }

    if (artifact.schemaPath) {
      const validate = getValidator(artifact.schemaPath);
      if (!validate(payload)) {
        failures.push({
          ...record,
          reason: `[schema invalid] ${JSON.stringify(validate.errors ?? [], null, 2)}`,
        });
      }
    }

    if (typeof artifact.customValidate === 'function') {
      for (const error of artifact.customValidate(payload)) {
        failures.push({ ...record, reason: `[artifact invalid] ${error}` });
      }
    }
  }

  return {
    ok: failures.length === 0,
    outputRoot: toRepoRelativePath(resolvedOutputRoot, repoRoot),
    checked,
    failures,
  };
}

function formatReport(report) {
  const lines = [
    '### Demo smoke artifact check',
    `- output root: ${report.outputRoot}`,
    `- checked artifacts: ${report.checked.length}`,
    `- failures: ${report.failures.length}`,
  ];

  const counts = report.checked.reduce((acc, artifact) => {
    acc[artifact.demo] = (acc[artifact.demo] ?? 0) + 1;
    return acc;
  }, {});
  for (const [demo, count] of Object.entries(counts)) {
    lines.push(`- ${demo}: ${count} artifacts`);
  }

  if (report.failures.length > 0) {
    lines.push('', '## Failures');
    for (const failure of report.failures) {
      lines.push(`- ${failure.path}: ${failure.reason}`);
    }
  }

  lines.push('');
  return lines.join('\n');
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    usage();
    return 0;
  }
  const report = checkDemoSmokeArtifacts({
    outputRoot: options.outputRoot,
    artifacts: artifactsForDemo(options.demo),
  });
  process.stdout.write(formatReport(report));
  if (!report.ok) {
    for (const failure of report.failures) {
      const annotation = failure.reason.replace(/\s+/gu, ' ').slice(0, 1000);
      process.stderr.write(`::error file=${failure.path}::${annotation}\n`);
    }
    return 1;
  }
  return 0;
}

const executedUrl = process.argv[1] ? pathToFileURL(path.resolve(process.argv[1])).href : null;
if (executedUrl && import.meta.url === executedUrl) {
  try {
    process.exitCode = run();
  } catch (error) {
    process.stderr.write(`[demo-smoke-artifacts] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}
