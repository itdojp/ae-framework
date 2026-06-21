#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import {
  buildMarkdownSummary,
  buildPolicyGateReport,
  evaluatePolicyGate,
  inspectAgentAssuranceFindings,
} from '../ci/policy-gate.mjs';
import { loadRiskPolicy } from '../ci/lib/risk-policy.mjs';

const DEMO_NAME = 'agent-assurance-demo';
const DEFAULT_OUTPUT_ROOT = 'artifacts';
const DEFAULT_GENERATED_AT = '2026-06-21T00:00:00.000Z';
const DEFAULT_REPOSITORY = 'itdojp/ae-framework';
const DEFAULT_PR_NUMBER = 3509;
const PRODUCER_INPUT = 'examples/assurance-control-plane/codex-change-package-demo/producer-output/codex-cli-task-output.json';
const ASSURANCE_PROFILE = 'fixtures/assurance/sample.assurance-profile.json';
const VERIFY_LITE_FIXTURE = 'fixtures/assurance-e2e/inventory-waiver/expected/verify-lite-run-summary.json';

function usage() {
  process.stdout.write(`Usage: node scripts/demo/run-agent-assurance-demo.mjs [options]\n\nOptions:\n  --output-root <path>      Output root under the repository (default: ${DEFAULT_OUTPUT_ROOT})\n  --generated-at <iso>     Deterministic generatedAt value (default: ${DEFAULT_GENERATED_AT})\n  --repository <owner/repo> Synthetic repository shown in policy summary (default: ${DEFAULT_REPOSITORY})\n  --pr-number <number>     Synthetic PR number shown in policy summary (default: ${DEFAULT_PR_NUMBER})\n  --help                   Show this help.\n`);
}

function readRequiredValue(argv, index, flag) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`${flag} requires a value`);
  }
  return next;
}

function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    outputRoot: DEFAULT_OUTPUT_ROOT,
    generatedAt: DEFAULT_GENERATED_AT,
    repository: DEFAULT_REPOSITORY,
    prNumber: DEFAULT_PR_NUMBER,
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
    if (arg === '--generated-at') {
      options.generatedAt = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--repository') {
      options.repository = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--pr-number') {
      const raw = readRequiredValue(argv, index, arg);
      const parsed = Number.parseInt(raw, 10);
      if (!Number.isFinite(parsed) || parsed < 1) {
        throw new Error(`${arg} must be a positive integer: ${raw}`);
      }
      options.prNumber = parsed;
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  options.generatedAt = ensureDateTime(options.generatedAt);
  if (!/^[^/\s]+\/[^/\s]+$/u.test(options.repository)) {
    throw new Error(`--repository must be owner/name: ${options.repository}`);
  }
  return options;
}

function ensureDateTime(value) {
  const raw = String(value ?? '').trim();
  if (!Number.isFinite(Date.parse(raw))) {
    throw new Error(`generatedAt must be an ISO date-time: ${raw || '(empty)'}`);
  }
  return new Date(raw).toISOString();
}

function toPosixPath(filePath) {
  return filePath.split(path.sep).join('/');
}

function toRepoRelativePath(filePath) {
  const relative = path.relative(process.cwd(), path.resolve(filePath));
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`path must stay under repository root: ${filePath}`);
  }
  return toPosixPath(relative);
}

function ensureUnderRepoRoot(targetPath, label) {
  const resolved = path.resolve(targetPath);
  const relative = path.relative(process.cwd(), resolved);
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`${label} must stay under the repository root: ${targetPath}`);
  }
  return resolved;
}

function ensureParent(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function writeJson(filePath, value) {
  ensureParent(filePath);
  fs.writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

function writeText(filePath, value) {
  ensureParent(filePath);
  fs.writeFileSync(filePath, value, 'utf8');
}

function copyJsonFixture(sourcePath, outputPath, generatedAt) {
  const payload = readJson(sourcePath);
  payload.timestamp = generatedAt;
  if (payload.metadata && typeof payload.metadata === 'object') {
    payload.metadata.generatedAtUtc = generatedAt;
    payload.metadata.generatedAtLocal = generatedAt.replace(/\.000Z$/u, '.000+00:00');
    payload.metadata.branch = DEMO_NAME;
    payload.metadata.runner = {
      name: 'agent-assurance-demo-fixture',
      os: process.platform,
      arch: process.arch,
      ci: false,
    };
    payload.metadata.toolVersions = {
      node: process.version,
    };
  }
  writeJson(outputPath, payload);
  return payload;
}

function runNode(args) {
  const result = spawnSync(process.execPath, args, {
    cwd: process.cwd(),
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (result.stdout) process.stdout.write(result.stdout);
  if (result.stderr) process.stderr.write(result.stderr);
  if (result.status !== 0) {
    throw new Error(`command failed: node ${args.join(' ')}`);
  }
}

function loadSchema(schemaPath) {
  return readJson(path.resolve(schemaPath));
}

function validateArtifact(label, payload, schemaPath) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const metadataSchemaPath = path.resolve('schema/artifact-metadata.schema.json');
  if (fs.existsSync(metadataSchemaPath)) {
    ajv.addSchema(readJson(metadataSchemaPath));
  }
  const validate = ajv.compile(loadSchema(schemaPath));
  if (!validate(payload)) {
    throw new Error(`${label} schema validation failed: ${JSON.stringify(validate.errors ?? [], null, 2)}`);
  }
}

function normalizeRepoPaths(value) {
  const repoRoot = process.cwd();
  const normalizeString = (text) => {
    const normalized = String(text);
    return normalized
      .split(`${repoRoot}${path.sep}`).join('')
      .split(`${repoRoot}/`).join('');
  };
  if (Array.isArray(value)) {
    return value.map((entry) => normalizeRepoPaths(entry));
  }
  if (value && typeof value === 'object') {
    return Object.fromEntries(Object.entries(value).map(([key, entry]) => [key, normalizeRepoPaths(entry)]));
  }
  if (typeof value === 'string') {
    return normalizeString(value);
  }
  return value;
}

function demoPaths(outputRoot) {
  const root = ensureUnderRepoRoot(outputRoot, 'output-root');
  return {
    outputRoot: root,
    verifyLiteJson: path.join(root, 'verify-lite', DEMO_NAME, 'verify-lite-run-summary.json'),
    producerJson: path.join(root, 'agents', DEMO_NAME, 'producer-normalization-summary.json'),
    producerMd: path.join(root, 'agents', DEMO_NAME, 'producer-normalization-summary.md'),
    assuranceJson: path.join(root, 'assurance', DEMO_NAME, 'assurance-summary.json'),
    assuranceMd: path.join(root, 'assurance', DEMO_NAME, 'assurance-summary.md'),
    policyJson: path.join(root, 'policy', DEMO_NAME, 'policy-gate-summary.json'),
    policyMd: path.join(root, 'policy', DEMO_NAME, 'policy-gate-summary.md'),
    reviewMd: path.join(root, 'review', DEMO_NAME, 'assurance-review.md'),
  };
}

function buildSyntheticPolicySummary({ options, paths, assuranceSummary }) {
  const producerSummaryPath = toRepoRelativePath(paths.producerJson);
  const assuranceSummaryPath = toRepoRelativePath(paths.assuranceJson);
  const policy = loadRiskPolicy('policy/risk-policy.yml');
  const agentAssuranceFindings = inspectAgentAssuranceFindings({
    assuranceSummaryPath: paths.assuranceJson,
    producerSummaryPath: paths.producerJson,
  });
  const pullRequest = {
    labels: [{ name: 'risk:low' }],
    body: '## Acceptance\nOffline BYO-agent assurance demo artifacts were generated and schema-validated.\n\n## Rollback\nDelete the generated demo artifacts and rerun the demo command.',
  };
  const changedFiles = [
    PRODUCER_INPUT,
    'examples/assurance-control-plane/codex-change-package-demo/README.md',
    'docs/guides/byo-agent-assurance-quickstart.md',
  ];
  const statusRollup = [
    {
      __typename: 'CheckRun',
      name: 'verify-lite',
      status: 'COMPLETED',
      conclusion: 'SUCCESS',
      workflowName: 'Verify Lite',
      startedAt: options.generatedAt,
      completedAt: options.generatedAt,
    },
  ];
  const assuranceState = {
    path: assuranceSummaryPath,
    present: true,
    schemaVersion: assuranceSummary.schemaVersion ?? 'assurance-summary/v1',
    generatedAt: assuranceSummary.generatedAt ?? options.generatedAt,
    summary: {
      totalClaims: assuranceSummary.summary?.claimCount ?? 0,
    },
    claims: [],
    warnings: [],
    errors: [],
  };
  const evaluation = evaluatePolicyGate({
    policy,
    pullRequest,
    changedFiles,
    reviews: [],
    statusRollup,
    reviewTopology: 'solo',
    assuranceMode: 'report-only',
    assurance: assuranceState,
    agentAssuranceFindings,
  });
  const summary = buildPolicyGateReport({
    generatedAtUtc: options.generatedAt,
    repository: options.repository,
    prNumber: options.prNumber,
    changedFiles,
    evaluation,
  });
  const normalizedSummary = normalizeRepoPaths(summary);
  const normalizedEvaluation = normalizedSummary.evaluation;
  writeJson(paths.policyJson, normalizedSummary);
  writeText(paths.policyMd, buildMarkdownSummary(options.prNumber, normalizedEvaluation));
  return { summary: normalizedSummary, producerSummaryPath, assuranceSummaryPath };
}

function renderReviewMarkdown({ options, paths, producerSummary, assuranceSummary, policySummary }) {
  const producer = producerSummary.producer?.displayName ?? producerSummary.producer?.id ?? 'producer';
  const producerFindings = producerSummary.summary?.reportOnlyFindings ?? 0;
  const missingEvidence = producerSummary.summary?.missingEvidence ?? 0;
  const assuranceAction = assuranceSummary.reviewSurface?.recommendedReviewerAction?.action ?? 'review-summary';
  const assuranceReason = assuranceSummary.reviewSurface?.recommendedReviewerAction?.reason ?? 'Review the generated assurance summary.';
  const policyResult = policySummary.evaluation?.assurance?.result ?? 'report-only';
  const policyMode = policySummary.evaluation?.assurance?.mode ?? 'report-only';

  return `# BYO-Agent Assurance Demo Review\n\n` +
    `> Demo-only reviewer surface. This Markdown is generated offline from fixtures and does not approve, prove, or merge a PR.\n\n` +
    `- Generated at: \`${options.generatedAt}\`\n` +
    `- Producer fixture: \`${PRODUCER_INPUT}\`\n` +
    `- Producer: \`${producer}\`\n` +
    `- Flow: producer output -> normalized evidence -> assurance summary -> policy report -> reviewer surface\n\n` +
    `## What reviewers should inspect first\n\n` +
    `1. **Producer normalization summary** — inspect missing evidence before trusting the producer narrative.\n` +
    `   - Artifact: \`${toRepoRelativePath(paths.producerJson)}\`\n` +
    `   - \`missing_evidence_finding_count\`: ${missingEvidence}\n` +
    `   - Report-only findings: ${producerFindings}\n` +
    `2. **Assurance summary** — inspect the recommended reviewer action and unresolved claim state.\n` +
    `   - Artifact: \`${toRepoRelativePath(paths.assuranceJson)}\`\n` +
    `   - Recommended action: \`${assuranceAction}\`\n` +
    `   - Reason: ${assuranceReason}\n` +
    `3. **Policy-gate summary** — confirm the fast-lane policy interpretation remains report-only.\n` +
    `   - Artifact: \`${toRepoRelativePath(paths.policyJson)}\`\n` +
    `   - Policy assurance result: \`${policyResult}\` (mode: \`${policyMode}\`)\n` +
    `4. **Verify Lite fixture summary** — use the baseline check summary as supporting evidence, not as proof.\n` +
    `   - Artifact: \`${toRepoRelativePath(paths.verifyLiteJson)}\`\n\n` +
    `## Demo-scoped effectiveness metrics\n\n` +
    `| Metric | Demo value | Interpretation |\n` +
    `| --- | --- | --- |\n` +
    `| \`missing_evidence_finding_count\` | ${missingEvidence} | Reviewer should check which producer claims still need schema-backed evidence. |\n` +
    `| \`scope_drift_finding_count\` | 0 | This quickstart does not model scope drift; scope drift is covered by a later scenario pack. |\n` +
    `| \`reviewer_comment_count\` | not collected | The quickstart is local and does not create a GitHub PR or review thread. |\n` +
    `| \`ci_rerun_count\` | not collected | The demo is offline and does not invoke GitHub Actions. |\n\n` +
    `## Baseline / Structured / High-assurance interpretation\n\n` +
    `- **Baseline**: verify-lite fixture and policy summary show the routine fast-lane check surface.\n` +
    `- **Structured assurance**: producer normalization and assurance summary expose claims, report-only findings, and missing evidence.\n` +
    `- **High-assurance escalation**: not mandatory here. Select \`risk:high\` / \`enforce-assurance\` only for critical claims such as authorization, payment, migrations, or security boundaries.\n\n` +
    `## Trust boundary\n\n` +
    `Producer output is evidence input, not approval. Raw logs support the decision only after ae-framework turns them into schema-backed artifacts and policy-oriented summaries.\n`;
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    usage();
    return 0;
  }
  const paths = demoPaths(options.outputRoot);

  const verifyLiteSummary = copyJsonFixture(VERIFY_LITE_FIXTURE, paths.verifyLiteJson, options.generatedAt);
  validateArtifact('verify-lite summary', verifyLiteSummary, 'schema/verify-lite-run-summary.schema.json');

  runNode([
    'scripts/agents/normalize-producer-output.mjs',
    '--input', PRODUCER_INPUT,
    '--out-json', toRepoRelativePath(paths.producerJson),
    '--out-md', toRepoRelativePath(paths.producerMd),
    '--generated-at', options.generatedAt,
  ]);
  const producerSummary = readJson(paths.producerJson);
  validateArtifact('producer normalization summary', producerSummary, 'schema/producer-normalization-summary.schema.json');

  runNode([
    'scripts/assurance/aggregate-lanes.mjs',
    '--assurance-profile', ASSURANCE_PROFILE,
    '--producer-summary', toRepoRelativePath(paths.producerJson),
    '--generated-at', options.generatedAt,
    '--output-json', toRepoRelativePath(paths.assuranceJson),
    '--output-md', toRepoRelativePath(paths.assuranceMd),
  ]);
  const assuranceSummary = readJson(paths.assuranceJson);
  validateArtifact('assurance summary', assuranceSummary, 'schema/assurance-summary.schema.json');

  const policyArtifacts = buildSyntheticPolicySummary({ options, paths, assuranceSummary });
  validateArtifact('policy gate summary', policyArtifacts.summary, 'schema/policy-gate-summary-v1.schema.json');

  const reviewMarkdown = renderReviewMarkdown({
    options,
    paths,
    producerSummary,
    assuranceSummary,
    policySummary: policyArtifacts.summary,
  });
  writeText(paths.reviewMd, reviewMarkdown);

  process.stdout.write('### BYO-Agent Assurance Demo\n');
  process.stdout.write(`- output root: ${toRepoRelativePath(paths.outputRoot)}\n`);
  process.stdout.write(`- verify-lite summary: ${toRepoRelativePath(paths.verifyLiteJson)}\n`);
  process.stdout.write(`- producer summary: ${toRepoRelativePath(paths.producerJson)}\n`);
  process.stdout.write(`- assurance summary: ${toRepoRelativePath(paths.assuranceJson)}\n`);
  process.stdout.write(`- policy summary: ${toRepoRelativePath(paths.policyJson)}\n`);
  process.stdout.write(`- reviewer surface: ${toRepoRelativePath(paths.reviewMd)}\n`);
  process.stdout.write(`- missing_evidence_finding_count: ${producerSummary.summary?.missingEvidence ?? 0}\n`);
  process.stdout.write(`- policy assurance result: ${policyArtifacts.summary.evaluation?.assurance?.result ?? 'unknown'} (${policyArtifacts.summary.evaluation?.assurance?.mode ?? 'unknown'})\n`);
  process.stdout.write('- network: not used\n');
  process.stdout.write('- GitHub token: not required\n');
  return 0;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  try {
    process.exitCode = run();
  } catch (error) {
    process.stderr.write(`[agent-assurance-demo] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}
