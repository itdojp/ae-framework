#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import {
  buildMarkdownSummary,
  buildPolicyGateReport,
  evaluatePolicyGate,
  inspectAgentAssuranceFindings,
} from '../ci/policy-gate.mjs';
import { loadRiskPolicy } from '../ci/lib/risk-policy.mjs';

const DEMO_NAME = 'high-risk-escalation-demo';
const DEFAULT_OUTPUT_ROOT = 'artifacts';
const DEFAULT_GENERATED_AT = '2026-06-21T00:00:00.000Z';
const DEFAULT_REPOSITORY = 'itdojp/ae-framework';
const DEFAULT_PR_NUMBER = 3512;
const EXAMPLE_ROOT = `examples/assurance-control-plane/${DEMO_NAME}`;
const PRODUCER_INPUT = `${EXAMPLE_ROOT}/producer-output/codex-cli-high-risk-escalation-output.json`;
const ASSURANCE_PROFILE = `${EXAMPLE_ROOT}/assurance-profile.json`;
const CLAIM_MANIFEST_FIXTURE = `${EXAMPLE_ROOT}/expected/claim-evidence-manifest.json`;
const PLAN_ARTIFACT_FIXTURE = `${EXAMPLE_ROOT}/expected/high-risk-plan-artifact.json`;
const PLAN_ARTIFACT_SCHEMA = 'schema/plan-artifact.schema.json';
const NORMAL_CHANGED_FILES = [
  `${EXAMPLE_ROOT}/README.md`,
  `${EXAMPLE_ROOT}/producer-output/codex-cli-high-risk-escalation-output.json`,
  'tests/unit/scripts/high-risk-escalation-demo.test.ts',
];
const HIGH_RISK_CHANGED_FILES = [
  'auth/tenant-isolation-policy.ts',
  'tests/unit/auth/tenant-isolation-policy.test.ts',
  `${EXAMPLE_ROOT}/README.md`,
];

function usage() {
  process.stdout.write(`Usage: node scripts/demo/run-high-risk-escalation-demo.mjs [options]\n\nOptions:\n  --output-root <path>      Output root under the repository (default: ${DEFAULT_OUTPUT_ROOT})\n  --generated-at <iso>     Deterministic generatedAt value (default: ${DEFAULT_GENERATED_AT})\n  --repository <owner/repo> Synthetic repository shown in policy summary (default: ${DEFAULT_REPOSITORY})\n  --pr-number <number>     Synthetic PR number shown in policy summary (default: ${DEFAULT_PR_NUMBER})\n  --help                   Show this help.\n`);
}

function readRequiredValue(argv, index, flag) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) throw new Error(`${flag} requires a value`);
  return next;
}

function ensureDateTime(value) {
  const raw = String(value ?? '').trim();
  if (!Number.isFinite(Date.parse(raw))) throw new Error(`generatedAt must be an ISO date-time: ${raw || '(empty)'}`);
  return new Date(raw).toISOString();
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
      if (!Number.isFinite(parsed) || parsed < 1) throw new Error(`${arg} must be a positive integer: ${raw}`);
      options.prNumber = parsed;
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }
  options.generatedAt = ensureDateTime(options.generatedAt);
  if (!/^[^/\s]+\/[^/\s]+$/u.test(options.repository)) throw new Error(`--repository must be owner/name: ${options.repository}`);
  return options;
}

function toPosixPath(filePath) {
  return filePath.split(path.sep).join('/');
}

function toRepoRelativePath(filePath) {
  const relative = path.relative(process.cwd(), path.resolve(filePath));
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) throw new Error(`path must stay under repository root: ${filePath}`);
  return toPosixPath(relative);
}

function ensureUnderRepoRoot(targetPath, label) {
  const resolved = path.resolve(targetPath);
  const relative = path.relative(process.cwd(), resolved);
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) throw new Error(`${label} must stay under repository root: ${targetPath}`);
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

function runNode(args) {
  const result = spawnSync(process.execPath, args, {
    cwd: process.cwd(),
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (result.stdout) process.stdout.write(result.stdout);
  if (result.stderr) process.stderr.write(result.stderr);
  if (result.status !== 0) throw new Error(`command failed: node ${args.join(' ')}`);
}

function normalizeRepoPaths(value) {
  const repoRoot = process.cwd();
  const normalizeString = (text) => String(text)
    .split(`${repoRoot}${path.sep}`).join('')
    .split(`${repoRoot}/`).join('');
  if (Array.isArray(value)) return value.map((entry) => normalizeRepoPaths(entry));
  if (value && typeof value === 'object') {
    return Object.fromEntries(Object.entries(value).map(([key, entry]) => [key, normalizeRepoPaths(entry)]));
  }
  if (typeof value === 'string') return normalizeString(value);
  return value;
}

function demoPaths(outputRoot) {
  const root = ensureUnderRepoRoot(outputRoot, 'output-root');
  return {
    outputRoot: root,
    producerJson: path.join(root, 'agents', DEMO_NAME, 'producer-normalization-summary.json'),
    producerMd: path.join(root, 'agents', DEMO_NAME, 'producer-normalization-summary.md'),
    claimManifestJson: path.join(root, 'assurance', DEMO_NAME, 'claim-evidence-manifest.json'),
    assuranceJson: path.join(root, 'assurance', DEMO_NAME, 'assurance-summary.json'),
    assuranceMd: path.join(root, 'assurance', DEMO_NAME, 'assurance-summary.md'),
    boundaryJson: path.join(root, 'context-pack', DEMO_NAME, 'boundary-map-summary.json'),
    planArtifactJson: path.join(root, 'plan', DEMO_NAME, 'high-risk-plan-artifact.json'),
    planValidationJson: path.join(root, 'plan', DEMO_NAME, 'plan-artifact-validation.json'),
    planValidationMd: path.join(root, 'plan', DEMO_NAME, 'plan-artifact-validation.md'),
    policyNormalJson: path.join(root, 'policy', DEMO_NAME, 'policy-gate-summary.normal.json'),
    policyNormalMd: path.join(root, 'policy', DEMO_NAME, 'policy-gate-summary.normal.md'),
    policyHighRiskJson: path.join(root, 'policy', DEMO_NAME, 'policy-gate-summary.high-risk.json'),
    policyHighRiskMd: path.join(root, 'policy', DEMO_NAME, 'policy-gate-summary.high-risk.md'),
    reviewNormalMd: path.join(root, 'review', DEMO_NAME, 'assurance-review.md'),
    reviewHighRiskMd: path.join(root, 'review', DEMO_NAME, 'assurance-review.high-risk.md'),
  };
}

function checkRun(name, generatedAt) {
  return {
    __typename: 'CheckRun',
    name,
    status: 'COMPLETED',
    conclusion: 'SUCCESS',
    workflowName: name,
    startedAt: generatedAt,
    completedAt: generatedAt,
  };
}

function materializeClaimManifest({ options, paths }) {
  const manifest = readJson(CLAIM_MANIFEST_FIXTURE);
  manifest.generatedAt = options.generatedAt;
  for (const artifact of manifest.sourceArtifacts) {
    if (artifact.id === 'producer-summary') {
      artifact.path = toRepoRelativePath(paths.producerJson);
    }
    if (artifact.id === 'manual-waiver-record') {
      artifact.path = `${toRepoRelativePath(paths.claimManifestJson)}#/claims/1/waiverRefs/0`;
    }
  }
  for (const claim of manifest.claims) {
    for (const evidence of claim.evidenceRefs) {
      if (evidence.sourceArtifactId === 'producer-summary') {
        evidence.artifactPath = evidence.artifactPath.replace(
          'artifacts/agents/high-risk-escalation-demo/producer-normalization-summary.json',
          toRepoRelativePath(paths.producerJson),
        );
      }
    }
  }
  writeJson(paths.claimManifestJson, manifest);
  return manifest;
}

function summarizeClaimForPolicy(claim, { strict }) {
  const evidenceRefs = Array.isArray(claim.evidenceRefs)
    ? claim.evidenceRefs.map((entry) => entry.id).filter(Boolean)
    : [];
  const missingEvidenceRefs = Array.isArray(claim.missingEvidenceRefs)
    ? claim.missingEvidenceRefs.map((entry) => entry.id).filter(Boolean)
    : [];
  const waiverRefs = Array.isArray(claim.waiverRefs)
    ? claim.waiverRefs.map((entry) => entry.id).filter(Boolean)
    : [];
  const waivers = strict && Array.isArray(claim.waiverRefs)
    ? claim.waiverRefs.map((entry) => ({
        id: entry.id,
        sourceArtifactId: entry.sourceArtifactId,
        status: entry.status,
        owner: entry.owner ?? null,
        reason: entry.reason ?? null,
        expires: entry.expires ?? null,
      }))
    : [];
  return {
    claimId: claim.id,
    result: strict && claim.status === 'unresolved' ? 'block' : (strict && claim.status === 'waived' ? 'waived' : 'report-only'),
    status: claim.status,
    evidenceRefs,
    missingEvidenceRefs,
    waiverRefs,
    waivers,
  };
}

function buildAssuranceStateForPolicy({ manifest, paths, strict }) {
  return {
    path: toRepoRelativePath(paths.claimManifestJson),
    present: true,
    schemaVersion: 'claim-evidence-manifest/v1',
    generatedAt: manifest.generatedAt,
    provenance: strict
      ? {
          path: 'artifacts/assurance/high-risk-escalation-demo/claim-evidence-provenance.json',
          present: true,
          trusted: true,
          schemaVersion: 'claim-evidence-provenance/v1',
          generatedAt: manifest.generatedAt,
          warnings: [],
          errors: [],
        }
      : null,
    summary: {
      totalClaims: manifest.summary.totalClaims,
    },
    claims: manifest.claims.map((claim) => summarizeClaimForPolicy(claim, { strict })),
    warnings: strict ? [] : ['Selected tenant-isolation claim gaps remain report-only until risk:high / enforce-assurance selects strict assurance.'],
    errors: [],
  };
}

function prepareHighRiskPlanArtifact({ options, paths }) {
  const planArtifact = readJson(PLAN_ARTIFACT_FIXTURE);
  planArtifact.generatedAt = options.generatedAt;
  planArtifact.source = {
    ...planArtifact.source,
    repository: options.repository,
    prNumber: options.prNumber,
  };
  writeJson(paths.planArtifactJson, planArtifact);
  runNode([
    'scripts/plan-artifact/validate.mjs',
    '--file', toRepoRelativePath(paths.planArtifactJson),
    '--schema', PLAN_ARTIFACT_SCHEMA,
    '--output-json', toRepoRelativePath(paths.planValidationJson),
    '--output-md', toRepoRelativePath(paths.planValidationMd),
  ]);
  writeJson(paths.planValidationJson, normalizeRepoPaths(readJson(paths.planValidationJson)));
  writeText(paths.planValidationMd, normalizeRepoPaths(fs.readFileSync(paths.planValidationMd, 'utf8')));
  const validation = normalizeRepoPaths(readJson(paths.planValidationJson));
  return {
    present: true,
    result: validation.result === 'pass' ? 'pass' : 'fail',
    riskSelected: planArtifact.risk.selected,
    path: toRepoRelativePath(paths.planArtifactJson),
    schemaPath: PLAN_ARTIFACT_SCHEMA,
    validationErrors: validation.errors ?? [],
    warnings: validation.warnings ?? [],
    source: planArtifact.source,
  };
}

function buildPolicySummary({ options, paths, manifest, mode, highRiskPlanArtifact }) {
  const policy = loadRiskPolicy('policy/risk-policy.yml');
  const agentAssuranceFindings = inspectAgentAssuranceFindings({
    assuranceSummaryPath: paths.assuranceJson,
    producerSummaryPath: paths.producerJson,
  });
  const isHighRisk = mode === 'high-risk';
  const labels = isHighRisk
    ? ['risk:high', 'enforce-assurance', 'enforce-testing']
    : ['risk:low'];
  const reviews = isHighRisk
    ? [{ id: 1, state: 'APPROVED', submitted_at: options.generatedAt, user: { login: 'human-reviewer', type: 'User' } }]
    : [];
  const statusRollup = [
    checkRun('verify-lite', options.generatedAt),
    checkRun('gate', options.generatedAt),
    checkRun('integration / run', options.generatedAt),
    checkRun('validate-artifacts / validate', options.generatedAt),
    ...(isHighRisk ? [checkRun('testing-ddd', options.generatedAt)] : []),
  ];
  const evaluation = evaluatePolicyGate({
    policy,
    pullRequest: {
      labels: labels.map((name) => ({ name })),
      body: '## Acceptance\nSelected high-risk tenant-isolation claim gaps are visible in the reviewer surface.\n\n## Rollback\nDelete the generated demo artifacts and rerun the scenario.',
    },
    changedFiles: isHighRisk ? HIGH_RISK_CHANGED_FILES : NORMAL_CHANGED_FILES,
    reviews,
    statusRollup,
    reviewTopology: 'team',
    assuranceMode: isHighRisk ? 'strict' : 'report-only',
    assurance: buildAssuranceStateForPolicy({ manifest, paths, strict: isHighRisk }),
    agentAssuranceFindings,
    planArtifact: isHighRisk ? highRiskPlanArtifact : null,
  });
  return normalizeRepoPaths(buildPolicyGateReport({
    generatedAtUtc: options.generatedAt,
    repository: options.repository,
    prNumber: options.prNumber,
    changedFiles: isHighRisk ? HIGH_RISK_CHANGED_FILES : NORMAL_CHANGED_FILES,
    evaluation,
  }));
}

function run(options) {
  const paths = demoPaths(options.outputRoot);
  runNode([
    'scripts/agents/normalize-producer-output.mjs',
    '--input', PRODUCER_INPUT,
    '--out-json', toRepoRelativePath(paths.producerJson),
    '--out-md', toRepoRelativePath(paths.producerMd),
    '--generated-at', options.generatedAt,
  ]);

  const manifest = materializeClaimManifest({ options, paths });

  runNode([
    'scripts/assurance/aggregate-lanes.mjs',
    '--assurance-profile', ASSURANCE_PROFILE,
    '--producer-summary', toRepoRelativePath(paths.producerJson),
    '--claim-evidence-manifest', toRepoRelativePath(paths.claimManifestJson),
    '--generated-at', options.generatedAt,
    '--output-json', toRepoRelativePath(paths.assuranceJson),
    '--output-md', toRepoRelativePath(paths.assuranceMd),
  ]);
  writeJson(paths.assuranceJson, normalizeRepoPaths(readJson(paths.assuranceJson)));
  writeText(paths.assuranceMd, normalizeRepoPaths(fs.readFileSync(paths.assuranceMd, 'utf8')));

  const highRiskPlanArtifact = prepareHighRiskPlanArtifact({ options, paths });
  const normalPolicy = buildPolicySummary({
    options, paths, manifest, mode: 'normal', highRiskPlanArtifact,
  });
  const highRiskPolicy = buildPolicySummary({
    options, paths, manifest, mode: 'high-risk', highRiskPlanArtifact,
  });
  writeJson(paths.policyNormalJson, normalPolicy);
  writeText(paths.policyNormalMd, buildMarkdownSummary(options.prNumber, normalPolicy.evaluation));
  writeJson(paths.policyHighRiskJson, highRiskPolicy);
  writeText(paths.policyHighRiskMd, buildMarkdownSummary(options.prNumber, highRiskPolicy.evaluation));

  runNode([
    'scripts/assurance/render-pr-review-surface.mjs',
    '--title', 'High-Risk Escalation Assurance Demo Review',
    '--producer-summary', toRepoRelativePath(paths.producerJson),
    '--assurance-summary', toRepoRelativePath(paths.assuranceJson),
    '--policy-gate-summary', toRepoRelativePath(paths.policyNormalJson),
    '--boundary-map-summary', toRepoRelativePath(paths.boundaryJson),
    '--claim-evidence-manifest', toRepoRelativePath(paths.claimManifestJson),
    '--output-md', toRepoRelativePath(paths.reviewNormalMd),
    '--generated-at', options.generatedAt,
  ]);

  runNode([
    'scripts/assurance/render-pr-review-surface.mjs',
    '--title', 'High-Risk Escalation Assurance Demo Review — High-Risk Strict Lane',
    '--producer-summary', toRepoRelativePath(paths.producerJson),
    '--assurance-summary', toRepoRelativePath(paths.assuranceJson),
    '--policy-gate-summary', toRepoRelativePath(paths.policyHighRiskJson),
    '--boundary-map-summary', toRepoRelativePath(paths.boundaryJson),
    '--claim-evidence-manifest', toRepoRelativePath(paths.claimManifestJson),
    '--output-md', toRepoRelativePath(paths.reviewHighRiskMd),
    '--generated-at', options.generatedAt,
  ]);

  const producer = readJson(paths.producerJson);
  const assurance = readJson(paths.assuranceJson);
  process.stdout.write([
    'High-Risk Escalation Assurance Demo',
    `output_root: ${toRepoRelativePath(paths.outputRoot)}`,
    `selected_critical_claims: ${assurance.claims.filter((claim) => claim.criticality === 'high' || claim.criticality === 'critical').length}`,
    `selected_high_risk_claim_count: ${assurance.claims.filter((claim) => claim.criticality === 'high' || claim.criticality === 'critical').length}`,
    `producer_missing_evidence_count: ${producer.summary?.missingEvidence ?? 0}`,
    `manifest_missing_evidence_claims: ${assurance.reviewSurface?.claimEvidence?.missingEvidenceClaims?.length ?? 'unknown'}`,
    `normal_policy_result: ${normalPolicy.evaluation?.assurance?.result ?? 'unknown'} (ok=${normalPolicy.evaluation?.ok ?? 'unknown'})`,
    `high_risk_policy_result: ${highRiskPolicy.evaluation?.assurance?.result ?? 'unknown'} (ok=${highRiskPolicy.evaluation?.ok ?? 'unknown'})`,
    'network: not used',
    'GitHub token: not required',
    `review_markdown: ${toRepoRelativePath(paths.reviewNormalMd)}`,
    '',
  ].join('\n'));
}

try {
  const options = parseArgs();
  if (options.help) {
    usage();
  } else {
    run(options);
  }
} catch (error) {
  const message = error instanceof Error ? error.message : String(error);
  console.error(`high-risk-escalation-demo: ${message}`);
  process.exitCode = 1;
}
