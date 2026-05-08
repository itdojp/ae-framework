#!/usr/bin/env node

import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import {
  DEFAULT_POLICY_PATH,
  collectRequiredLabels,
  getRiskLabels,
  inferRiskLevel,
  loadRiskPolicy,
} from '../ci/lib/risk-policy.mjs';
import { normalizeLabelNames } from '../ci/lib/automation-guards.mjs';

const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/change-package/change-package.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/change-package/change-package.md';
const DEFAULT_V2_OUTPUT_JSON_PATH = 'artifacts/change-package/change-package-v2.json';
const DEFAULT_V2_OUTPUT_MD_PATH = 'artifacts/change-package/change-package-v2.md';
const DEFAULT_ARTIFACT_ROOT = '.';
const DEFAULT_MODE = 'detailed';
const DEFAULT_CLAIM_EVIDENCE_MANIFEST_PATH = 'artifacts/assurance/claim-evidence-manifest.json';
const DEFAULT_POLICY_DECISION_PATH = 'artifacts/ci/policy-decision-js-v1.json';
const DEFAULT_ASSURANCE_SUMMARY_PATH = 'artifacts/assurance/assurance-summary.json';
const DEFAULT_CLAIM_LEVEL_SUMMARY_PATH = 'artifacts/assurance/claim-level-summary.json';
const DEFAULT_POST_DEPLOY_VERIFY_PATH = 'artifacts/release/post-deploy-verify.json';

const ASSURANCE_LEVELS = ['A0', 'A1', 'A2', 'A3', 'A4'];
const V2_CLAIM_STATUSES = new Set([
  'satisfied',
  'proved',
  'model-checked',
  'tested',
  'runtime-mitigated',
  'waived',
  'unresolved',
  'failed',
  'not-applicable',
]);
const V2_PROOF_METHODS = new Set([
  'spec',
  'property',
  'tla',
  'alloy',
  'smt',
  'csp',
  'lean',
  'kani',
  'runtime',
]);
const V2_PROOF_STATUSES = new Set(['open', 'discharged', 'waived']);

const EVIDENCE_CATALOG = [
  {
    id: 'verifyLiteSummary',
    path: 'artifacts/verify-lite/verify-lite-run-summary.json',
    description: 'verify-lite run summary',
  },
  {
    id: 'policyGateSummary',
    path: 'artifacts/ci/policy-gate-summary.json',
    description: 'policy-gate summary',
  },
  {
    id: 'harnessHealth',
    path: 'artifacts/ci/harness-health.json',
    description: 'harness health summary',
  },
  {
    id: 'conformanceSummary',
    path: 'artifacts/hermetic-reports/conformance/summary.json',
    description: 'runtime conformance summary',
  },
  {
    id: 'contextPackSuggestions',
    path: 'artifacts/context-pack/context-pack-suggestions.json',
    description: 'context-pack suggestions summary',
  },
];
const ENFORCE_ARTIFACTS_STRICT_COMMAND = [
  'bash scripts/trace/run-kvonce-conformance.sh --input samples/trace/kvonce-sample.ndjson --format ndjson --output-dir artifacts/hermetic-reports/trace',
  'node scripts/ci/write-verify-lite-summary.mjs',
  'node scripts/trace/create-report-envelope.mjs artifacts/verify-lite/verify-lite-run-summary.json artifacts/report-envelope.json',
  'mkdir -p artifacts/trace',
  'cp artifacts/report-envelope.json artifacts/trace/report-envelope.json',
  'pnpm run artifacts:validate -- --strict=true',
].join(' && ');

function parseChangedFilesEnv(value) {
  if (!value) return [];
  const separators = value.includes('\n') ? '\n' : ',';
  return value
    .split(separators)
    .map((entry) => String(entry || '').trim())
    .filter(Boolean);
}

function toUniqueSorted(values) {
  return [...new Set(values)].sort((left, right) => left.localeCompare(right));
}

function parseLabelsCsv(value) {
  if (!value) return [];
  return value
    .split(',')
    .map((entry) => String(entry || '').trim())
    .filter(Boolean);
}

function normalizeSchemaVersion(value) {
  const normalized = String(value || 'v1').trim().toLowerCase();
  if (normalized === 'v1' || normalized === 'change-package/v1') {
    return 'v1';
  }
  if (normalized === 'v2' || normalized === 'change-package/v2') {
    return 'v2';
  }
  throw new Error(`unsupported schema version: ${value}`);
}

function parseArgs(argv = process.argv) {
  const options = {
    policyPath: DEFAULT_POLICY_PATH,
    outputJsonPath: DEFAULT_OUTPUT_JSON_PATH,
    outputMarkdownPath: DEFAULT_OUTPUT_MD_PATH,
    v2OutputJsonPath: DEFAULT_V2_OUTPUT_JSON_PATH,
    v2OutputMarkdownPath: DEFAULT_V2_OUTPUT_MD_PATH,
    changedFilesPath: '',
    artifactRoot: DEFAULT_ARTIFACT_ROOT,
    mode: DEFAULT_MODE,
    schemaVersion: 'v1',
    dualWrite: false,
    claimEvidenceManifestPath: DEFAULT_CLAIM_EVIDENCE_MANIFEST_PATH,
    policyDecisionPath: DEFAULT_POLICY_DECISION_PATH,
    assuranceSummaryPath: DEFAULT_ASSURANCE_SUMMARY_PATH,
    claimLevelSummaryPath: DEFAULT_CLAIM_LEVEL_SUMMARY_PATH,
    postDeployVerifyPath: DEFAULT_POST_DEPLOY_VERIFY_PATH,
    repository: '',
    prNumber: null,
    baseRef: '',
    headRef: '',
    intentSummary: '',
    labelsCsv: '',
    eventPath: process.env.GITHUB_EVENT_PATH || '',
    help: false,
    outputJsonPathExplicit: false,
    outputMarkdownPathExplicit: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    const readValue = (name) => {
      if (!next || next.startsWith('-')) {
        throw new Error(`missing value for ${name}`);
      }
      index += 1;
      return next;
    };

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--policy') {
      options.policyPath = readValue('--policy');
      continue;
    }
    if (arg.startsWith('--policy=')) {
      options.policyPath = arg.slice('--policy='.length);
      continue;
    }
    if (arg === '--output-json') {
      options.outputJsonPath = readValue('--output-json');
      options.outputJsonPathExplicit = true;
      continue;
    }
    if (arg.startsWith('--output-json=')) {
      options.outputJsonPath = arg.slice('--output-json='.length);
      options.outputJsonPathExplicit = true;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMarkdownPath = readValue('--output-md');
      options.outputMarkdownPathExplicit = true;
      continue;
    }
    if (arg.startsWith('--output-md=')) {
      options.outputMarkdownPath = arg.slice('--output-md='.length);
      options.outputMarkdownPathExplicit = true;
      continue;
    }
    if (arg === '--v2-output-json') {
      options.v2OutputJsonPath = readValue('--v2-output-json');
      continue;
    }
    if (arg.startsWith('--v2-output-json=')) {
      options.v2OutputJsonPath = arg.slice('--v2-output-json='.length);
      continue;
    }
    if (arg === '--v2-output-md') {
      options.v2OutputMarkdownPath = readValue('--v2-output-md');
      continue;
    }
    if (arg.startsWith('--v2-output-md=')) {
      options.v2OutputMarkdownPath = arg.slice('--v2-output-md='.length);
      continue;
    }
    if (arg === '--changed-files-file') {
      options.changedFilesPath = readValue('--changed-files-file');
      continue;
    }
    if (arg.startsWith('--changed-files-file=')) {
      options.changedFilesPath = arg.slice('--changed-files-file='.length);
      continue;
    }
    if (arg === '--artifact-root') {
      options.artifactRoot = readValue('--artifact-root');
      continue;
    }
    if (arg.startsWith('--artifact-root=')) {
      options.artifactRoot = arg.slice('--artifact-root='.length);
      continue;
    }
    if (arg === '--mode') {
      options.mode = readValue('--mode');
      continue;
    }
    if (arg.startsWith('--mode=')) {
      options.mode = arg.slice('--mode='.length);
      continue;
    }
    if (arg === '--schema-version') {
      options.schemaVersion = readValue('--schema-version');
      continue;
    }
    if (arg.startsWith('--schema-version=')) {
      options.schemaVersion = arg.slice('--schema-version='.length);
      continue;
    }
    if (arg === '--dual-write') {
      options.dualWrite = true;
      continue;
    }
    if (arg === '--claim-evidence-manifest') {
      options.claimEvidenceManifestPath = readValue('--claim-evidence-manifest');
      continue;
    }
    if (arg.startsWith('--claim-evidence-manifest=')) {
      options.claimEvidenceManifestPath = arg.slice('--claim-evidence-manifest='.length);
      continue;
    }
    if (arg === '--policy-decision') {
      options.policyDecisionPath = readValue('--policy-decision');
      continue;
    }
    if (arg.startsWith('--policy-decision=')) {
      options.policyDecisionPath = arg.slice('--policy-decision='.length);
      continue;
    }
    if (arg === '--assurance-summary') {
      options.assuranceSummaryPath = readValue('--assurance-summary');
      continue;
    }
    if (arg.startsWith('--assurance-summary=')) {
      options.assuranceSummaryPath = arg.slice('--assurance-summary='.length);
      continue;
    }
    if (arg === '--claim-level-summary') {
      options.claimLevelSummaryPath = readValue('--claim-level-summary');
      continue;
    }
    if (arg.startsWith('--claim-level-summary=')) {
      options.claimLevelSummaryPath = arg.slice('--claim-level-summary='.length);
      continue;
    }
    if (arg === '--post-deploy-verify') {
      options.postDeployVerifyPath = readValue('--post-deploy-verify');
      continue;
    }
    if (arg.startsWith('--post-deploy-verify=')) {
      options.postDeployVerifyPath = arg.slice('--post-deploy-verify='.length);
      continue;
    }
    if (arg === '--repo') {
      options.repository = readValue('--repo');
      continue;
    }
    if (arg.startsWith('--repo=')) {
      options.repository = arg.slice('--repo='.length);
      continue;
    }
    if (arg === '--pr') {
      options.prNumber = Number(readValue('--pr'));
      continue;
    }
    if (arg.startsWith('--pr=')) {
      options.prNumber = Number(arg.slice('--pr='.length));
      continue;
    }
    if (arg === '--base-ref') {
      options.baseRef = readValue('--base-ref');
      continue;
    }
    if (arg.startsWith('--base-ref=')) {
      options.baseRef = arg.slice('--base-ref='.length);
      continue;
    }
    if (arg === '--head-ref') {
      options.headRef = readValue('--head-ref');
      continue;
    }
    if (arg.startsWith('--head-ref=')) {
      options.headRef = arg.slice('--head-ref='.length);
      continue;
    }
    if (arg === '--intent-summary') {
      options.intentSummary = readValue('--intent-summary');
      continue;
    }
    if (arg.startsWith('--intent-summary=')) {
      options.intentSummary = arg.slice('--intent-summary='.length);
      continue;
    }
    if (arg === '--labels') {
      options.labelsCsv = readValue('--labels');
      continue;
    }
    if (arg.startsWith('--labels=')) {
      options.labelsCsv = arg.slice('--labels='.length);
      continue;
    }
    if (arg === '--event-path') {
      options.eventPath = readValue('--event-path');
      continue;
    }
    if (arg.startsWith('--event-path=')) {
      options.eventPath = arg.slice('--event-path='.length);
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  const normalizedSchemaVersion = normalizeSchemaVersion(options.schemaVersion);
  options.schemaVersion = normalizedSchemaVersion;
  if (normalizedSchemaVersion === 'v2' && !options.dualWrite) {
    if (!options.outputJsonPathExplicit) {
      options.outputJsonPath = DEFAULT_V2_OUTPUT_JSON_PATH;
    }
    if (!options.outputMarkdownPathExplicit) {
      options.outputMarkdownPath = DEFAULT_V2_OUTPUT_MD_PATH;
    }
  }

  return options;
}

function printHelp() {
  process.stdout.write(
    `Change Package generator\n\n`
    + `Usage:\n`
    + `  node scripts/change-package/generate.mjs [options]\n\n`
    + `Options:\n`
    + `  --policy <path>               risk policy path (default: ${DEFAULT_POLICY_PATH})\n`
    + `  --output-json <path>          output JSON path (default: ${DEFAULT_OUTPUT_JSON_PATH})\n`
    + `  --output-md <path>            output Markdown path (default: ${DEFAULT_OUTPUT_MD_PATH})\n`
    + `  --schema-version <v1|v2>      generated contract version (default: v1)\n`
    + `  --dual-write                  write v1 plus v2 outputs using --v2-output-* paths\n`
    + `  --v2-output-json <path>       dual-write v2 JSON path (default: ${DEFAULT_V2_OUTPUT_JSON_PATH})\n`
    + `  --v2-output-md <path>         dual-write v2 Markdown path (default: ${DEFAULT_V2_OUTPUT_MD_PATH})\n`
    + `  --claim-evidence-manifest <path> claim-evidence-manifest/v1 input for v2 (default: ${DEFAULT_CLAIM_EVIDENCE_MANIFEST_PATH})\n`
    + `  --policy-decision <path>      policy-decision/v1 input for v2 (default: ${DEFAULT_POLICY_DECISION_PATH})\n`
    + `  --assurance-summary <path>    assurance-summary/v1 input for v2 (default: ${DEFAULT_ASSURANCE_SUMMARY_PATH})\n`
    + `  --claim-level-summary <path>  claim-level-summary/v1 input for v2 (default: ${DEFAULT_CLAIM_LEVEL_SUMMARY_PATH})\n`
    + `  --post-deploy-verify <path>   post-deploy verification input for v2 release controls (default: ${DEFAULT_POST_DEPLOY_VERIFY_PATH})\n`
    + `  --changed-files-file <path>   newline-separated changed files input\n`
    + `  --artifact-root <path>        root path for evidence existence checks (default: ${DEFAULT_ARTIFACT_ROOT})\n`
    + `  --mode <digest|detailed>      markdown detail level (default: ${DEFAULT_MODE})\n`
    + `  --repo <owner/repo>           repository override\n`
    + `  --pr <number>                 PR number override\n`
    + `  --base-ref <ref>              base branch override\n`
    + `  --head-ref <ref>              head branch override\n`
    + `  --intent-summary <text>       intent summary override\n`
    + `  --labels <csv>                labels override (comma-separated)\n`
    + `  --event-path <path>           GitHub event JSON path override\n`
    + `  --help, -h                    show help\n`,
  );
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function readJsonIfExists(filePath) {
  if (!filePath || !fs.existsSync(filePath)) {
    return null;
  }
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch {
    return null;
  }
}

function ensureArray(value) {
  return Array.isArray(value) ? value : [];
}

function ensureObject(value) {
  return value && typeof value === 'object' && !Array.isArray(value) ? value : {};
}

function uniqueStrings(values) {
  return [...new Set(
    ensureArray(values)
      .map((value) => String(value || '').trim())
      .filter(Boolean),
  )];
}

function normalizeAssuranceLevel(value, fallback = 'A0') {
  const candidate = String(value || '').trim().toUpperCase();
  return ASSURANCE_LEVELS.includes(candidate) ? candidate : fallback;
}

function assuranceLevelIndex(value) {
  const index = ASSURANCE_LEVELS.indexOf(normalizeAssuranceLevel(value));
  return index >= 0 ? index : 0;
}

function maxAssuranceLevel(values, fallback = 'A0') {
  const levels = ensureArray(values).map((value) => normalizeAssuranceLevel(value, fallback));
  if (levels.length === 0) return fallback;
  return ASSURANCE_LEVELS[Math.max(...levels.map(assuranceLevelIndex))];
}

function minAssuranceLevel(values, fallback = 'A0') {
  const levels = ensureArray(values).map((value) => normalizeAssuranceLevel(value, fallback));
  if (levels.length === 0) return fallback;
  return ASSURANCE_LEVELS[Math.min(...levels.map(assuranceLevelIndex))];
}

function oneLevelBelow(value) {
  const index = assuranceLevelIndex(value);
  return ASSURANCE_LEVELS[Math.max(0, index - 1)];
}

function normalizeCriticality(value) {
  const candidate = String(value || '').trim().toLowerCase();
  return ['low', 'medium', 'high', 'critical'].includes(candidate) ? candidate : 'medium';
}

function normalizeV2ClaimStatus(value, fallback = 'unresolved') {
  const candidate = String(value || '').trim().toLowerCase();
  return V2_CLAIM_STATUSES.has(candidate) ? candidate : fallback;
}

function normalizeDecisionResult(value, fallback = 'unassessed') {
  const candidate = String(value || '').trim().toLowerCase();
  return ['pass', 'waived', 'report-only', 'block', 'unassessed'].includes(candidate) ? candidate : fallback;
}

function normalizeDecisionMode(value, enforced = false) {
  const candidate = String(value || '').trim().toLowerCase();
  if (candidate === 'strict' || candidate === 'report-only') return candidate;
  return enforced ? 'strict' : 'unknown';
}

function normalizeV2ProofMethod(value) {
  const candidate = String(value || '').trim().toLowerCase();
  if (V2_PROOF_METHODS.has(candidate)) return candidate;
  if (candidate === 'manual' || candidate === 'other') return 'runtime';
  return 'spec';
}

function normalizeV2ProofStatus(value) {
  const candidate = String(value || '').trim().toLowerCase();
  if (V2_PROOF_STATUSES.has(candidate)) return candidate;
  if (candidate === 'unresolved') return 'open';
  return 'open';
}

function normalizeDate(value, fallback = '2099-12-31') {
  const candidate = String(value || '').trim();
  return /^\d{4}-\d{2}-\d{2}$/u.test(candidate) ? candidate : fallback;
}

function stripJsonPointer(artifactRef) {
  return String(artifactRef || '').split('#')[0].trim();
}

function normalizeArtifactRefs(values, fallback) {
  const refs = uniqueStrings(values)
    .map(stripJsonPointer)
    .filter(Boolean);
  return refs.length > 0 ? refs : [fallback].filter(Boolean);
}

function collectRequirementRefs(rawClaim) {
  const directRefs = [
    ...ensureArray(rawClaim?.requirementRefs),
    ...ensureArray(rawClaim?.requirements),
    ...ensureArray(rawClaim?.requirementIds),
  ];
  const specEvidenceRefs = ensureArray(rawClaim?.evidenceRefs)
    .filter((entry) => String(entry?.kind || '').trim().toLowerCase() === 'spec')
    .map((entry) => entry?.artifactPath || entry?.id);
  return uniqueStrings([...directRefs, ...specEvidenceRefs]);
}

function normalizeClaimDecision(rawDecision) {
  const decision = ensureObject(rawDecision);
  const result = normalizeDecisionResult(decision.result);
  const enforced = Boolean(decision.enforced);
  return {
    result,
    mode: normalizeDecisionMode(decision.mode, enforced),
    enforced,
    reason: String(decision.reason || 'No policy decision was linked for this claim.'),
  };
}

function loadOptionalJsonSource(id, filePath, description) {
  const payload = readJsonIfExists(filePath);
  return {
    id,
    path: filePath,
    description,
    present: Boolean(payload),
    payload,
  };
}

function inferV2StatusFromManifestClaim(claim) {
  const status = String(claim?.status || '').trim().toLowerCase();
  if (status === 'waived') return 'waived';
  if (status === 'unresolved' || status === 'partial') return 'unresolved';
  const proofRefs = ensureArray(claim?.proofObligationRefs);
  if (proofRefs.some((entry) => String(entry?.status || '').trim() === 'discharged')) {
    return 'model-checked';
  }
  const evidenceRefs = ensureArray(claim?.evidenceRefs);
  if (evidenceRefs.some((entry) => String(entry?.kind || '').trim() === 'proof')) {
    return 'model-checked';
  }
  if (evidenceRefs.some((entry) => String(entry?.kind || '').trim() === 'runtime')) {
    return 'runtime-mitigated';
  }
  return status === 'satisfied' ? 'tested' : 'unresolved';
}

function mapPolicyClaimResultToV2Status(result, status) {
  const normalizedResult = String(result || '').trim().toLowerCase();
  if (normalizedResult === 'waived') return 'waived';
  if (normalizedResult === 'block') return 'failed';
  if (normalizedResult === 'report-only') return 'unresolved';
  const normalizedStatus = String(status || '').trim().toLowerCase();
  if (normalizedStatus === 'waived') return 'waived';
  if (normalizedStatus === 'partial' || normalizedStatus === 'unresolved') return 'unresolved';
  if (V2_CLAIM_STATUSES.has(normalizedStatus)) return normalizedStatus;
  return 'satisfied';
}

function upsertClaim(claimsById, rawClaim) {
  const id = String(rawClaim?.id || rawClaim?.claimId || '').trim();
  if (!id) return null;
  const existing = claimsById.get(id) || {
    id,
    statement: `Assurance claim ${id}`,
    status: 'unresolved',
    criticality: 'medium',
    targetLevel: 'A0',
    achievedLevel: 'A0',
    requirementRefs: [],
    decision: normalizeClaimDecision(null),
    artifactRefs: [],
  };
  const merged = {
    ...existing,
    statement: String(rawClaim?.statement || existing.statement || `Assurance claim ${id}`),
    status: normalizeV2ClaimStatus(rawClaim?.status, existing.status),
    criticality: normalizeCriticality(rawClaim?.criticality || existing.criticality),
    targetLevel: normalizeAssuranceLevel(rawClaim?.targetLevel, existing.targetLevel),
    achievedLevel: normalizeAssuranceLevel(rawClaim?.achievedLevel, existing.achievedLevel),
    requirementRefs: uniqueStrings([
      ...ensureArray(existing.requirementRefs),
      ...collectRequirementRefs(rawClaim),
    ]),
    decision: rawClaim?.decision ? normalizeClaimDecision(rawClaim.decision) : existing.decision,
    artifactRefs: normalizeArtifactRefs([
      ...ensureArray(existing.artifactRefs),
      ...ensureArray(rawClaim?.artifactRefs),
    ], `artifacts/change-package/${id}.json`),
  };
  claimsById.set(id, merged);
  return merged;
}

function collectManifestArtifactRefs(claim, manifestPath) {
  return normalizeArtifactRefs([
    ...ensureArray(claim?.evidenceRefs).map((entry) => entry?.artifactPath),
    ...ensureArray(claim?.proofObligationRefs).map((entry) => entry?.artifactPath),
  ], manifestPath || DEFAULT_CLAIM_EVIDENCE_MANIFEST_PATH);
}

function ingestManifestForV2(claimsById, proofObligations, waivers, source) {
  const manifest = ensureObject(source.payload);
  for (const rawClaim of ensureArray(manifest.claims)) {
    const claim = upsertClaim(claimsById, {
      id: rawClaim?.id,
      statement: rawClaim?.statement,
      criticality: rawClaim?.criticality,
      status: inferV2StatusFromManifestClaim(rawClaim),
      targetLevel: rawClaim?.targetLevel,
      achievedLevel: rawClaim?.achievedLevel,
      requirementRefs: rawClaim?.requirementRefs,
      artifactRefs: collectManifestArtifactRefs(rawClaim, source.path),
    });
    if (!claim) continue;

    for (const rawObligation of ensureArray(rawClaim?.proofObligationRefs)) {
      const id = String(rawObligation?.id || '').trim();
      if (!id) continue;
      proofObligations.push({
        id,
        claimId: claim.id,
        method: normalizeV2ProofMethod(rawObligation?.method),
        status: normalizeV2ProofStatus(rawObligation?.status),
        artifactRefs: normalizeArtifactRefs([rawObligation?.artifactPath], claim.artifactRefs[0] || source.path),
      });
    }

    for (const rawWaiver of ensureArray(rawClaim?.waiverRefs)) {
      waivers.push({
        owner: String(rawWaiver?.owner || 'unknown'),
        expires: normalizeDate(rawWaiver?.expires),
        reason: String(rawWaiver?.reason || `Waiver recorded for claim ${claim.id}`),
        relatedClaimIds: [claim.id],
        evidenceRefs: normalizeArtifactRefs([rawWaiver?.artifactPath, rawWaiver?.temporaryOverridePath, source.path], source.path),
      });
    }
  }
}

function ingestAssuranceSummaryForV2(claimsById, source) {
  const assuranceSummary = ensureObject(source.payload);
  for (const rawClaim of ensureArray(assuranceSummary.claims)) {
    const claimId = String(rawClaim?.claimId || rawClaim?.id || '').trim();
    if (!claimId || claimsById.has(claimId)) continue;
    upsertClaim(claimsById, {
      id: claimId,
      statement: rawClaim?.statement,
      criticality: rawClaim?.criticality,
      status: String(rawClaim?.status || '').trim() === 'satisfied' ? 'tested' : 'unresolved',
      targetLevel: rawClaim?.targetLevel,
      achievedLevel: inferAssuranceSummaryAchievedLevel(rawClaim),
      requirementRefs: rawClaim?.requirementRefs,
      artifactRefs: ensureArray(rawClaim?.evidence).map((entry) => entry?.artifactPath),
    });
  }
}

function ingestClaimLevelSummaryForV2(claimsById, proofObligations, waivers, assumptions, runtimeControls, source) {
  const summary = ensureObject(source.payload);
  for (const rawClaim of ensureArray(summary.claims)) {
    const claimId = String(rawClaim?.claimId || rawClaim?.id || '').trim();
    if (!claimId) continue;
    const artifactRefs = [
      ...ensureArray(rawClaim?.evidenceRefs).map((entry) => entry?.artifactPath),
      source.path,
    ];
    const claim = upsertClaim(claimsById, {
      id: claimId,
      statement: rawClaim?.statement,
      criticality: rawClaim?.criticality,
      status: rawClaim?.state,
      targetLevel: rawClaim?.targetLevel,
      achievedLevel: rawClaim?.achievedLevel,
      requirementRefs: collectRequirementRefs(rawClaim),
      decision: rawClaim?.decision,
      artifactRefs,
    });
    if (!claim) continue;

    for (const rawEvidence of ensureArray(rawClaim?.evidenceRefs)) {
      const kind = String(rawEvidence?.kind || '').trim().toLowerCase();
      if (!['proof', 'model', 'runtime'].includes(kind)) continue;
      const evidenceId = String(rawEvidence?.id || `${claim.id}:${kind}:${proofObligations.length}`).trim();
      if (!evidenceId) continue;
      proofObligations.push({
        id: `${evidenceId}:obligation`,
        claimId: claim.id,
        method: normalizeV2ProofMethod(kind),
        status: String(rawEvidence?.status || '').trim().toLowerCase() === 'observed' ? 'discharged' : 'open',
        artifactRefs: normalizeArtifactRefs([rawEvidence?.artifactPath], source.path),
      });
    }

    for (const rawWaiver of ensureArray(rawClaim?.waiverRefs)) {
      waivers.push({
        owner: String(rawWaiver?.owner || 'unknown'),
        expires: normalizeDate(rawWaiver?.expires),
        reason: String(rawWaiver?.reason || `Waiver recorded for claim ${claim.id}`),
        relatedClaimIds: [claim.id],
        evidenceRefs: normalizeArtifactRefs([rawWaiver?.temporaryOverridePath, rawWaiver?.artifactPath, source.path], source.path),
      });
    }

    for (const rawAssumption of ensureArray(rawClaim?.assumptions)) {
      assumptions.push({
        id: String(rawAssumption?.id || `${claim.id}:assumption:${assumptions.length}`),
        statement: String(rawAssumption?.statement || `Assumption linked to ${claim.id}.`),
        owner: String(rawAssumption?.owner || 'unknown'),
        evidenceRefs: normalizeArtifactRefs([rawAssumption?.artifactPath, source.path], source.path),
        status: String(rawAssumption?.status || ''),
        claimId: claim.id,
      });
    }

    for (const rawControl of ensureArray(rawClaim?.runtimeControls)) {
      runtimeControls.push({
        id: String(rawControl?.id || `${claim.id}:runtime-control:${runtimeControls.length}`),
        kind: String(rawControl?.kind || 'other'),
        description: String(rawControl?.description || `Runtime control linked to ${claim.id}.`),
        artifactPath: rawControl?.artifactPath,
        claimId: claim.id,
      });
    }
  }
}

function inferAssuranceSummaryAchievedLevel(claim) {
  const targetLevel = normalizeAssuranceLevel(claim?.targetLevel);
  const status = String(claim?.status || '').trim().toLowerCase();
  if (status === 'warning' || status === 'partial' || status === 'unresolved') {
    return oneLevelBelow(targetLevel);
  }
  return targetLevel;
}

function collectSourceClaimStatuses(manifestClaims, assuranceClaims) {
  const statusesByClaimId = new Map();
  for (const rawClaim of [
    ...ensureArray(manifestClaims),
    ...ensureArray(assuranceClaims),
  ]) {
    const claimId = String(rawClaim?.id || rawClaim?.claimId || '').trim();
    const status = String(rawClaim?.status || '').trim().toLowerCase();
    if (!claimId || !status) continue;

    const existing = statusesByClaimId.get(claimId);
    if (existing === 'unresolved') continue;
    const normalizedStatus = status === 'warning' ? 'partial' : status;
    if (normalizedStatus === 'unresolved' || (normalizedStatus === 'partial' && !existing)) {
      statusesByClaimId.set(claimId, normalizedStatus);
      continue;
    }
    if (!existing) {
      statusesByClaimId.set(claimId, normalizedStatus);
    }
  }
  return statusesByClaimId;
}

function ingestPolicyDecisionForV2(claimsById, waivers, source) {
  const assurance = ensureObject(source.payload?.evaluation?.assurance);
  for (const rawClaim of ensureArray(assurance.claims)) {
    const claimId = String(rawClaim?.claimId || '').trim();
    if (!claimId) continue;
    upsertClaim(claimsById, {
      id: claimId,
      status: mapPolicyClaimResultToV2Status(rawClaim?.result, rawClaim?.status),
      artifactRefs: [source.path],
    });
  }
  for (const rawWaiver of ensureArray(assurance.waivers)) {
    const claimId = String(rawWaiver?.claimId || '').trim();
    if (!claimId) continue;
    waivers.push({
      owner: String(rawWaiver?.owner || 'unknown'),
      expires: normalizeDate(rawWaiver?.expires),
      reason: String(rawWaiver?.reason || `Policy decision waiver for claim ${claimId}`),
      relatedClaimIds: [claimId],
      evidenceRefs: normalizeArtifactRefs([source.path], source.path),
    });
  }
}

function dedupeProofObligations(entries) {
  const seen = new Set();
  const result = [];
  for (const entry of entries) {
    const key = `${entry.id}::${entry.claimId}`;
    if (seen.has(key)) continue;
    seen.add(key);
    result.push(entry);
  }
  return result.sort((left, right) => `${left.claimId}:${left.id}`.localeCompare(`${right.claimId}:${right.id}`));
}

function dedupeWaivers(entries) {
  const seen = new Set();
  const result = [];
  for (const entry of entries) {
    const relatedClaimIds = uniqueStrings(entry.relatedClaimIds);
    if (relatedClaimIds.length === 0) continue;
    const normalized = {
      owner: String(entry.owner || 'unknown'),
      expires: normalizeDate(entry.expires),
      reason: String(entry.reason || 'Change-package v2 waiver'),
      relatedClaimIds,
      evidenceRefs: normalizeArtifactRefs(entry.evidenceRefs, DEFAULT_CLAIM_LEVEL_SUMMARY_PATH),
    };
    const key = `${normalized.owner}::${normalized.expires}::${normalized.reason}::${normalized.relatedClaimIds.join(',')}`;
    if (seen.has(key)) continue;
    seen.add(key);
    result.push(normalized);
  }
  return result.sort((left, right) => left.relatedClaimIds.join(',').localeCompare(right.relatedClaimIds.join(',')));
}

function buildV2Evidence(baseEvidence, sources) {
  const sourceItems = sources.map((source) => ({
    id: source.id,
    path: source.path,
    description: source.description,
    present: source.present,
  }));
  const items = [
    ...baseEvidence.items,
    ...sourceItems,
  ];
  const presentCount = items.filter((item) => item.present).length;
  return {
    ...baseEvidence,
    items,
    presentCount,
    missingCount: items.length - presentCount,
  };
}

function summarizeClaimStatuses(claims) {
  const summary = new Map();
  for (const claim of claims) {
    summary.set(claim.status, (summary.get(claim.status) || 0) + 1);
  }
  return summary;
}

function buildV2Assurance(claims, manifestSource, policyDecisionSource, assuranceSummarySource, claimLevelSummarySource) {
  const manifestClaims = ensureArray(manifestSource.payload?.claims);
  const assuranceClaims = ensureArray(assuranceSummarySource.payload?.claims);
  const claimLevelClaims = ensureArray(claimLevelSummarySource.payload?.claims);
  const targetLevel = maxAssuranceLevel([
    ...manifestClaims.map((claim) => claim?.targetLevel),
    ...assuranceClaims.map((claim) => claim?.targetLevel),
    ...claimLevelClaims.map((claim) => claim?.targetLevel),
    ...claims.map((claim) => claim?.targetLevel),
  ]);
  const achievedLevel = minAssuranceLevel([
    ...manifestClaims.map((claim) => claim?.achievedLevel),
    ...assuranceClaims.map(inferAssuranceSummaryAchievedLevel),
    ...claimLevelClaims.map((claim) => claim?.achievedLevel),
    ...claims.map((claim) => claim?.achievedLevel),
  ], targetLevel);
  const policyAssurance = ensureObject(policyDecisionSource.payload?.evaluation?.assurance);
  const policyResult = String(policyAssurance.result || '').trim().toLowerCase();
  const manifestStatuses = manifestClaims.map((claim) => String(claim?.status || '').trim().toLowerCase()).filter(Boolean);
  const sourceStatusesByClaimId = collectSourceClaimStatuses(manifestClaims, assuranceClaims);
  const sourceStatuses = [...sourceStatusesByClaimId.values()];
  const generatedUnresolvedClaims = claims
    .filter((claim) => claim.status === 'unresolved')
    .filter((claim) => sourceStatusesByClaimId.get(claim.id) !== 'partial');

  let status = 'unassessed';
  const claimStatusSummary = summarizeClaimStatuses(claims);
  if (claimStatusSummary.get('failed') > 0 || policyResult === 'block') {
    status = 'failed';
  } else if (claims.length > 0 && claims.every((claim) => claim.status === 'not-applicable')) {
    status = 'not-applicable';
  } else if (sourceStatuses.includes('unresolved') || generatedUnresolvedClaims.length > 0) {
    status = 'unresolved';
  } else if (policyResult === 'report-only' || manifestStatuses.includes('partial') || sourceStatuses.includes('partial')) {
    status = 'partial';
  } else if (policyResult === 'waived') {
    status = 'waived';
  } else if (claims.length > 0 && claims.every((claim) => claim.status === 'waived')) {
    status = 'waived';
  } else if (claims.length > 0 || policyResult === 'pass' || policyResult === 'waived') {
    status = 'satisfied';
  }

  return {
    targetLevel,
    achievedLevel,
    status,
  };
}

function inferChangedRequirementRefs(changedFiles) {
  return uniqueStrings(changedFiles.filter((filePath) => {
    const normalized = String(filePath || '').trim().toLowerCase();
    return normalized.startsWith('requirements/')
      || normalized.startsWith('reqs/')
      || normalized.includes('/requirements/')
      || normalized.startsWith('spec/')
      || normalized.startsWith('docs/product/')
      || normalized.startsWith('docs/requirements/');
  }));
}

function buildV2Requirements(changedFiles, claims) {
  return {
    changedRefs: inferChangedRequirementRefs(changedFiles),
    claimRefs: claims
      .filter((claim) => ensureArray(claim.requirementRefs).length > 0)
      .map((claim) => ({
        claimId: claim.id,
        refs: uniqueStrings(claim.requirementRefs),
      }))
      .sort((left, right) => left.claimId.localeCompare(right.claimId)),
  };
}

function mapEvidenceStatusToLaneStatus(status) {
  const normalized = String(status || '').trim().toLowerCase();
  if (normalized === 'failed') return 'fail';
  if (normalized === 'missing' || normalized === 'stale') return 'warn';
  return 'pass';
}

function mergeLaneStatus(current, next) {
  const rank = { missing: 0, pass: 1, warn: 2, fail: 3 };
  return rank[next] > rank[current] ? next : current;
}

function buildValidationLanes(claimLevelSummarySource, baseEvidence) {
  const lanesById = new Map();
  for (const item of ensureArray(baseEvidence.items)) {
    const status = item.present ? 'pass' : 'missing';
    lanesById.set(item.id, {
      id: item.id,
      status,
      evidenceRefs: [item.path],
    });
  }
  for (const claim of ensureArray(claimLevelSummarySource.payload?.claims)) {
    for (const evidence of [
      ...ensureArray(claim?.evidenceRefs),
      ...ensureArray(claim?.missingEvidenceRefs).map((entry) => ({
        ...entry,
        kind: entry?.expectedKind,
        status: 'missing',
        artifactPath: claimLevelSummarySource.path,
      })),
    ]) {
      const laneId = String(evidence?.kind || evidence?.expectedKind || 'other').trim().toLowerCase() || 'other';
      const laneStatus = mapEvidenceStatusToLaneStatus(evidence?.status);
      const existing = lanesById.get(laneId) || { id: laneId, status: 'pass', evidenceRefs: [] };
      existing.status = mergeLaneStatus(existing.status, laneStatus);
      existing.evidenceRefs = uniqueStrings([...existing.evidenceRefs, evidence?.artifactPath]);
      lanesById.set(laneId, existing);
    }
  }
  return [...lanesById.values()].sort((left, right) => left.id.localeCompare(right.id));
}

function buildPolicyDecisionSummary(policyDecisionSource) {
  const assurance = ensureObject(policyDecisionSource.payload?.evaluation?.assurance);
  const result = normalizeDecisionResult(assurance.result);
  const enforced = String(assurance.mode || '').trim().toLowerCase() === 'strict' || result === 'block';
  return {
    present: policyDecisionSource.present,
    sourceArtifactPath: policyDecisionSource.present ? policyDecisionSource.path : null,
    result,
    mode: policyDecisionSource.present ? normalizeDecisionMode(assurance.mode, enforced) : 'unknown',
    enforced,
    reason: policyDecisionSource.present
      ? `Policy decision assurance result is ${result}.`
      : 'No policy-decision/v1 artifact was available when the change package was generated.',
    warnings: ensureArray(assurance.warnings).map(String),
    errors: ensureArray(assurance.errors).map(String),
  };
}

function buildReleaseControls(baseChangePackage, postDeploySource) {
  const postDeployChecks = postDeploySource.present
    ? [postDeploySource.path]
    : ['post-deploy-verify workflow or release verification artifact required before production rollout'];
  return {
    preDeployChecks: uniqueStrings(baseChangePackage.reproducibility.commands),
    postDeployChecks,
    rollbackSignals: uniqueStrings([
      ...ensureArray(baseChangePackage.monitoringPlan.alerts),
      'post-deploy-verify.status=fail',
    ]),
  };
}

function buildResidualRisks(claims, assumptions) {
  const risks = [];
  for (const claim of claims) {
    if (!['failed', 'unresolved', 'runtime-mitigated', 'waived'].includes(claim.status)) continue;
    risks.push({
      id: `claim:${claim.id}:${claim.status}`,
      statement: `${claim.status} claim requires human review: ${claim.statement}`,
      severity: normalizeCriticality(claim.criticality),
      source: 'change-package/v2 claim status',
      claimIds: [claim.id],
    });
  }
  for (const assumption of assumptions) {
    if (!['needs-validation', 'residual-risk'].includes(String(assumption.status || ''))) continue;
    risks.push({
      id: `assumption:${assumption.id}`,
      statement: assumption.statement,
      severity: 'medium',
      source: 'claim-level-summary/v1 assumption',
      owner: assumption.owner,
      claimIds: [assumption.claimId].filter(Boolean),
    });
  }
  const seen = new Set();
  return risks.filter((risk) => {
    if (seen.has(risk.id)) return false;
    seen.add(risk.id);
    return true;
  }).sort((left, right) => left.id.localeCompare(right.id));
}

function toPositiveInt(value) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) return null;
  const truncated = Math.trunc(parsed);
  if (truncated <= 0) return null;
  return truncated;
}

function runGit(args) {
  try {
    return execFileSync('git', args, { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim();
  } catch {
    return '';
  }
}

function readChangedFilesFromFile(filePath) {
  if (!filePath) return [];
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) {
    throw new Error(`changed files file not found: ${resolved}`);
  }
  return fs.readFileSync(resolved, 'utf8')
    .split('\n')
    .map((line) => line.trim())
    .filter(Boolean);
}

function readChangedFilesFromGit(baseRef) {
  const insideGit = runGit(['rev-parse', '--is-inside-work-tree']);
  if (insideGit !== 'true') return [];

  if (baseRef) {
    // Shallow checkout in CI may not have base ref. Fetch once and ignore failures.
    runGit(['fetch', '--no-tags', '--depth=1', 'origin', baseRef]);
    const fromBase = runGit(['diff', '--name-only', '--diff-filter=ACMR', `origin/${baseRef}...HEAD`]);
    if (fromBase) {
      return fromBase.split('\n').map((entry) => entry.trim()).filter(Boolean);
    }
  }

  const fromLastCommit = runGit(['diff', '--name-only', '--diff-filter=ACMR', 'HEAD~1']);
  if (!fromLastCommit) {
    return [];
  }
  return fromLastCommit.split('\n').map((entry) => entry.trim()).filter(Boolean);
}

function resolveChangedFiles(options, eventPayload, baseRef) {
  const fromFile = readChangedFilesFromFile(options.changedFilesPath);
  if (fromFile.length > 0) {
    return toUniqueSorted(fromFile);
  }

  const envChangedFiles = parseChangedFilesEnv(process.env.CHANGE_PACKAGE_CHANGED_FILES || '');
  if (envChangedFiles.length > 0) {
    return toUniqueSorted(envChangedFiles);
  }

  const payloadChangedFiles = parseChangedFilesEnv(eventPayload?.inputs?.changed_files || '');
  if (payloadChangedFiles.length > 0) {
    return toUniqueSorted(payloadChangedFiles);
  }

  return toUniqueSorted(readChangedFilesFromGit(baseRef));
}

function inferAreaFromFile(filePath) {
  const normalized = String(filePath || '').replace(/\\/g, '/');
  if (!normalized) return 'unknown';
  if (normalized === 'README.md' || normalized.startsWith('docs/')) return 'docs';
  if (normalized === 'package.json' || normalized.endsWith('/package.json') || normalized.endsWith('lock.yaml') || normalized.endsWith('lock.json') || normalized.endsWith('.lock')) {
    return 'dependencies';
  }
  if (normalized.startsWith('.github/workflows/') || normalized.startsWith('scripts/ci/')) return 'ci';
  if (normalized.startsWith('policy/')) return 'policy';
  if (normalized.startsWith('schema/')) return 'schema';
  if (normalized.startsWith('spec/')) return 'spec';
  if (normalized.startsWith('src/')) return 'source';
  if (normalized.startsWith('tests/')) return 'tests';
  if (normalized.startsWith('scripts/')) return 'scripts';
  const [segment] = normalized.split('/');
  return segment || 'unknown';
}

function inferScopeAreas(changedFiles) {
  if (!Array.isArray(changedFiles) || changedFiles.length === 0) {
    return ['unknown'];
  }
  return toUniqueSorted(changedFiles.map(inferAreaFromFile));
}

function resolveRepository(options, eventPayload) {
  const explicit = String(options.repository || '').trim();
  if (explicit) return explicit;
  const fromEnv = String(process.env.GITHUB_REPOSITORY || '').trim();
  if (fromEnv) return fromEnv;
  const fromPayload = String(eventPayload?.repository?.full_name || '').trim();
  if (fromPayload) return fromPayload;
  return null;
}

function resolvePrNumber(options, eventPayload) {
  const fromArgs = toPositiveInt(options.prNumber);
  if (fromArgs) return fromArgs;
  const fromEnv = toPositiveInt(process.env.PR_NUMBER);
  if (fromEnv) return fromEnv;
  return toPositiveInt(
    eventPayload?.pull_request?.number
    || eventPayload?.workflow_run?.pull_requests?.[0]?.number
    || eventPayload?.issue?.number
    || eventPayload?.number
    || eventPayload?.inputs?.pr_number,
  );
}

function resolveBaseRef(options, eventPayload) {
  const fromArgs = String(options.baseRef || '').trim();
  if (fromArgs) return fromArgs;
  const fromEnv = String(process.env.GITHUB_BASE_REF || '').trim();
  if (fromEnv) return fromEnv;
  const fromPayload = String(eventPayload?.pull_request?.base?.ref || '').trim();
  if (fromPayload) return fromPayload;
  return 'main';
}

function resolveHeadRef(options, eventPayload) {
  const fromArgs = String(options.headRef || '').trim();
  if (fromArgs) return fromArgs;
  const fromEnv = String(process.env.GITHUB_HEAD_REF || '').trim();
  if (fromEnv) return fromEnv;
  const fromPayload = String(eventPayload?.pull_request?.head?.ref || '').trim();
  if (fromPayload) return fromPayload;
  const fromGit = runGit(['rev-parse', '--abbrev-ref', 'HEAD']);
  if (fromGit) return fromGit;
  return 'unknown';
}

function resolveCurrentLabels(options, eventPayload) {
  const fromArgs = parseLabelsCsv(options.labelsCsv);
  if (fromArgs.length > 0) return normalizeLabelNames(fromArgs);

  const fromEnv = parseLabelsCsv(process.env.CHANGE_PACKAGE_LABELS || '');
  if (fromEnv.length > 0) return normalizeLabelNames(fromEnv);

  const fromPayload = Array.isArray(eventPayload?.pull_request?.labels)
    ? eventPayload.pull_request.labels.map((label) => label?.name).filter(Boolean)
    : [];
  return normalizeLabelNames(fromPayload);
}

function resolveIntentSummary(options, eventPayload, changedFileCount) {
  const explicit = String(options.intentSummary || '').trim();
  if (explicit) return explicit;

  const fromEnv = String(process.env.CHANGE_PACKAGE_INTENT_SUMMARY || '').trim();
  if (fromEnv) return fromEnv;

  const title = String(eventPayload?.pull_request?.title || '').trim();
  if (title) return title;

  const body = String(eventPayload?.pull_request?.body || '')
    .split('\n')
    .map((line) => line.trim())
    .find(Boolean);
  if (body) return body;

  return changedFileCount > 0
    ? `Update ${changedFileCount} file(s) with policy-bound risk/evidence tracking.`
    : 'Generate policy-bound risk/evidence package.';
}

function buildEvidence(artifactRoot) {
  const resolvedRoot = path.resolve(artifactRoot || '.');
  const items = EVIDENCE_CATALOG.map((item) => {
    const absolutePath = path.resolve(resolvedRoot, item.path);
    return {
      id: item.id,
      path: item.path,
      description: item.description,
      present: fs.existsSync(absolutePath),
    };
  });
  const presentCount = items.filter((item) => item.present).length;
  return {
    artifactRoot: path.relative(process.cwd(), resolvedRoot) || '.',
    items,
    presentCount,
    missingCount: items.length - presentCount,
  };
}

function pushUnique(target, value) {
  if (!value) return;
  if (!target.includes(value)) target.push(value);
}

function buildReproducibilityCommands(requiredLabels) {
  const commands = ['pnpm run verify:lite'];

  if (requiredLabels.includes('run-ci-extended')) {
    pushUnique(commands, 'pnpm run test:ci:extended');
  }
  if (requiredLabels.includes('run-security')) {
    pushUnique(commands, 'pnpm run security:integrated:quick');
  }
  if (requiredLabels.includes('enforce-artifacts')) {
    pushUnique(commands, ENFORCE_ARTIFACTS_STRICT_COMMAND);
  }
  if (requiredLabels.includes('enforce-testing')) {
    pushUnique(commands, 'pnpm run test:ci:lite');
  }
  if (requiredLabels.includes('enforce-context-pack')) {
    pushUnique(commands, 'pnpm run context-pack:e2e-fixture');
  }

  return commands;
}

function buildMonitoringPlan(requiredLabels) {
  const signals = ['policy-gate.status', 'verify-lite.status', 'harness-health.severity'];
  const alerts = [];

  if (requiredLabels.includes('run-security')) {
    pushUnique(signals, 'security.status');
    pushUnique(alerts, 'security-gate-failed');
  }
  if (requiredLabels.includes('run-ci-extended')) {
    pushUnique(signals, 'ci-extended.status');
    pushUnique(alerts, 'ci-extended-failed');
  }
  if (requiredLabels.includes('enforce-artifacts')) {
    pushUnique(signals, 'artifacts-validate.status');
    pushUnique(alerts, 'artifacts-missing');
  }
  if (requiredLabels.includes('enforce-testing')) {
    pushUnique(signals, 'testing-ddd.status');
    pushUnique(alerts, 'testing-gate-failed');
  }
  if (requiredLabels.includes('enforce-context-pack')) {
    pushUnique(signals, 'context-pack-e2e.status');
    pushUnique(alerts, 'context-pack-gate-failed');
  }

  return { signals, alerts };
}

function buildExceptions({
  missingRequiredLabels,
  selectedRiskLabel,
  inferredRiskLabel,
  currentRiskLabels,
  evidence,
}) {
  const exceptions = [];
  if (missingRequiredLabels.length > 0) {
    exceptions.push({
      code: 'missing-required-labels',
      message: `Missing required labels: ${missingRequiredLabels.join(', ')}`,
    });
  }
  if (currentRiskLabels.length === 0) {
    exceptions.push({
      code: 'missing-risk-label',
      message: 'No risk label is present on the pull request.',
    });
  }
  if (currentRiskLabels.length > 1) {
    exceptions.push({
      code: 'multiple-risk-labels',
      message: `Multiple risk labels are present: ${currentRiskLabels.join(', ')}`,
    });
  }
  if (selectedRiskLabel !== inferredRiskLabel) {
    exceptions.push({
      code: 'risk-label-mismatch',
      message: `Selected risk label (${selectedRiskLabel}) differs from inferred (${inferredRiskLabel})`,
    });
  }
  if (evidence.presentCount === 0) {
    exceptions.push({
      code: 'evidence-empty',
      message: 'No evidence artifact is present under artifact root.',
    });
  }
  return exceptions;
}

function escapeMarkdownCell(value) {
  return String(value ?? '')
    .replace(/\\/gu, '\\\\')
    .replace(/\|/gu, '\\|')
    .replace(/\r?\n/gu, ' ')
    .trim();
}

function renderTable(headers, rows) {
  if (rows.length === 0) {
    return '- (none)';
  }
  return [
    `| ${headers.map(escapeMarkdownCell).join(' | ')} |`,
    `| ${headers.map(() => '---').join(' | ')} |`,
    ...rows.map((row) => `| ${row.map(escapeMarkdownCell).join(' | ')} |`),
  ].join('\n');
}

function renderStatusCounts(claims) {
  const counts = summarizeClaimStatuses(claims);
  return ['satisfied', 'tested', 'model-checked', 'proved', 'runtime-mitigated', 'waived', 'unresolved', 'failed', 'not-applicable']
    .map((status) => `${status}=${counts.get(status) || 0}`)
    .join(', ');
}

function renderV2DetailedSections(changePackage, outputJsonPath) {
  if (changePackage.schemaVersion !== 'change-package/v2') {
    return [];
  }
  const claims = ensureArray(changePackage.claims);
  const proofObligations = ensureArray(changePackage.proofObligations);
  const waivers = ensureArray(changePackage.waivers);
  const residualRisks = ensureArray(changePackage.residualRisks);
  return [
    '### Proof-carrying Assurance',
    `- evidence package: \`${outputJsonPath || DEFAULT_V2_OUTPUT_JSON_PATH}\``,
    `- target/achieved/status: ${changePackage.assurance.targetLevel}/${changePackage.assurance.achievedLevel}/${changePackage.assurance.status}`,
    `- claim states: ${renderStatusCounts(claims)}`,
    `- policy decision: ${changePackage.policyDecision.result} (${changePackage.policyDecision.mode}, enforced=${changePackage.policyDecision.enforced})`,
    `- changed requirement refs: ${ensureArray(changePackage.requirements.changedRefs).length > 0 ? changePackage.requirements.changedRefs.join(', ') : '(none)'}`,
    '',
    '### Claims',
    renderTable(
      ['id', 'status', 'target', 'achieved', 'criticality', 'requirements', 'artifactRefs', 'statement'],
      claims.map((claim) => [
        claim.id,
        claim.status,
        claim.targetLevel,
        claim.achievedLevel,
        claim.criticality,
        ensureArray(claim.requirementRefs).join(', ') || '(none)',
        String(ensureArray(claim.artifactRefs).length),
        claim.statement,
      ]),
    ),
    '',
    '### Proof Obligations',
    renderTable(
      ['id', 'claimId', 'method', 'status', 'artifactRefs'],
      proofObligations.map((obligation) => [
        obligation.id,
        obligation.claimId,
        obligation.method,
        obligation.status,
        String(ensureArray(obligation.artifactRefs).length),
      ]),
    ),
    '',
    '### Validation Lanes',
    renderTable(
      ['id', 'status', 'evidenceRefs'],
      ensureArray(changePackage.validationLanes).map((lane) => [
        lane.id,
        lane.status,
        String(ensureArray(lane.evidenceRefs).length),
      ]),
    ),
    '',
    '### Release / Post-deploy Controls',
    `- pre-deploy checks: ${ensureArray(changePackage.releaseControls.preDeployChecks).length}`,
    `- post-deploy checks: ${ensureArray(changePackage.releaseControls.postDeployChecks).join(', ') || '(none)'}`,
    `- rollback signals: ${ensureArray(changePackage.releaseControls.rollbackSignals).join(', ') || '(none)'}`,
    '',
    '### Residual Risks',
    renderTable(
      ['id', 'severity', 'claimIds', 'statement'],
      residualRisks.map((risk) => [
        risk.id,
        risk.severity,
        ensureArray(risk.claimIds).join(', '),
        risk.statement,
      ]),
    ),
    '',
    '### Waivers',
    renderTable(
      ['owner', 'expires', 'relatedClaimIds', 'evidenceRefs', 'reason'],
      waivers.map((waiver) => [
        waiver.owner,
        waiver.expires,
        ensureArray(waiver.relatedClaimIds).join(', '),
        String(ensureArray(waiver.evidenceRefs).length),
        waiver.reason,
      ]),
    ),
    '',
  ];
}

function renderV2DigestSuffix(changePackage, outputJsonPath) {
  if (changePackage.schemaVersion !== 'change-package/v2') {
    return '';
  }
  return ` | assurance=${changePackage.assurance.targetLevel}/${changePackage.assurance.achievedLevel}/${changePackage.assurance.status}`
    + ` | claims=${ensureArray(changePackage.claims).length}`
    + ` | states(${renderStatusCounts(ensureArray(changePackage.claims))})`
    + ` | proofObligations=${ensureArray(changePackage.proofObligations).length}`
    + ` | waivers=${ensureArray(changePackage.waivers).length}`
    + ` | evidencePackage=${outputJsonPath || DEFAULT_V2_OUTPUT_JSON_PATH}`;
}

function renderDetailedMarkdown(changePackage, outputJsonPath) {
  const risk = changePackage.risk;
  const evidenceRows = changePackage.evidence.items
    .map((item) => `| ${item.id} | \`${item.path}\` | ${item.present ? 'yes' : 'no'} |`)
    .join('\n');
  const forceTriggers = risk.rationale.forceHighRiskTriggers.length > 0
    ? risk.rationale.forceHighRiskTriggers
      .map((item) => `${item.condition} (${item.ruleId})`)
      .join(', ')
    : '(none)';
  const exceptions = changePackage.exceptions.length > 0
    ? changePackage.exceptions.map((item) => `- ${item.code}: ${item.message}`).join('\n')
    : '- (none)';

  return [
    '## Change Package',
    `- schema: \`${changePackage.schemaVersion}\``,
    `- generatedAt: ${changePackage.generatedAt}`,
    `- policy: \`${changePackage.policyPath}\``,
    '',
    '### Intent',
    `- ${changePackage.intent.summary}`,
    '',
    '### Scope',
    `- changed files: ${changePackage.scope.changedFileCount}`,
    `- areas: ${changePackage.scope.areas.join(', ')}`,
    '',
    '### Risk',
    `- selected: ${risk.selected}`,
    `- inferred: ${risk.inferred}`,
    `- isHighRisk: ${risk.isHighRisk}`,
    `- required labels: ${risk.requiredLabels.length > 0 ? risk.requiredLabels.join(', ') : '(none)'}`,
    `- missing required labels: ${risk.missingRequiredLabels.length > 0 ? risk.missingRequiredLabels.join(', ') : '(none)'}`,
    `- high-risk path matches: ${risk.rationale.highRiskPathMatches.length > 0 ? risk.rationale.highRiskPathMatches.join(', ') : '(none)'}`,
    `- force-high triggers: ${forceTriggers}`,
    '',
    '### Evidence',
    `- present/missing: ${changePackage.evidence.presentCount}/${changePackage.evidence.missingCount}`,
    '',
    '| id | path | present |',
    '| --- | --- | --- |',
    evidenceRows,
    '',
    ...renderV2DetailedSections(changePackage, outputJsonPath),
    '### Reproducibility',
    ...changePackage.reproducibility.commands.map((command) => `- \`${command}\``),
    '',
    '### Rollout Plan',
    `- strategy: ${changePackage.rolloutPlan.strategy}`,
    ...changePackage.rolloutPlan.notes.map((note) => `- ${note}`),
    '',
    '### Monitoring Plan',
    `- signals: ${changePackage.monitoringPlan.signals.join(', ') || '(none)'}`,
    `- alerts: ${changePackage.monitoringPlan.alerts.join(', ') || '(none)'}`,
    '',
    '### Exceptions',
    exceptions,
    '',
  ].join('\n');
}

function renderDigestMarkdown(changePackage, outputJsonPath) {
  const risk = changePackage.risk;
  return [
    '### Change Package',
    `- risk=${risk.selected} (inferred=${risk.inferred}) | files=${changePackage.scope.changedFileCount} | areas=${changePackage.scope.areas.join(', ')} | evidence=${changePackage.evidence.presentCount}/${changePackage.evidence.missingCount} present/missing${renderV2DigestSuffix(changePackage, outputJsonPath)}`,
    `- required labels: ${risk.requiredLabels.length > 0 ? risk.requiredLabels.join(', ') : '(none)'} | missing: ${risk.missingRequiredLabels.length > 0 ? risk.missingRequiredLabels.join(', ') : '(none)'}`,
    `- reproducibility: ${changePackage.reproducibility.commands.map((command) => `\`${command}\``).join(', ')}`,
    '',
  ].join('\n');
}

function renderMarkdown(changePackage, mode, outputJsonPath) {
  if (mode === 'digest') {
    return renderDigestMarkdown(changePackage, outputJsonPath);
  }
  return renderDetailedMarkdown(changePackage, outputJsonPath);
}

function isModeDigest(mode) {
  return String(mode || '').trim().toLowerCase() === 'digest';
}

function buildChangePackage(options, eventPayload) {
  const policy = loadRiskPolicy(options.policyPath);
  const repository = resolveRepository(options, eventPayload);
  const prNumber = resolvePrNumber(options, eventPayload);
  const baseRef = resolveBaseRef(options, eventPayload);
  const headRef = resolveHeadRef(options, eventPayload);
  const changedFiles = resolveChangedFiles(options, eventPayload, baseRef);
  const currentLabels = resolveCurrentLabels(options, eventPayload);
  const currentLabelSet = new Set(currentLabels);

  const riskLabels = getRiskLabels(policy);
  const currentRiskLabels = currentLabels.filter(
    (label) => label === riskLabels.low || label === riskLabels.high,
  );
  const inferredRisk = inferRiskLevel(policy, changedFiles);
  const { requiredLabels } = collectRequiredLabels(policy, changedFiles);

  const selectedRiskLabel = currentRiskLabels.length === 1
    ? currentRiskLabels[0]
    : inferredRisk.level;
  const missingRequiredLabels = requiredLabels.filter((label) => !currentLabelSet.has(label));
  const evidence = buildEvidence(options.artifactRoot);
  const intentSummary = resolveIntentSummary(options, eventPayload, changedFiles.length);
  const monitoringPlan = buildMonitoringPlan(requiredLabels);
  if (missingRequiredLabels.length > 0) {
    pushUnique(monitoringPlan.alerts, 'missing-required-labels');
  }

  const isHighRisk = selectedRiskLabel === riskLabels.high || inferredRisk.level === riskLabels.high;
  const rolloutPlan = {
    strategy: isHighRisk ? 'manual-approval-and-gate-green' : 'auto-merge-when-gates-pass',
    references: [options.policyPath],
    notes: isHighRisk
      ? [
        'High-risk changes require human approval and required gate labels.',
        'Do not merge until required labels/checks are green.',
      ]
      : [
        'Low-risk changes can be merged when required checks are green.',
      ],
  };

  const changePackage = {
    schemaVersion: 'change-package/v1',
    generatedAt: new Date().toISOString(),
    policyPath: options.policyPath,
    source: {
      repository,
      prNumber,
      baseRef,
      headRef,
    },
    intent: {
      summary: intentSummary,
    },
    scope: {
      changedFiles,
      changedFileCount: changedFiles.length,
      areas: inferScopeAreas(changedFiles),
    },
    risk: {
      selected: selectedRiskLabel,
      inferred: inferredRisk.level,
      isHighRisk,
      requiredLabels,
      missingRequiredLabels,
      rationale: {
        highRiskPathMatches: inferredRisk.highRiskPathMatches,
        forceHighRiskTriggers: inferredRisk.forceHighRiskTriggers,
      },
    },
    evidence,
    reproducibility: {
      commands: buildReproducibilityCommands(requiredLabels),
    },
    rolloutPlan,
    monitoringPlan,
    exceptions: buildExceptions({
      missingRequiredLabels,
      selectedRiskLabel,
      inferredRiskLabel: inferredRisk.level,
      currentRiskLabels,
      evidence,
    }),
  };

  return changePackage;
}

function buildChangePackageV2(options, eventPayload, baseChangePackage = buildChangePackage(options, eventPayload)) {
  const claimEvidenceManifest = loadOptionalJsonSource(
    'claimEvidenceManifest',
    options.claimEvidenceManifestPath,
    'claim-evidence-manifest/v1 assurance claims',
  );
  const policyDecision = loadOptionalJsonSource(
    'policyDecision',
    options.policyDecisionPath,
    'policy-decision/v1 policy-gate decision',
  );
  const assuranceSummary = loadOptionalJsonSource(
    'assuranceSummary',
    options.assuranceSummaryPath,
    'assurance-summary/v1 lane coverage summary',
  );
  const claimLevelSummary = loadOptionalJsonSource(
    'claimLevelSummary',
    options.claimLevelSummaryPath,
    'claim-level-summary/v1 per-claim achieved-level summary',
  );
  const postDeployVerify = loadOptionalJsonSource(
    'postDeployVerify',
    options.postDeployVerifyPath,
    'post-deploy verification result',
  );
  const claimsById = new Map();
  const proofObligations = [];
  const waivers = [];
  const assumptions = [];
  const runtimeControls = [];

  if (assuranceSummary.present) {
    ingestAssuranceSummaryForV2(claimsById, assuranceSummary);
  }
  if (claimEvidenceManifest.present) {
    ingestManifestForV2(claimsById, proofObligations, waivers, claimEvidenceManifest);
  }
  if (policyDecision.present) {
    ingestPolicyDecisionForV2(claimsById, waivers, policyDecision);
  }
  if (claimLevelSummary.present) {
    ingestClaimLevelSummaryForV2(claimsById, proofObligations, waivers, assumptions, runtimeControls, claimLevelSummary);
  }

  const claims = Array.from(claimsById.values())
    .map((claim) => ({
      ...claim,
      artifactRefs: normalizeArtifactRefs(claim.artifactRefs, options.claimEvidenceManifestPath),
    }))
    .sort((left, right) => left.id.localeCompare(right.id));
  const claimIds = new Set(claims.map((claim) => claim.id));
  const filteredProofObligations = dedupeProofObligations(proofObligations)
    .filter((obligation) => claimIds.has(obligation.claimId));
  const filteredWaivers = dedupeWaivers(waivers)
    .map((waiver) => ({
      ...waiver,
      relatedClaimIds: waiver.relatedClaimIds.filter((claimId) => claimIds.has(claimId)),
    }))
    .filter((waiver) => waiver.relatedClaimIds.length > 0);
  const releaseControls = buildReleaseControls(baseChangePackage, postDeployVerify);
  const normalizedRuntimeControls = {
    alerts: uniqueStrings([
      ...baseChangePackage.monitoringPlan.alerts,
      ...runtimeControls.filter((control) => control.kind === 'alert').map((control) => control.id),
    ]),
    featureFlags: uniqueStrings([
      ...runtimeControls.filter((control) => control.kind === 'feature-flag').map((control) => control.id),
    ]),
  };

  return {
    ...baseChangePackage,
    schemaVersion: 'change-package/v2',
    evidence: buildV2Evidence(baseChangePackage.evidence, [
      claimEvidenceManifest,
      policyDecision,
      assuranceSummary,
      claimLevelSummary,
      postDeployVerify,
    ]),
    requirements: buildV2Requirements(baseChangePackage.scope.changedFiles, claims),
    validationLanes: buildValidationLanes(claimLevelSummary, baseChangePackage.evidence),
    policyDecision: buildPolicyDecisionSummary(policyDecision),
    releaseControls,
    residualRisks: buildResidualRisks(claims, assumptions),
    assurance: buildV2Assurance(claims, claimEvidenceManifest, policyDecision, assuranceSummary, claimLevelSummary),
    claims,
    assumptions: assumptions.map((assumption) => ({
      id: assumption.id,
      statement: assumption.statement,
      owner: assumption.owner,
      evidenceRefs: normalizeArtifactRefs(assumption.evidenceRefs, claimLevelSummary.path),
    })).sort((left, right) => left.id.localeCompare(right.id)),
    proofObligations: filteredProofObligations,
    counterexamples: [],
    trustBoundary: {
      outsideModel: [],
    },
    runtimeControls: normalizedRuntimeControls,
    waivers: filteredWaivers,
  };
}

function writeChangePackageOutputs(changePackage, outputJsonPath, outputMarkdownPath, mode) {
  const markdown = renderMarkdown(changePackage, mode, outputJsonPath);

  ensureDirectory(outputJsonPath);
  fs.writeFileSync(outputJsonPath, `${JSON.stringify(changePackage, null, 2)}\n`);

  ensureDirectory(outputMarkdownPath);
  fs.writeFileSync(outputMarkdownPath, `${markdown.trimEnd()}\n`);

  return markdown;
}

function writeOutputs(options, changePackage) {
  return writeChangePackageOutputs(
    changePackage,
    options.outputJsonPath,
    options.outputMarkdownPath,
    isModeDigest(options.mode) ? 'digest' : 'detailed',
  );
}

async function run(options = parseArgs(process.argv)) {
  if (options.help) {
    printHelp();
    return null;
  }

  const eventPayload = readJsonIfExists(options.eventPath) || {};
  const v1ChangePackage = buildChangePackage(options, eventPayload);
  const changePackage = options.schemaVersion === 'v2'
    ? buildChangePackageV2(options, eventPayload, v1ChangePackage)
    : v1ChangePackage;
  const markdown = writeOutputs(options, changePackage);
  let v2ChangePackage = null;
  if (options.dualWrite) {
    v2ChangePackage = buildChangePackageV2(options, eventPayload, v1ChangePackage);
    writeChangePackageOutputs(
      v2ChangePackage,
      options.v2OutputJsonPath,
      options.v2OutputMarkdownPath,
      isModeDigest(options.mode) ? 'digest' : 'detailed',
    );
  }
  process.stdout.write(`${markdown.trimEnd()}\n`);
  return options.dualWrite
    ? { primary: changePackage, v1: v1ChangePackage, v2: v2ChangePackage }
    : changePackage;
}

function isDirectExecution() {
  const entry = process.argv[1];
  if (!entry) return false;
  return import.meta.url === pathToFileURL(resolve(entry)).href;
}

if (isDirectExecution()) {
  try {
    await run();
  } catch (error) {
    const message = error instanceof Error ? error.stack || error.message : String(error);
    process.stderr.write(`[change-package:generate] ${message}\n`);
    process.exit(1);
  }
}

export {
  buildChangePackage,
  buildChangePackageV2,
  parseArgs,
  renderMarkdown,
  run,
};
