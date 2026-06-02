#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import {
  buildClaimLevelSummary,
  renderClaimLevelSummaryMarkdown,
  validateClaimLevelSummary,
} from './aggregate-claim-levels.mjs';
import { buildClaimEvidenceManifest, renderClaimEvidenceManifestMarkdown, validateManifest } from './build-claim-evidence-manifest.mjs';
import {
  buildMarkdownSummary,
  buildPolicyGateReport,
  buildPolicyInputV1,
  evaluatePolicyGate,
  inspectClaimEvidenceManifest,
} from '../ci/policy-gate.mjs';
import { loadRiskPolicy } from '../ci/lib/risk-policy.mjs';
import { validateClaimEvidenceManifestSemantics } from '../ci/lib/claim-evidence-manifest-contract.mjs';
import { renderMarkdown as renderChangePackageMarkdown } from '../change-package/generate.mjs';

const DEFAULT_SCENARIO = 'inventory-waiver';
const DEFAULT_FIXTURE_ROOT = 'fixtures/assurance-e2e';
const DEFAULT_GENERATED_AT = '2026-05-06T00:00:00.000Z';

const ARTIFACT_FILES = [
  'verify-lite-run-summary.json',
  'assurance-summary.json',
  'claim-evidence-manifest.json',
  'claim-evidence-manifest.md',
  'policy-input-v1.json',
  'policy-decision-js-v1.json',
  'policy-gate-summary.json',
  'policy-gate-summary.md',
  'claim-level-summary.json',
  'claim-level-summary.md',
  'change-package-v2.json',
  'change-package-v2.md',
];

function usage() {
  process.stdout.write(`Usage: node scripts/assurance/run-e2e-scenario.mjs [options]\n\nOptions:\n  --scenario <name>          scenario name under fixtures/assurance-e2e (default: ${DEFAULT_SCENARIO})\n  --scenario-dir <path>      explicit scenario directory\n  --output-dir <path>        actual artifact output directory\n  --generated-at <iso>       deterministic generatedAt value (default: ${DEFAULT_GENERATED_AT})\n  --update-expected          replace expected artifacts with the current actual artifacts\n  --no-compare               generate and validate only; skip expected-vs-actual comparison\n  --help                     show this help\n`);
}

function readRequiredValue(argv, index, option) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`${option} requires a value`);
  }
  return next;
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    scenario: DEFAULT_SCENARIO,
    scenarioDir: null,
    outputDir: null,
    generatedAt: DEFAULT_GENERATED_AT,
    updateExpected: false,
    compare: true,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--scenario') {
      options.scenario = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--scenario-dir') {
      options.scenarioDir = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--update-expected') {
      options.updateExpected = true;
      continue;
    }
    if (arg === '--no-compare') {
      options.compare = false;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
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

function timestampSlug(value) {
  return ensureDateTime(value)
    .replace(/\.\d{3}Z$/u, 'Z')
    .replace(/[:.]/gu, '-');
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function writeText(filePath, content) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, content, 'utf8');
}

function writeJson(filePath, payload) {
  writeText(filePath, `${JSON.stringify(payload, null, 2)}\n`);
}

function toPosixPath(filePath) {
  return filePath.split(path.sep).join('/');
}

function toRepoRelativePath(filePath) {
  const relativePath = path.relative(process.cwd(), filePath);
  return relativePath && !relativePath.startsWith('..') && !path.isAbsolute(relativePath)
    ? toPosixPath(relativePath)
    : toPosixPath(filePath);
}

function ensureOutputDirUnderRepoRoot(outputDir) {
  const relativePath = path.relative(process.cwd(), outputDir);
  if (!relativePath || relativePath.startsWith('..') || path.isAbsolute(relativePath)) {
    throw new Error(`output-dir must stay under the repository root: ${outputDir}`);
  }
}

function stableStringify(value) {
  if (Array.isArray(value)) {
    return `[${value.map((entry) => stableStringify(entry)).join(',')}]`;
  }
  if (value && typeof value === 'object') {
    return `{${Object.keys(value)
      .sort((left, right) => left.localeCompare(right))
      .map((key) => `${JSON.stringify(key)}:${stableStringify(value[key])}`)
      .join(',')}}`;
  }
  return JSON.stringify(value);
}

function normalizeForComparison(filePath) {
  const raw = fs.readFileSync(filePath, 'utf8');
  if (filePath.endsWith('.json')) {
    return `${JSON.stringify(JSON.parse(raw), Object.keys(JSON.parse(raw)).sort(), 2)}\n`;
  }
  return raw.replace(/\r\n/gu, '\n');
}

function compareArtifact(expectedPath, actualPath) {
  if (!fs.existsSync(expectedPath)) {
    return `expected artifact missing: ${expectedPath}`;
  }
  const expected = expectedPath.endsWith('.json')
    ? stableStringify(readJson(expectedPath))
    : normalizeForComparison(expectedPath);
  const actual = actualPath.endsWith('.json')
    ? stableStringify(readJson(actualPath))
    : normalizeForComparison(actualPath);
  if (expected === actual) {
    return null;
  }
  return `artifact differs: ${path.basename(actualPath)}`;
}

function loadSchemaValidator(schemaPath) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const metadataSchemaPath = path.resolve('schema/artifact-metadata.schema.json');
  if (fs.existsSync(metadataSchemaPath)) {
    ajv.addSchema(readJson(metadataSchemaPath));
  }
  const schema = readJson(path.resolve(schemaPath));
  return ajv.compile(schema);
}

function validateWithSchema(label, payload, schemaPath, semanticValidate = null) {
  const validate = loadSchemaValidator(schemaPath);
  if (!validate(payload)) {
    throw new Error(`${label} schema validation failed: ${JSON.stringify(validate.errors ?? [], null, 2)}`);
  }
  if (typeof semanticValidate === 'function') {
    const semanticErrors = semanticValidate(payload);
    if (semanticErrors.length > 0) {
      throw new Error(`${label} semantic validation failed: ${JSON.stringify(semanticErrors, null, 2)}`);
    }
  }
}

function checkRun(name, conclusion = 'SUCCESS') {
  return {
    __typename: 'CheckRun',
    name,
    status: 'COMPLETED',
    conclusion,
  };
}

function normalizeCheckEntryForContract(entry) {
  return {
    name: String(entry?.name || '').trim(),
    state: String(entry?.state || '').trim(),
    type: String(entry?.type || '').trim(),
    status: String(entry?.status || '').trim(),
    conclusion: String(entry?.conclusion || '').trim(),
  };
}

function normalizeCheckResultForContract(item) {
  return {
    ...item,
    result: {
      ...item.result,
      matches: (Array.isArray(item.result?.matches) ? item.result.matches : []).map(normalizeCheckEntryForContract),
    },
  };
}

function normalizeEvaluationForContract(evaluation) {
  const { planArtifact: _planArtifact, ...contractEvaluation } = evaluation;
  return {
    ...contractEvaluation,
    requiredCheckResults: (Array.isArray(evaluation.requiredCheckResults) ? evaluation.requiredCheckResults : [])
      .map(normalizeCheckResultForContract),
    gateCheckResults: (Array.isArray(evaluation.gateCheckResults) ? evaluation.gateCheckResults : [])
      .map(normalizeCheckResultForContract),
  };
}

function scenarioPaths(options) {
  const scenarioDir = path.resolve(options.scenarioDir || path.join(DEFAULT_FIXTURE_ROOT, options.scenario));
  const scenarioName = path.basename(scenarioDir);
  const outputDir = path.resolve(
    options.outputDir || path.join('artifacts/assurance-e2e', scenarioName, timestampSlug(options.generatedAt)),
  );
  ensureOutputDirUnderRepoRoot(outputDir);
  return {
    scenarioName,
    scenarioDir,
    inputsDir: path.join(scenarioDir, 'inputs'),
    expectedDir: path.join(scenarioDir, 'expected'),
    outputDir,
  };
}

function canonicalArtifactPaths(scenarioName) {
  const root = `artifacts/assurance-e2e/${scenarioName}`;
  return {
    verifyLite: `${root}/verify-lite-run-summary.json`,
    assuranceSummary: `${root}/assurance-summary.json`,
    claimEvidenceManifest: `${root}/claim-evidence-manifest.json`,
    policyInput: `${root}/policy-input-v1.json`,
    policyDecision: `${root}/policy-decision-js-v1.json`,
    policyGateSummary: `${root}/policy-gate-summary.json`,
    claimLevelSummary: `${root}/claim-level-summary.json`,
    changePackageV2: `${root}/change-package-v2.json`,
  };
}

function buildPolicyArtifacts({ scenarioName, generatedAt, manifestPath, outputDir, changePackagePath }) {
  const canonical = canonicalArtifactPaths(scenarioName);
  const policy = loadRiskPolicy('policy/risk-policy.yml');
  const assurance = inspectClaimEvidenceManifest(manifestPath, generatedAt);
  assurance.path = canonical.claimEvidenceManifest;
  if (assurance.provenance) {
    const originalProvenancePath = assurance.provenance.path;
    const canonicalProvenancePath = `${path.posix.dirname(canonical.claimEvidenceManifest)}/claim-evidence-provenance.json`;
    const normalizeProvenancePath = (message) => String(message).split(originalProvenancePath).join(canonicalProvenancePath);
    assurance.provenance.path = canonicalProvenancePath;
    assurance.provenance.warnings = (Array.isArray(assurance.provenance.warnings) ? assurance.provenance.warnings : [])
      .map(normalizeProvenancePath);
    assurance.provenance.errors = (Array.isArray(assurance.provenance.errors) ? assurance.provenance.errors : [])
      .map(normalizeProvenancePath);
  }
  const pullRequest = {
    labels: [{ name: 'risk:low' }],
    body: '## Acceptance\nFixture scenario reproduces verify-lite, assurance summary, claim evidence manifest, and policy decision artifacts.\n\n## Rollback\nRevert the fixture scenario, runner, and expected golden artifacts.',
  };
  const changedFiles = [
    toRepoRelativePath(changePackagePath),
    'scripts/assurance/run-e2e-scenario.mjs',
  ];
  const reviews = [];
  const statusRollup = [checkRun('verify-lite')];
  const reviewTopology = 'solo';
  const assuranceMode = 'report-only';
  const repo = 'itdojp/ae-framework';
  const prNumber = 3245;

  const policyInput = buildPolicyInputV1({
    repo,
    prNumber,
    policyPath: 'policy/risk-policy.yml',
    policy,
    pullRequest,
    changedFiles,
    reviews,
    statusRollup,
    reviewTopology,
    assuranceMode,
    assurance,
    now: generatedAt,
  });
  const evaluation = evaluatePolicyGate({
    policy,
    pullRequest,
    changedFiles,
    reviews,
    statusRollup,
    reviewTopology,
    assuranceMode,
    assurance,
  });
  const contractEvaluation = normalizeEvaluationForContract(evaluation);
  const policyDecision = {
    schemaVersion: '1.0.0',
    contractId: 'policy-decision.v1',
    generatedAtUtc: generatedAt,
    repository: repo,
    prNumber,
    inputPath: canonical.policyInput,
    engine: {
      kind: 'js',
      status: 'supported',
      version: 'node',
    },
    evaluation: contractEvaluation,
  };
  const policyGateSummary = buildPolicyGateReport({
    generatedAtUtc: generatedAt,
    repository: repo,
    prNumber,
    changedFiles,
    evaluation: contractEvaluation,
  });
  const policyGateMarkdown = buildMarkdownSummary(prNumber, contractEvaluation);

  writeJson(path.join(outputDir, 'policy-input-v1.json'), policyInput);
  writeJson(path.join(outputDir, 'policy-decision-js-v1.json'), policyDecision);
  writeJson(path.join(outputDir, 'policy-gate-summary.json'), policyGateSummary);
  writeText(path.join(outputDir, 'policy-gate-summary.md'), `${policyGateMarkdown}\n`);

  validateWithSchema('policy input', policyInput, 'schema/policy-input-v1.schema.json');
  validateWithSchema('policy decision', policyDecision, 'schema/policy-decision-v1.schema.json');
  validateWithSchema('policy gate summary', policyGateSummary, 'schema/policy-gate-summary-v1.schema.json');

  return {
    policyInput,
    policyDecision,
    policyGateSummary,
  };
}

function buildClaimLevelArtifacts({ scenarioName, generatedAt, outputDir, manifestPath, policyGateSummaryPath, changePackagePath }) {
  const canonical = canonicalArtifactPaths(scenarioName);
  const claimLevelSummary = buildClaimLevelSummary({
    claimEvidenceManifest: manifestPath,
    policyGateSummary: policyGateSummaryPath,
    changePackage: changePackagePath,
    temporaryOverrides: [],
    generatedAt,
    repository: 'itdojp/ae-framework',
    prNumber: 3245,
    baseRef: 'main',
    headRef: 'feat/3245-assurance-e2e',
    headSha: 'fixture-current-head-smoke',
  });
  claimLevelSummary.inputs.claimEvidenceManifest.path = canonical.claimEvidenceManifest;
  claimLevelSummary.inputs.policyGateSummary.path = canonical.policyGateSummary;
  validateClaimLevelSummary(claimLevelSummary, 'schema/claim-level-summary-v1.schema.json');
  writeJson(path.join(outputDir, 'claim-level-summary.json'), claimLevelSummary);
  writeText(path.join(outputDir, 'claim-level-summary.md'), renderClaimLevelSummaryMarkdown(claimLevelSummary));
  return claimLevelSummary;
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

function summarizePolicyDecisionForChangePackage(policyDecision, sourceArtifactPath) {
  const assurance = policyDecision?.evaluation?.assurance && typeof policyDecision.evaluation.assurance === 'object'
    ? policyDecision.evaluation.assurance
    : {};
  const result = normalizeDecisionResult(assurance.result);
  const enforced = String(assurance.mode || '').trim().toLowerCase() === 'strict' || result === 'block';
  return {
    present: true,
    sourceArtifactPath,
    result,
    mode: normalizeDecisionMode(assurance.mode, enforced),
    enforced,
    reason: `Policy decision assurance result is ${result}.`,
    warnings: Array.isArray(assurance.warnings) ? assurance.warnings.map(String) : [],
    errors: Array.isArray(assurance.errors) ? assurance.errors.map(String) : [],
  };
}

function buildChangePackageArtifacts({ scenarioName, outputDir, changePackagePath, policyDecisionPath }) {
  const canonical = canonicalArtifactPaths(scenarioName);
  const changePackage = readJson(changePackagePath);
  const policyDecision = readJson(policyDecisionPath);
  changePackage.policyDecision = summarizePolicyDecisionForChangePackage(policyDecision, canonical.policyDecision);
  validateWithSchema('change package v2', changePackage, 'schema/change-package-v2.schema.json');
  writeJson(path.join(outputDir, 'change-package-v2.json'), changePackage);
  writeText(
    path.join(outputDir, 'change-package-v2.md'),
    renderChangePackageMarkdown(changePackage, 'detailed', canonical.changePackageV2),
  );
  return changePackage;
}

export function runScenario(options) {
  const generatedAt = ensureDateTime(options.generatedAt);
  const paths = scenarioPaths(options);
  const canonical = canonicalArtifactPaths(paths.scenarioName);

  const inputFiles = {
    verifyLite: path.join(paths.inputsDir, 'verify-lite-run-summary.json'),
    assuranceSummary: path.join(paths.inputsDir, 'assurance-summary.json'),
    changePackage: path.join(paths.inputsDir, 'change-package-v2.json'),
    qualityScorecard: path.join(paths.inputsDir, 'quality-scorecard.json'),
  };
  for (const [label, filePath] of Object.entries(inputFiles)) {
    if (!fs.existsSync(filePath)) {
      throw new Error(`${label} input not found: ${filePath}`);
    }
  }

  fs.mkdirSync(paths.outputDir, { recursive: true });
  const verifyLiteSummary = readJson(inputFiles.verifyLite);
  const assuranceSummary = readJson(inputFiles.assuranceSummary);
  writeJson(path.join(paths.outputDir, 'verify-lite-run-summary.json'), verifyLiteSummary);
  writeJson(path.join(paths.outputDir, 'assurance-summary.json'), assuranceSummary);
  validateWithSchema('verify-lite run summary', verifyLiteSummary, 'schema/verify-lite-run-summary.schema.json');
  validateWithSchema('assurance summary', assuranceSummary, 'schema/assurance-summary.schema.json');

  const manifest = buildClaimEvidenceManifest({
    assuranceSummary: toRepoRelativePath(inputFiles.assuranceSummary),
    changePackages: [toRepoRelativePath(inputFiles.changePackage)],
    qualityScorecard: toRepoRelativePath(inputFiles.qualityScorecard),
    verifyLiteSummary: toRepoRelativePath(inputFiles.verifyLite),
    traceBundles: [],
    generatedAt,
    outputJson: path.join(paths.outputDir, 'claim-evidence-manifest.json'),
    outputMd: path.join(paths.outputDir, 'claim-evidence-manifest.md'),
    schema: 'schema/claim-evidence-manifest.schema.json',
    validate: true,
  });
  validateManifest(manifest, 'schema/claim-evidence-manifest.schema.json');
  writeJson(path.join(paths.outputDir, 'claim-evidence-manifest.json'), manifest);
  writeText(path.join(paths.outputDir, 'claim-evidence-manifest.md'), renderClaimEvidenceManifestMarkdown(manifest));
  validateWithSchema(
    'claim evidence manifest',
    manifest,
    'schema/claim-evidence-manifest.schema.json',
    validateClaimEvidenceManifestSemantics,
  );

  const policyArtifacts = buildPolicyArtifacts({
    scenarioName: paths.scenarioName,
    generatedAt,
    manifestPath: path.join(paths.outputDir, 'claim-evidence-manifest.json'),
    outputDir: paths.outputDir,
    changePackagePath: inputFiles.changePackage,
  });
  const claimLevelSummary = buildClaimLevelArtifacts({
    scenarioName: paths.scenarioName,
    generatedAt,
    outputDir: paths.outputDir,
    manifestPath: path.join(paths.outputDir, 'claim-evidence-manifest.json'),
    policyGateSummaryPath: path.join(paths.outputDir, 'policy-gate-summary.json'),
    changePackagePath: inputFiles.changePackage,
  });
  const changePackage = buildChangePackageArtifacts({
    scenarioName: paths.scenarioName,
    outputDir: paths.outputDir,
    changePackagePath: inputFiles.changePackage,
    policyDecisionPath: path.join(paths.outputDir, 'policy-decision-js-v1.json'),
  });

  if (options.updateExpected) {
    fs.mkdirSync(paths.expectedDir, { recursive: true });
    for (const fileName of ARTIFACT_FILES) {
      fs.copyFileSync(path.join(paths.outputDir, fileName), path.join(paths.expectedDir, fileName));
    }
  }

  const comparisonErrors = [];
  if (options.compare) {
    for (const fileName of ARTIFACT_FILES) {
      const error = compareArtifact(path.join(paths.expectedDir, fileName), path.join(paths.outputDir, fileName));
      if (error) comparisonErrors.push(error);
    }
  }
  if (comparisonErrors.length > 0) {
    throw new Error(`assurance e2e scenario drift detected:\n- ${comparisonErrors.join('\n- ')}\nRun with --update-expected after reviewing intentional changes.`);
  }

  return {
    scenario: paths.scenarioName,
    outputDir: paths.outputDir,
    expectedDir: paths.expectedDir,
    canonical,
    summary: {
      verifyLiteStatus: Object.values(verifyLiteSummary.steps).every((step) => step.status === 'success') ? 'success' : 'non-success',
      assuranceClaims: assuranceSummary.summary?.claimCount ?? assuranceSummary.claims?.length ?? 0,
      claimEvidenceClaims: manifest.summary.totalClaims,
      claimLevelClaims: claimLevelSummary.summary.totalClaims,
      claimEvidenceWaived: manifest.summary.waived,
      policyDecision: policyArtifacts.policyDecision.evaluation.assurance?.result ?? 'unknown',
      changePackageStatus: changePackage.assurance?.status ?? 'unknown',
    },
  };
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    usage();
    return 0;
  }
  const result = runScenario(options);
  process.stdout.write('### Assurance E2E Scenario\n');
  process.stdout.write(`- scenario: ${result.scenario}\n`);
  process.stdout.write(`- output: ${result.outputDir}\n`);
  process.stdout.write(`- claim evidence claims: ${result.summary.claimEvidenceClaims}\n`);
  process.stdout.write(`- claim-level claims: ${result.summary.claimLevelClaims}\n`);
  process.stdout.write(`- waived claims: ${result.summary.claimEvidenceWaived}\n`);
  process.stdout.write(`- policy assurance result: ${result.summary.policyDecision}\n`);
  process.stdout.write(`- change-package assurance status: ${result.summary.changePackageStatus}\n`);
  process.stdout.write('- comparison: ok\n');
  return 0;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  try {
    process.exitCode = run();
  } catch (error) {
    process.stderr.write(`[assurance-e2e] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}
