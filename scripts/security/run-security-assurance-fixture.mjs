#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { run as runAggregateLanes } from '../assurance/aggregate-lanes.mjs';
import {
  buildClaimEvidenceManifest,
  renderClaimEvidenceManifestMarkdown,
  validateManifest,
} from '../assurance/build-claim-evidence-manifest.mjs';
import { validateClaimEvidenceManifestSemantics } from '../ci/lib/claim-evidence-manifest-contract.mjs';
import {
  validateSecurityAuditTaskBundleSemantics,
  validateSecurityCodeMapSemantics,
  validateSecurityFindingSemantics,
  validateSecurityReviewSemantics,
} from '../ci/lib/security-assurance-contract.mjs';

const REPO_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const DEFAULT_SCENARIO = 'cache-key';
const DEFAULT_FIXTURE_ROOT = 'fixtures/security-assurance';
const DEFAULT_GENERATED_AT = '2026-05-07T00:00:00.000Z';
const SECURITY_CLI_TIMEOUT_MS = 120_000;

const ARTIFACT_FILES = [
  'security-audit-scope.json',
  'security-threat-model.json',
  'security-claims.json',
  'security-claims.md',
  'security-code-map.json',
  'security-code-map.md',
  'security-audit-tasks.json',
  'security-audit-summary.md',
  'security-findings.json',
  'security-review.json',
  'security-review.md',
  'assurance-summary.json',
  'assurance-summary.md',
  'claim-evidence-manifest.json',
  'claim-evidence-manifest.md',
  'security-summary.md',
];

const JSON_ARTIFACT_SCHEMAS = {
  'security-audit-scope.json': { schema: 'schema/security-audit-scope-v1.schema.json' },
  'security-threat-model.json': { schema: 'schema/security-threat-model-v1.schema.json' },
  'security-claims.json': { schema: 'schema/security-claim-v1.schema.json' },
  'security-code-map.json': {
    schema: 'schema/security-code-map-v1.schema.json',
    semanticValidate: validateSecurityCodeMapSemantics,
  },
  'security-audit-tasks.json': {
    schema: 'schema/security-audit-task-bundle-v1.schema.json',
    semanticValidate: validateSecurityAuditTaskBundleSemantics,
  },
  'security-findings.json': {
    schema: 'schema/security-finding-v1.schema.json',
    semanticValidate: validateSecurityFindingSemantics,
  },
  'security-review.json': {
    schema: 'schema/security-review-v1.schema.json',
    semanticValidate: validateSecurityReviewSemantics,
  },
  'assurance-summary.json': { schema: 'schema/assurance-summary.schema.json' },
  'claim-evidence-manifest.json': {
    schema: 'schema/claim-evidence-manifest.schema.json',
    semanticValidate: validateClaimEvidenceManifestSemantics,
  },
};

function usage() {
  process.stdout.write(`Usage: node scripts/security/run-security-assurance-fixture.mjs [options]\n\nOptions:\n  --scenario <name>          scenario under fixtures/security-assurance (default: ${DEFAULT_SCENARIO})\n  --scenario-dir <path>      explicit scenario directory\n  --output-dir <path>        actual artifact output directory\n  --generated-at <iso>       deterministic generatedAt value (default: ${DEFAULT_GENERATED_AT})\n  --update-expected          replace expected artifacts with current normalized actual artifacts\n  --no-compare               generate and validate only; skip expected-vs-actual comparison\n  --help                     show this help\n`);
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

function toPosixPath(filePath) {
  return String(filePath).split(path.sep).join('/');
}

function toRepoRelativePath(filePath) {
  const relativePath = path.relative(REPO_ROOT, filePath);
  return relativePath && !relativePath.startsWith('..') && !path.isAbsolute(relativePath)
    ? toPosixPath(relativePath)
    : toPosixPath(filePath);
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

function copyJsonWithGeneratedAt(inputPath, outputPath, generatedAt) {
  const payload = readJson(inputPath);
  if (Object.prototype.hasOwnProperty.call(payload, 'generatedAt')) {
    payload.generatedAt = generatedAt;
  }
  writeJson(outputPath, payload);
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

function normalizeTextForComparison(filePath) {
  const raw = fs.readFileSync(filePath, 'utf8');
  return raw.replace(/\r\n/gu, '\n');
}

function compareArtifact(expectedPath, actualPath) {
  if (!fs.existsSync(expectedPath)) {
    return `expected artifact missing: ${expectedPath}`;
  }
  const expected = expectedPath.endsWith('.json')
    ? stableStringify(readJson(expectedPath))
    : normalizeTextForComparison(expectedPath);
  const actual = actualPath.endsWith('.json')
    ? stableStringify(readJson(actualPath))
    : normalizeTextForComparison(actualPath);
  return expected === actual ? null : `artifact differs: ${path.basename(actualPath)}`;
}

function scenarioPaths(options) {
  const scenarioDir = path.resolve(REPO_ROOT, options.scenarioDir || path.join(DEFAULT_FIXTURE_ROOT, options.scenario));
  const scenarioName = path.basename(scenarioDir);
  const outputDir = path.resolve(
    REPO_ROOT,
    options.outputDir || path.join('artifacts/security-assurance', scenarioName, timestampSlug(options.generatedAt)),
  );
  return {
    scenarioName,
    scenarioDir,
    inputsDir: path.join(scenarioDir, 'inputs'),
    expectedDir: path.join(scenarioDir, 'expected'),
    outputDir,
  };
}

function canonicalRoots(scenarioName) {
  return {
    scenario: `fixtures/security-assurance/${scenarioName}`,
    inputs: `fixtures/security-assurance/${scenarioName}/inputs`,
    output: `artifacts/security-assurance/${scenarioName}`,
  };
}

function normalizeReplacementEntries(paths) {
  const canonical = canonicalRoots(paths.scenarioName);
  const entries = [
    [paths.outputDir, canonical.output],
    [paths.inputsDir, canonical.inputs],
    [paths.scenarioDir, canonical.scenario],
  ];
  const normalized = [];
  for (const [fromPath, toPath] of entries) {
    normalized.push([toPosixPath(path.resolve(fromPath)), toPath]);
    normalized.push([toRepoRelativePath(path.resolve(fromPath)), toPath]);
  }
  return normalized
    .filter(([fromPath]) => fromPath && fromPath !== '.')
    .sort((left, right) => right[0].length - left[0].length);
}

function replaceAllLiteral(value, search, replacement) {
  return value.split(search).join(replacement);
}

function normalizeString(value, replacements) {
  let normalized = value.replace(/\\/gu, '/');
  for (const [fromPath, toPath] of replacements) {
    normalized = replaceAllLiteral(normalized, fromPath, toPath);
  }
  return normalized;
}

function deepNormalize(value, replacements) {
  if (Array.isArray(value)) {
    return value.map((entry) => deepNormalize(entry, replacements));
  }
  if (value && typeof value === 'object') {
    return Object.fromEntries(
      Object.entries(value).map(([key, entry]) => [key, deepNormalize(entry, replacements)]),
    );
  }
  return typeof value === 'string' ? normalizeString(value, replacements) : value;
}

function deterministicMetadata(generatedAt) {
  return {
    generatedAtUtc: generatedAt,
    generatedAtLocal: generatedAt,
    timezoneOffset: '+00:00',
    gitCommit: null,
    branch: null,
    runner: {
      name: 'security-assurance-fixture',
      os: 'normalized',
      arch: 'normalized',
      ci: false,
    },
    toolVersions: {},
  };
}

function normalizeAssuranceSummary(summary, generatedAt) {
  return {
    ...summary,
    generatedAt,
    metadata: deterministicMetadata(generatedAt),
  };
}

function buildAjv() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const metadataSchemaPath = path.join(REPO_ROOT, 'schema/artifact-metadata.schema.json');
  if (fs.existsSync(metadataSchemaPath)) {
    ajv.addSchema(readJson(metadataSchemaPath));
  }
  return ajv;
}

function validateWithSchema(label, payload, schemaPath, semanticValidate = null) {
  const ajv = buildAjv();
  const validate = ajv.compile(readJson(path.join(REPO_ROOT, schemaPath)));
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

function validateJsonArtifact(fileName, payload) {
  const check = JSON_ARTIFACT_SCHEMAS[fileName];
  if (!check) return;
  validateWithSchema(fileName, payload, check.schema, check.semanticValidate ?? null);
}

function rewriteNormalizedJsonArtifacts(paths, generatedAt) {
  const replacements = normalizeReplacementEntries(paths);
  for (const fileName of ARTIFACT_FILES.filter((entry) => entry.endsWith('.json'))) {
    const filePath = path.join(paths.outputDir, fileName);
    if (!fs.existsSync(filePath)) {
      throw new Error(`expected generated artifact was not written: ${filePath}`);
    }
    let payload = deepNormalize(readJson(filePath), replacements);
    if (fileName === 'assurance-summary.json') {
      payload = normalizeAssuranceSummary(payload, generatedAt);
    }
    validateJsonArtifact(fileName, payload);
    writeJson(filePath, payload);
  }
}

function rewriteNormalizedTextArtifacts(paths, generatedAt) {
  const replacements = normalizeReplacementEntries(paths);
  for (const fileName of ARTIFACT_FILES.filter((entry) => entry.endsWith('.md'))) {
    const filePath = path.join(paths.outputDir, fileName);
    if (!fs.existsSync(filePath)) {
      throw new Error(`expected generated artifact was not written: ${filePath}`);
    }
    let content = normalizeString(fs.readFileSync(filePath, 'utf8'), replacements).replace(/\r\n/gu, '\n');
    if (fileName === 'assurance-summary.md') {
      content = content.replace(/^- generatedAt: .+$/mu, `- generatedAt: ${generatedAt}`);
    }
    writeText(filePath, content.endsWith('\n') ? content : `${content}\n`);
  }
}

function resolveTsxBinary() {
  const binary = path.join(REPO_ROOT, 'node_modules', '.bin', process.platform === 'win32' ? 'tsx.cmd' : 'tsx');
  return fs.existsSync(binary) ? binary : 'tsx';
}

function runSecurityCli(label, args) {
  const result = spawnSync(resolveTsxBinary(), ['src/cli/index.ts', 'security', ...args], {
    cwd: REPO_ROOT,
    encoding: 'utf8',
    env: {
      ...process.env,
      FORCE_COLOR: '0',
      NO_COLOR: '1',
    },
    maxBuffer: 16 * 1024 * 1024,
    timeout: SECURITY_CLI_TIMEOUT_MS,
  });
  if (result.error) {
    const timeoutSuffix = result.error.code === 'ETIMEDOUT' ? ` after ${SECURITY_CLI_TIMEOUT_MS}ms` : '';
    throw new Error(`${label} failed${timeoutSuffix}: ${result.error.message}`);
  }
  if (result.status === null && result.signal) {
    throw new Error(`${label} terminated by signal ${result.signal}`);
  }
  if (result.status !== 0) {
    throw new Error(`${label} failed with exit code ${result.status ?? 'unknown'}\nstdout:\n${result.stdout}\nstderr:\n${result.stderr}`);
  }
  return result;
}

function runAggregate(paths) {
  runAggregateLanes([
    '--assurance-profile', path.join(paths.inputsDir, 'assurance-profile.json'),
    '--security-claims', path.join(paths.outputDir, 'security-claims.json'),
    '--security-findings', path.join(paths.outputDir, 'security-findings.json'),
    '--security-review', path.join(paths.outputDir, 'security-review.json'),
    '--output-json', path.join(paths.outputDir, 'assurance-summary.json'),
    '--output-md', path.join(paths.outputDir, 'assurance-summary.md'),
  ]);
}

function writeClaimEvidenceManifest(paths, generatedAt) {
  const missingChangePackage = path.join(paths.outputDir, '__missing-change-package-v2.json');
  const missingTraceBundle = path.join(paths.outputDir, '__missing-trace-bundle.json');
  const manifest = buildClaimEvidenceManifest({
    assuranceSummary: path.join(paths.outputDir, 'assurance-summary.json'),
    changePackages: [missingChangePackage],
    qualityScorecard: null,
    verifyLiteSummary: null,
    traceBundles: [missingTraceBundle],
    securityClaims: path.join(paths.outputDir, 'security-claims.json'),
    securityFindings: path.join(paths.outputDir, 'security-findings.json'),
    securityReview: path.join(paths.outputDir, 'security-review.json'),
    generatedAt,
  });
  const normalized = deepNormalize(manifest, normalizeReplacementEntries(paths));
  validateManifest(normalized, path.join(REPO_ROOT, 'schema/claim-evidence-manifest.schema.json'));
  writeJson(path.join(paths.outputDir, 'claim-evidence-manifest.json'), normalized);
  writeText(path.join(paths.outputDir, 'claim-evidence-manifest.md'), renderClaimEvidenceManifestMarkdown(normalized));
}

function countResponsesByResult(responsesPath) {
  const payload = readJson(responsesPath);
  const responses = Array.isArray(payload.responses) ? payload.responses : [];
  return responses.reduce((counts, response) => {
    const result = String(response?.result ?? 'unknown');
    counts[result] = (counts[result] ?? 0) + 1;
    return counts;
  }, {});
}

function writeSecuritySummary(paths, generatedAt) {
  const claims = readJson(path.join(paths.outputDir, 'security-claims.json'));
  const threatModel = readJson(path.join(paths.outputDir, 'security-threat-model.json'));
  const codeMap = readJson(path.join(paths.outputDir, 'security-code-map.json'));
  const findings = readJson(path.join(paths.outputDir, 'security-findings.json'));
  const review = readJson(path.join(paths.outputDir, 'security-review.json'));
  const assuranceSummary = readJson(path.join(paths.outputDir, 'assurance-summary.json'));
  const manifest = readJson(path.join(paths.outputDir, 'claim-evidence-manifest.json'));
  const responseCounts = countResponsesByResult(path.join(paths.inputsDir, 'security-audit-responses.json'));

  const lines = [
    '# Security Assurance fixture summary',
    '',
    `- Scenario: ${paths.scenarioName}`,
    `- Generated at: ${generatedAt}`,
    `- Claims: ${claims.summary?.totalClaims ?? claims.claims?.length ?? 0}`,
    `- Threats: ${threatModel.summary?.totalThreats ?? threatModel.threats?.length ?? 0}`,
    `- Code-map candidate locations: ${codeMap.summary?.totalCandidateLocations ?? 0}`,
    `- Audit responses: finding=${responseCounts.finding ?? 0}, no-finding=${responseCounts['no-finding'] ?? 0}`,
    `- Findings: ${findings.summary?.totalFindings ?? 0}`,
    `- Review results: needs-human-review=${review.summary?.byResult?.needsHumanReview ?? 0}, rejected=${review.summary?.byResult?.rejected ?? 0}, out-of-scope=${review.summary?.byResult?.outOfScope ?? 0}`,
    `- Assurance claims: ${assuranceSummary.summary?.claimCount ?? 0}`,
    `- Manifest security: findings=${manifest.summary?.security?.findings ?? 0}, highOrCriticalOpen=${manifest.summary?.security?.highOrCriticalOpen ?? 0}, outOfScope=${manifest.summary?.security?.outOfScope ?? 0}, rejected=${manifest.summary?.security?.rejected ?? 0}`,
    '',
    '## Expected lane behavior',
    '',
    '- `SEC-CLAIM-001` produces `SEC-FINDING-001` and remains `needs-human-review`.',
    '- `SEC-CLAIM-002` has a `no-finding` proof-attempt response.',
    '- `SEC-CLAIM-003` produces `SEC-FINDING-002`, which the Scope gate classifies as `out-of-scope`.',
    '',
  ];
  writeText(path.join(paths.outputDir, 'security-summary.md'), lines.join('\n'));
}

function requiredInputs(paths) {
  return {
    spec: path.join(paths.inputsDir, 'spec.md'),
    target: path.join(paths.inputsDir, 'target'),
    scope: path.join(paths.inputsDir, 'security-audit-scope.json'),
    threatModel: path.join(paths.inputsDir, 'security-threat-model.json'),
    responses: path.join(paths.inputsDir, 'security-audit-responses.json'),
    assuranceProfile: path.join(paths.inputsDir, 'assurance-profile.json'),
  };
}

function ensureScenarioInputs(paths) {
  for (const [label, filePath] of Object.entries(requiredInputs(paths))) {
    if (!fs.existsSync(filePath)) {
      throw new Error(`${label} input not found: ${filePath}`);
    }
  }
}

function generateSecurityArtifacts(paths, generatedAt) {
  const inputs = requiredInputs(paths);
  fs.mkdirSync(paths.outputDir, { recursive: true });
  copyJsonWithGeneratedAt(inputs.scope, path.join(paths.outputDir, 'security-audit-scope.json'), generatedAt);
  copyJsonWithGeneratedAt(inputs.threatModel, path.join(paths.outputDir, 'security-threat-model.json'), generatedAt);

  runSecurityCli('security claims extraction', [
    'extract-claims',
    '--spec', inputs.spec,
    '--out', paths.outputDir,
    '--generated-at', generatedAt,
  ]);
  runSecurityCli('security code-map generation', [
    'map-code',
    '--claims', path.join(paths.outputDir, 'security-claims.json'),
    '--scope', path.join(paths.outputDir, 'security-audit-scope.json'),
    '--target', inputs.target,
    '--out', paths.outputDir,
    '--generated-at', generatedAt,
  ]);
  runSecurityCli('security proof-attempt audit', [
    'audit',
    '--claims', path.join(paths.outputDir, 'security-claims.json'),
    '--code-map', path.join(paths.outputDir, 'security-code-map.json'),
    '--scope', path.join(paths.outputDir, 'security-audit-scope.json'),
    '--out', paths.outputDir,
    '--response-fixture', inputs.responses,
    '--generated-at', generatedAt,
  ]);
  runSecurityCli('security three-gate review', [
    'review',
    '--findings', path.join(paths.outputDir, 'security-findings.json'),
    '--scope', path.join(paths.outputDir, 'security-audit-scope.json'),
    '--code-map', path.join(paths.outputDir, 'security-code-map.json'),
    '--out', paths.outputDir,
    '--generated-at', generatedAt,
  ]);
}

function updateExpected(paths) {
  fs.mkdirSync(paths.expectedDir, { recursive: true });
  for (const fileName of ARTIFACT_FILES) {
    fs.copyFileSync(path.join(paths.outputDir, fileName), path.join(paths.expectedDir, fileName));
  }
}

function compareExpected(paths) {
  const comparisonErrors = [];
  for (const fileName of ARTIFACT_FILES) {
    const error = compareArtifact(path.join(paths.expectedDir, fileName), path.join(paths.outputDir, fileName));
    if (error) comparisonErrors.push(error);
  }
  if (comparisonErrors.length > 0) {
    throw new Error(`security assurance fixture drift detected:\n- ${comparisonErrors.join('\n- ')}\nRun with --update-expected after reviewing intentional changes.`);
  }
}

export function runScenario(options) {
  const generatedAt = ensureDateTime(options.generatedAt);
  const paths = scenarioPaths(options);
  ensureScenarioInputs(paths);

  const previousCwd = process.cwd();
  process.chdir(REPO_ROOT);
  try {
    generateSecurityArtifacts(paths, generatedAt);
    runAggregate(paths);
    writeClaimEvidenceManifest(paths, generatedAt);
    rewriteNormalizedJsonArtifacts(paths, generatedAt);
    writeSecuritySummary(paths, generatedAt);
    rewriteNormalizedTextArtifacts(paths, generatedAt);

    if (options.updateExpected) {
      updateExpected(paths);
    }
    if (options.compare) {
      compareExpected(paths);
    }

    const findings = readJson(path.join(paths.outputDir, 'security-findings.json'));
    const review = readJson(path.join(paths.outputDir, 'security-review.json'));
    const manifest = readJson(path.join(paths.outputDir, 'claim-evidence-manifest.json'));
    return {
      scenario: paths.scenarioName,
      outputDir: paths.outputDir,
      expectedDir: paths.expectedDir,
      summary: {
        claims: readJson(path.join(paths.outputDir, 'security-claims.json')).summary.totalClaims,
        findings: findings.summary.totalFindings,
        needsHumanReview: review.summary.byResult.needsHumanReview,
        rejected: review.summary.byResult.rejected,
        outOfScope: review.summary.byResult.outOfScope,
        highOrCriticalOpen: manifest.summary.security?.highOrCriticalOpen ?? 0,
        compared: options.compare,
      },
    };
  } finally {
    process.chdir(previousCwd);
  }
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    usage();
    return 0;
  }
  const result = runScenario(options);
  process.stdout.write('### Security Assurance Fixture\n');
  process.stdout.write(`- scenario: ${result.scenario}\n`);
  process.stdout.write(`- output: ${result.outputDir}\n`);
  process.stdout.write(`- claims: ${result.summary.claims}\n`);
  process.stdout.write(`- findings: ${result.summary.findings}\n`);
  process.stdout.write(`- needs-human-review: ${result.summary.needsHumanReview}\n`);
  process.stdout.write(`- rejected: ${result.summary.rejected}\n`);
  process.stdout.write(`- out-of-scope: ${result.summary.outOfScope}\n`);
  process.stdout.write(`- high/critical open: ${result.summary.highOrCriticalOpen}\n`);
  process.stdout.write(`- comparison: ${result.summary.compared ? 'ok' : 'skipped'}\n`);
  return 0;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  try {
    process.exitCode = run();
  } catch (error) {
    process.stderr.write(`[security-assurance-fixture] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}
