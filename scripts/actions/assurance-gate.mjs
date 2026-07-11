#!/usr/bin/env node
import { existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { performance } from 'node:perf_hooks';
import process from 'node:process';
import { parseArgs } from 'node:util';

const BUILTIN_PROFILES = new Set(['minimal', 'standard', 'full']);
const SCHEMA_BY_VERSION = new Map([
  ['assurance-summary/v1', 'assurance-summary'],
  ['claim-evidence-manifest/v1', 'claim-evidence-manifest'],
  ['change-package/v2', 'change-package-v2'],
  ['ae-handoff/v1', 'ae-handoff'],
  ['policy-decision/v1', 'policy-decision-v1'],
  ['policy-gate-summary/v1', 'policy-gate-summary-v1'],
  ['verify-lite-run-summary/v1', 'verify-lite-run-summary'],
  ['producer-normalization-summary/v1', 'producer-normalization-summary'],
]);

const SCHEMA_BY_CONTRACT_ID = new Map([
  ['policy-decision.v1', 'policy-decision-v1'],
  ['policy-gate-summary.v1', 'policy-gate-summary-v1'],
]);

const SEMVER_SCHEMA_VERSION = /^\d+\.\d+\.\d+$/u;

function parseBoolean(value, defaultValue) {
  if (value === undefined || value === null || value === '') return defaultValue;
  return ['1', 'true', 'yes', 'on'].includes(String(value).trim().toLowerCase());
}

function parseCli(argv) {
  const parsed = parseArgs({
    args: argv,
    options: {
      profile: { type: 'string', default: 'minimal' },
      'artifacts-dir': { type: 'string', default: 'artifacts' },
      policy: { type: 'string' },
      'output-dir': { type: 'string', default: 'artifacts/assurance-gate' },
      workspace: { type: 'string' },
      'action-repo': { type: 'string' },
      environment: { type: 'string' },
      'fail-on-block': { type: 'string', default: 'true' },
      'timing-output': { type: 'string' },
    },
    strict: true,
    allowPositionals: false,
  });
  return parsed.values;
}

function hasActionRepoMarkers(candidate) {
  return existsSync(path.join(candidate, 'packages', 'core', 'package.json'))
    && existsSync(path.join(candidate, 'profiles', 'minimal.yaml'))
    && existsSync(path.join(candidate, 'policy', 'release-policy.yml'));
}

function repoRootFromActionPath() {
  if (!process.env.GITHUB_ACTION_PATH) return process.cwd();
  let candidate = path.resolve(process.env.GITHUB_ACTION_PATH);
  for (let depth = 0; depth < 6; depth += 1) {
    if (hasActionRepoMarkers(candidate)) return candidate;
    const parent = path.dirname(candidate);
    if (parent === candidate) break;
    candidate = parent;
  }
  return path.resolve(process.env.GITHUB_ACTION_PATH, '..', '..', '..');
}

function assertContained(root, candidate, label) {
  const resolvedRoot = path.resolve(root);
  const resolvedCandidate = path.resolve(candidate);
  const relative = path.relative(resolvedRoot, resolvedCandidate);
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`${label} must be inside ${resolvedRoot}: ${resolvedCandidate}`);
  }
  return resolvedCandidate;
}

function resolveWorkspacePath(workspace, value, label) {
  const candidate = path.isAbsolute(value) ? value : path.join(workspace, value);
  return assertContained(workspace, candidate, label);
}

function isContainedPath(root, candidate) {
  const relative = path.relative(path.resolve(root), path.resolve(candidate));
  return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
}

function readJson(filePath) {
  return JSON.parse(readFileSync(filePath, 'utf8'));
}

function collectJsonFiles(dir) {
  if (!existsSync(dir)) return [];
  const entries = readdirSync(dir, { withFileTypes: true });
  const files = [];
  for (const entry of entries) {
    const target = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files.push(...collectJsonFiles(target));
    } else if (entry.isFile() && entry.name.endsWith('.json')) {
      files.push(target);
    }
  }
  return files.sort();
}

function normalizeEvidenceArray(value) {
  return Array.isArray(value) ? value.filter((entry) => entry && typeof entry === 'object') : [];
}

function normalizeStringArray(value) {
  return Array.isArray(value)
    ? value.map((entry) => String(entry).trim()).filter(Boolean)
    : [];
}

function loadEvidenceBundle(artifactsDir) {
  const evidenceFile = path.join(artifactsDir, 'evidence.json');
  const defaultBundle = { evidence: [], policyEvidence: [], inputs: {}, source: null };
  if (!existsSync(evidenceFile)) return defaultBundle;
  const payload = readJson(evidenceFile);
  return {
    evidence: normalizeEvidenceArray(payload.evidence),
    policyEvidence: normalizeStringArray(payload.policyEvidence),
    inputs: payload.inputs && typeof payload.inputs === 'object' && !Array.isArray(payload.inputs) ? payload.inputs : {},
    source: evidenceFile,
  };
}

function discoverPolicyEvidenceFromArtifacts(jsonFiles) {
  const evidence = [];
  for (const filePath of jsonFiles) {
    const base = path.basename(filePath, '.json');
    if (base === 'evidence') continue;
    try {
      const payload = readJson(filePath);
      if (typeof payload.policyEvidenceId === 'string') evidence.push(payload.policyEvidenceId);
      if (typeof payload.evidenceId === 'string') evidence.push(payload.evidenceId);
    } catch {
      // Validation reports malformed JSON separately; discovery stays best-effort.
    }
  }
  return evidence;
}

function semverSchemaName(payload) {
  if (!SEMVER_SCHEMA_VERSION.test(String(payload.schemaVersion ?? ''))) return undefined;
  if ('timestamp' in payload && 'metadata' in payload && 'flags' in payload && 'steps' in payload && 'artifacts' in payload) {
    return 'verify-lite-run-summary';
  }
  if ('source' in payload && 'generatedAt' in payload && 'traceCorrelation' in payload && 'summary' in payload) {
    return 'envelope';
  }
  return undefined;
}

function schemaNameForArtifact(payload) {
  return SCHEMA_BY_VERSION.get(String(payload.schemaVersion ?? ''))
    ?? SCHEMA_BY_CONTRACT_ID.get(String(payload.contractId ?? ''))
    ?? semverSchemaName(payload);
}

function validateArtifacts(jsonFiles, validateWithSchema) {
  const validated = [];
  const warnings = [];
  const errors = [];
  for (const filePath of jsonFiles) {
    try {
      const payload = readJson(filePath);
      const schemaName = schemaNameForArtifact(payload);
      if (!schemaName) {
        warnings.push({ file: filePath, message: 'No curated schema mapping for artifact schemaVersion or contractId.' });
        continue;
      }
      const result = validateWithSchema(schemaName, payload);
      if (result.ok) {
        validated.push({ file: filePath, schema: schemaName });
      } else {
        errors.push({ file: filePath, schema: schemaName, errors: result.errors });
      }
    } catch (error) {
      errors.push({ file: filePath, errors: [{ message: error instanceof Error ? error.message : String(error) }] });
    }
  }
  return { validated, warnings, errors };
}

function resolveProfilePath(actionRepo, workspace, profile) {
  if (BUILTIN_PROFILES.has(profile)) {
    return {
      profilePath: path.join(actionRepo, 'profiles', `${profile}.yaml`),
      profileLabel: `profiles/${profile}.yaml`,
      builtin: true,
    };
  }
  const profilePath = resolveWorkspacePath(workspace, profile, 'custom profile');
  return { profilePath, profileLabel: path.relative(workspace, profilePath), builtin: false };
}

function resolvePolicyPath({ actionRepo, workspace, profilePath, builtin, profile, policyInput }) {
  if (policyInput) return resolveWorkspacePath(workspace, policyInput, 'policy');
  const deployment = profile.deployment && typeof profile.deployment === 'object' ? profile.deployment : {};
  const gatePolicy = deployment.gatePolicy && typeof deployment.gatePolicy === 'object' ? deployment.gatePolicy : {};
  const source = typeof gatePolicy.source === 'string' ? gatePolicy.source : 'policy/release-policy.yml';
  if (builtin) return path.join(actionRepo, source);
  const candidate = path.isAbsolute(source) ? source : path.resolve(path.dirname(profilePath), source);
  return assertContained(workspace, candidate, 'custom profile policy');
}

function writeGithubOutput(values) {
  const outputPath = process.env.GITHUB_OUTPUT;
  if (!outputPath) return;
  const lines = [];
  for (const [key, value] of Object.entries(values)) {
    lines.push(`${key}=${String(value).replace(/\n/g, '%0A')}`);
  }
  writeFileSync(outputPath, `${lines.join('\n')}\n`, { flag: 'a' });
}

async function main() {
  const gateStartedAt = performance.now();
  const options = parseCli(process.argv.slice(2));
  const workspace = path.resolve(options.workspace ?? process.env.GITHUB_WORKSPACE ?? process.cwd());
  const actionRepo = path.resolve(options['action-repo'] ?? repoRootFromActionPath());
  const outputDir = resolveWorkspacePath(workspace, options['output-dir'], 'output directory');
  const artifactsDir = resolveWorkspacePath(workspace, options['artifacts-dir'], 'artifacts directory');
  const failOnBlock = parseBoolean(options['fail-on-block'], true);
  const timingOutputPath = options['timing-output']
    ? resolveWorkspacePath(workspace, options['timing-output'], 'timing output')
    : null;
  const coreModulePath = path.join(actionRepo, 'packages', 'core', 'dist', 'index.js');

  if (!existsSync(coreModulePath)) {
    throw new Error(`@ae-framework/core build output not found: ${coreModulePath}. Run pnpm --filter @ae-framework/core run build in the action repository first.`);
  }

  const core = await import(coreModulePath);
  const { profilePath, profileLabel, builtin } = resolveProfilePath(actionRepo, workspace, options.profile);
  if (!existsSync(profilePath)) throw new Error(`Profile not found: ${profilePath}`);

  const profileText = readFileSync(profilePath, 'utf8');
  const profile = core.parseProfile(profileText);
  const profileValidation = core.validateProfile(profile);
  if (!profileValidation.ok) {
    throw new Error(`Profile validation failed: ${JSON.stringify(profileValidation.errors, null, 2)}`);
  }

  const policyPath = resolvePolicyPath({
    actionRepo,
    workspace,
    profilePath,
    builtin,
    profile,
    policyInput: options.policy,
  });
  if (!existsSync(policyPath)) throw new Error(`Policy not found: ${policyPath}`);

  const jsonFiles = collectJsonFiles(artifactsDir).filter((filePath) => !isContainedPath(outputDir, filePath));
  const evidenceBundle = loadEvidenceBundle(artifactsDir);
  const artifactValidation = validateArtifacts(jsonFiles, core.validateWithSchema);
  const policyEvidence = Array.from(new Set([
    ...evidenceBundle.policyEvidence,
    ...discoverPolicyEvidenceFromArtifacts(jsonFiles),
  ])).sort();
  const generatedAt = new Date().toISOString();

  const summary = core.aggregateLanes({
    profile,
    generatedAt,
    evidence: evidenceBundle.evidence,
    assuranceProfilePath: profileLabel,
    inputs: evidenceBundle.inputs,
  });
  const policyText = readFileSync(policyPath, 'utf8');
  const policyPayload = core.parseYamlOrJson(policyText);
  const policyValidation = core.validateWithSchema('release-policy', policyPayload);
  if (!policyValidation.ok) {
    throw new Error(`Policy validation failed: ${JSON.stringify(policyValidation.errors, null, 2)}`);
  }

  const policyDecision = core.evaluatePolicyGate({
    policy: policyPayload,
    evidenceIds: policyEvidence,
    generatedAt,
    inputPath: builtin ? path.relative(actionRepo, policyPath) : path.relative(workspace, policyPath),
    environment: options.environment,
  });
  const reviewSurfaceStartedAt = performance.now();
  const reviewSurface = core.renderReviewSurface(summary, { policyDecision });
  const reviewSurfaceRenderingMs = performance.now() - reviewSurfaceStartedAt;

  mkdirSync(outputDir, { recursive: true });
  const summaryPath = path.join(outputDir, 'assurance-summary.json');
  const policyDecisionPath = path.join(outputDir, 'policy-decision.json');
  const reviewPath = path.join(outputDir, 'review-surface.md');
  const gateResultPath = path.join(outputDir, 'gate-result.json');
  const gateResult = {
    schemaVersion: 'assurance-gate-result/v1',
    generatedAt,
    profile: options.profile,
    profilePath: profileLabel,
    artifactsDir: path.relative(workspace, artifactsDir),
    outputDir: path.relative(workspace, outputDir),
    evidenceSource: evidenceBundle.source ? path.relative(workspace, evidenceBundle.source) : null,
    artifactValidation: {
      validatedCount: artifactValidation.validated.length,
      warningCount: artifactValidation.warnings.length,
      errorCount: artifactValidation.errors.length,
      validated: artifactValidation.validated.map((entry) => ({ ...entry, file: path.relative(workspace, entry.file) })),
      warnings: artifactValidation.warnings.map((entry) => ({ ...entry, file: path.relative(workspace, entry.file) })),
      errors: artifactValidation.errors.map((entry) => ({ ...entry, file: path.relative(workspace, entry.file) })),
    },
    policyEvidence,
    policyResult: policyDecision.result,
    policyDecisionPath: path.relative(workspace, policyDecisionPath),
    assuranceSummaryPath: path.relative(workspace, summaryPath),
    reviewSurfacePath: path.relative(workspace, reviewPath),
  };

  writeFileSync(summaryPath, `${JSON.stringify(summary, null, 2)}\n`);
  writeFileSync(policyDecisionPath, `${JSON.stringify(policyDecision, null, 2)}\n`);
  writeFileSync(reviewPath, reviewSurface);
  writeFileSync(gateResultPath, `${JSON.stringify(gateResult, null, 2)}\n`);
  if (timingOutputPath) {
    mkdirSync(path.dirname(timingOutputPath), { recursive: true });
    writeFileSync(timingOutputPath, `${JSON.stringify({
      schemaVersion: 'assurance-gate-internal-timing/v1',
      generatedAt,
      reviewSurfaceRenderingMs,
      gateProcessElapsedMs: performance.now() - gateStartedAt,
    }, null, 2)}\n`);
  }
  writeGithubOutput({
    'gate-result': policyDecision.result,
    'gate-result-path': path.relative(workspace, gateResultPath),
    'assurance-summary-path': path.relative(workspace, summaryPath),
    'policy-decision-path': path.relative(workspace, policyDecisionPath),
    'review-surface-path': path.relative(workspace, reviewPath),
  });

  console.log(`ae-framework assurance gate: ${policyDecision.result}`);
  console.log(`profile: ${options.profile}`);
  console.log(`policy evidence: ${policyEvidence.join(', ') || '(none)'}`);
  console.log(`review surface: ${reviewPath}`);

  if (artifactValidation.errors.length > 0) {
    console.error(JSON.stringify(artifactValidation.errors, null, 2));
    process.exit(1);
  }
  if (failOnBlock && policyDecision.result === 'block') {
    console.error(`policy blocked: missing evidence ${policyDecision.missingEvidence.join(', ') || '(none)'}`);
    process.exit(1);
  }
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exit(1);
});
