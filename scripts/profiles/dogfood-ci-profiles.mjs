#!/usr/bin/env node
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { parseArgs } from 'node:util';

const DEFAULT_FIXTURE = 'fixtures/profiles/dogfood/recent-pr-gate-decisions.json';
const DEFAULT_OUTPUT = 'artifacts/profiles/profile-dogfood-report.json';
const DEFAULT_OUTPUT_MD = 'artifacts/profiles/profile-dogfood-report.md';
const BUILTIN_PROFILES = ['minimal', 'standard', 'full'];
const PASSING_CHECK_CONCLUSIONS = new Set(['success', 'skipped', 'neutral']);
const BLOCKING_CHECK_CONCLUSIONS = new Set(['failure', 'cancelled', 'timed_out', 'action_required']);
const PENDING_CHECK_CONCLUSIONS = new Set(['queued', 'pending', 'in_progress', 'requested', 'waiting']);
const SCHEMA_VERSION = 'profile-dogfood-report/v1';

function readJson(filePath) {
  return JSON.parse(readFileSync(filePath, 'utf8'));
}

function readText(filePath) {
  return readFileSync(filePath, 'utf8');
}

function ensureParent(filePath) {
  mkdirSync(path.dirname(path.resolve(filePath)), { recursive: true });
}

function uniqueSorted(values) {
  return Array.from(new Set(values.filter((value) => typeof value === 'string' && value.trim().length > 0).map((value) => value.trim()))).sort();
}

function normalizeConclusion(value) {
  return String(value ?? '').trim().toLowerCase().replace(/-/g, '_');
}

function checkDecision(conclusion) {
  const normalized = normalizeConclusion(conclusion);
  if (PASSING_CHECK_CONCLUSIONS.has(normalized)) return 'pass';
  if (BLOCKING_CHECK_CONCLUSIONS.has(normalized)) return 'block';
  if (PENDING_CHECK_CONCLUSIONS.has(normalized) || !normalized) return 'pending';
  return 'block';
}

function statusForCheck(checks, name) {
  const direct = checks[name];
  if (typeof direct === 'string') return direct;
  if (direct && typeof direct === 'object' && typeof direct.conclusion === 'string') return direct.conclusion;
  return 'missing';
}

function currentDecision(caseEntry) {
  const expected = String(caseEntry.currentCiDecision ?? '').trim().toLowerCase();
  if (['pass', 'block', 'pending'].includes(expected)) return expected;
  throw new Error(`case ${caseEntry.id ?? '(unknown)'} has invalid currentCiDecision: ${caseEntry.currentCiDecision}`);
}

function requiredChecksFromProfile(profile) {
  const deployment = profile.deployment && typeof profile.deployment === 'object' ? profile.deployment : {};
  return uniqueSorted(Array.isArray(deployment.requiredChecks) ? deployment.requiredChecks.map(String) : []);
}

function optionalChecksFromProfile(profile) {
  const deployment = profile.deployment && typeof profile.deployment === 'object' ? profile.deployment : {};
  return uniqueSorted(Array.isArray(deployment.optionalChecks) ? deployment.optionalChecks.map(String) : []);
}

function activeLanesFromProfile(profile) {
  const deployment = profile.deployment && typeof profile.deployment === 'object' ? profile.deployment : {};
  return uniqueSorted(Array.isArray(deployment.activeLanes) ? deployment.activeLanes.map(String) : []);
}

function evidenceForCase(caseEntry, profile) {
  const checks = caseEntry.checks && typeof caseEntry.checks === 'object' ? caseEntry.checks : {};
  const requiredChecks = requiredChecksFromProfile(profile);
  const claimRefs = Array.isArray(profile.claims) ? profile.claims.map((claim) => claim.id).filter(Boolean) : [];
  const firstClaim = claimRefs[0] ?? `${profile.profileId}-dogfood`;
  const evidence = [];
  if (requiredChecks.some((check) => checkDecision(statusForCheck(checks, check)) === 'pass')) {
    evidence.push({
      claimRefs: [firstClaim],
      lane: 'spec',
      kind: 'schema',
      sourceKind: 'spec-derived',
      origin: caseEntry.id,
      status: 'observed',
      artifactPath: caseEntry.sourceArtifact ?? null,
      detail: 'Profile required checks are present in the replay case.',
      generatorLineage: 'profile-dogfood-fixture',
    });
    evidence.push({
      claimRefs: [firstClaim],
      lane: 'behavior',
      kind: 'integration',
      sourceKind: 'runtime-derived',
      origin: caseEntry.id,
      status: 'observed',
      artifactPath: caseEntry.sourceArtifact ?? null,
      detail: 'Current CI decision fixture supplies runtime check conclusions.',
      generatorLineage: 'profile-dogfood-fixture',
    });
  }
  return evidence;
}

function profileDecisionForCase({ core, profile, caseEntry, generatedAt }) {
  const checks = caseEntry.checks && typeof caseEntry.checks === 'object' ? caseEntry.checks : {};
  const requiredChecks = requiredChecksFromProfile(profile);
  const checkResults = requiredChecks.map((name) => {
    const conclusion = statusForCheck(checks, name);
    return { name, conclusion, decision: checkDecision(conclusion) };
  });
  const observedEvidenceIds = checkResults
    .filter((check) => check.decision === 'pass')
    .map((check) => check.name);
  const syntheticPolicy = { schemaVersion: 'profile-ci-checks/v1', requiredEvidence: requiredChecks };
  const policyDecision = core.evaluatePolicyGate({
    policy: syntheticPolicy,
    evidenceIds: observedEvidenceIds,
    generatedAt,
    inputPath: `${profile.profileId}.deployment.requiredChecks`,
    mode: 'strict',
  });
  const hasPending = checkResults.some((check) => check.decision === 'pending');
  const decision = hasPending ? 'pending' : policyDecision.result === 'pass' ? 'pass' : 'block';
  const expected = currentDecision(caseEntry);
  return {
    id: caseEntry.id,
    source: caseEntry.source ?? 'fixture-equivalent',
    sourcePr: caseEntry.sourcePr ?? null,
    currentCiDecision: expected,
    profileDecision: decision,
    drift: expected !== decision,
    requiredChecks: checkResults,
    optionalChecks: optionalChecksFromProfile(profile).map((name) => ({ name, conclusion: statusForCheck(checks, name) })),
    policyDecision,
  };
}

function summarizeCases(cases) {
  return {
    caseCount: cases.length,
    passCount: cases.filter((entry) => entry.profileDecision === 'pass').length,
    blockCount: cases.filter((entry) => entry.profileDecision === 'block').length,
    pendingCount: cases.filter((entry) => entry.profileDecision === 'pending').length,
    driftCount: cases.filter((entry) => entry.drift).length,
  };
}

async function loadCore(coreDist) {
  const coreModulePath = path.resolve(coreDist);
  return import(pathToFileURL(coreModulePath).href);
}

async function loadProfile({ core, profileId, repoRoot }) {
  const sourcePath = path.join(repoRoot, 'profiles', `${profileId}.yaml`);
  const text = readText(sourcePath);
  const profile = core.parseProfile(text);
  const validation = core.validateProfile(profile);
  if (!validation.ok) {
    throw new Error(`Profile validation failed for ${profileId}: ${JSON.stringify(validation.errors, null, 2)}`);
  }
  return { profile, sourcePath: path.relative(repoRoot, sourcePath) };
}

function validateFixture(fixture, fixturePath) {
  if (fixture.schemaVersion !== 'profile-dogfood-replay/v1') {
    throw new Error(`Unsupported fixture schemaVersion in ${fixturePath}: ${fixture.schemaVersion}`);
  }
  if (!Array.isArray(fixture.cases)) {
    throw new Error(`Fixture ${fixturePath} must contain a cases array`);
  }
  if (fixture.cases.length < 20) {
    throw new Error(`Fixture ${fixturePath} must include at least 20 replay cases; found ${fixture.cases.length}`);
  }
}

function parseProfileSelection(value) {
  const raw = String(value || 'all').trim();
  const selected = raw === 'all'
    ? BUILTIN_PROFILES
    : raw.split(',').map((entry) => entry.trim()).filter(Boolean);
  for (const profile of selected) {
    if (!BUILTIN_PROFILES.includes(profile)) {
      throw new Error(`Unsupported profile for dogfood replay: ${profile}`);
    }
  }
  return selected;
}

export async function buildDogfoodReport(options = {}) {
  const repoRoot = path.resolve(options.repoRoot ?? process.cwd());
  const fixturePath = path.resolve(repoRoot, options.fixture ?? DEFAULT_FIXTURE);
  const coreDist = path.resolve(repoRoot, options.coreDist ?? 'packages/core/dist/index.js');
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const fixture = readJson(fixturePath);
  validateFixture(fixture, fixturePath);
  const selectedProfiles = parseProfileSelection(options.profile ?? 'all');
  const core = await loadCore(coreDist);
  const profileReports = [];

  for (const profileId of selectedProfiles) {
    const { profile, sourcePath } = await loadProfile({ core, profileId, repoRoot });
    const replayCases = fixture.cases.map((caseEntry) => profileDecisionForCase({ core, profile, caseEntry, generatedAt }));
    const assuranceSummary = core.aggregateLanes({
      profile,
      generatedAt,
      evidence: fixture.cases.flatMap((caseEntry) => evidenceForCase(caseEntry, profile)),
      assuranceProfilePath: sourcePath,
      inputs: {
        evidenceManifests: [path.relative(repoRoot, fixturePath)],
      },
    });
    profileReports.push({
      profileId,
      sourcePath,
      mapsToReadmeProfile: profile.deployment?.mapsToReadmeProfile ?? null,
      requiredChecks: requiredChecksFromProfile(profile),
      optionalChecks: optionalChecksFromProfile(profile),
      activeLanes: activeLanesFromProfile(profile),
      assuranceSummary: {
        claimCount: assuranceSummary.summary.claimCount,
        satisfiedClaims: assuranceSummary.summary.satisfiedClaims,
        warningClaims: assuranceSummary.summary.warningClaims,
        warningCount: assuranceSummary.summary.warningCount,
      },
      summary: summarizeCases(replayCases),
      cases: replayCases,
    });
  }

  const driftCount = profileReports.reduce((sum, profile) => sum + profile.summary.driftCount, 0);
  return {
    schemaVersion: SCHEMA_VERSION,
    generatedAt,
    status: driftCount === 0 ? 'pass' : 'fail',
    fixture: {
      path: path.relative(repoRoot, fixturePath),
      schemaVersion: fixture.schemaVersion,
      mode: fixture.coverage?.mode ?? 'unknown',
      targetRecentPrCount: fixture.coverage?.targetRecentPrCount ?? 20,
      documentedReason: fixture.coverage?.documentedReason ?? null,
      caseCount: fixture.cases.length,
    },
    ciProfileMapping: {
      verifyLite: 'minimal',
      currentPrVerification: 'standard',
      nightlyAndLabelGatedHeavyLanes: 'full',
    },
    summary: {
      profileCount: profileReports.length,
      replayCoverageCount: fixture.cases.length,
      driftCount,
    },
    profiles: profileReports,
  };
}

export function renderMarkdown(report) {
  const lines = [
    '# Deploy-time profile dogfood report',
    '',
    `- Status: ${report.status}`,
    `- Fixture: ${report.fixture.path}`,
    `- Coverage: ${report.fixture.caseCount}/${report.fixture.targetRecentPrCount} ${report.fixture.mode}`,
    `- Drift count: ${report.summary.driftCount}`,
    '',
    '## CI profile mapping',
    '',
    `- Verify Lite: ${report.ciProfileMapping.verifyLite}`,
    `- Current PR verification: ${report.ciProfileMapping.currentPrVerification}`,
    `- Nightly / label-gated heavy lanes: ${report.ciProfileMapping.nightlyAndLabelGatedHeavyLanes}`,
    '',
    '## Profile replay results',
    '',
    '| Profile | README mapping | Required checks | Cases | Drift |',
    '| --- | --- | --- | ---: | ---: |',
  ];
  for (const profile of report.profiles) {
    lines.push(`| ${profile.profileId} | ${profile.mapsToReadmeProfile ?? 'n/a'} | ${profile.requiredChecks.join(', ') || 'none'} | ${profile.summary.caseCount} | ${profile.summary.driftCount} |`);
  }
  const drifts = report.profiles.flatMap((profile) => profile.cases.filter((caseEntry) => caseEntry.drift).map((caseEntry) => ({ profile: profile.profileId, ...caseEntry })));
  if (drifts.length > 0) {
    lines.push('', '## Drift findings', '');
    for (const drift of drifts) {
      lines.push(`- ${drift.profile}/${drift.id}: current=${drift.currentCiDecision}, profile=${drift.profileDecision}`);
    }
  } else {
    lines.push('', 'No drift detected in replay fixture.');
  }
  return `${lines.join('\n')}\n`;
}

export function parseCli(argv) {
  const args = argv.filter((arg) => arg !== '--');
  const parsed = parseArgs({
    args,
    options: {
      profile: { type: 'string', default: 'all' },
      fixture: { type: 'string', default: DEFAULT_FIXTURE },
      out: { type: 'string', default: DEFAULT_OUTPUT },
      'out-md': { type: 'string', default: DEFAULT_OUTPUT_MD },
      'core-dist': { type: 'string', default: 'packages/core/dist/index.js' },
      'no-write': { type: 'boolean', default: false },
      help: { type: 'boolean', short: 'h', default: false },
    },
    strict: true,
    allowPositionals: false,
  });
  return parsed.values;
}

function printHelp() {
  process.stdout.write(`Usage: node scripts/profiles/dogfood-ci-profiles.mjs [--profile minimal|standard|full|all] [--fixture <path>] [--out <path>] [--out-md <path>]\n\nRuns deploy-time profile replay through @ae-framework/core and compares profile-derived required-check decisions with the current CI decision fixture.\n`);
}

export async function runCli(argv = process.argv.slice(2)) {
  const options = parseCli(argv);
  if (options.help) {
    printHelp();
    return 0;
  }
  const report = await buildDogfoodReport({
    profile: options.profile,
    fixture: options.fixture,
    coreDist: options['core-dist'],
  });
  if (!options['no-write']) {
    ensureParent(options.out);
    writeFileSync(options.out, `${JSON.stringify(report, null, 2)}\n`);
    ensureParent(options['out-md']);
    writeFileSync(options['out-md'], renderMarkdown(report));
  }
  process.stdout.write(`profile dogfood: ${report.status}; profiles=${report.summary.profileCount}; cases=${report.summary.replayCoverageCount}; drift=${report.summary.driftCount}\n`);
  return report.status === 'pass' ? 0 : 1;
}

function isCliInvocation(argv = process.argv) {
  return Boolean(argv[1]) && import.meta.url === pathToFileURL(path.resolve(argv[1])).href;
}

if (isCliInvocation()) {
  runCli().then((exitCode) => {
    process.exit(exitCode);
  }).catch((error) => {
    console.error(error instanceof Error ? error.message : String(error));
    process.exit(1);
  });
}
