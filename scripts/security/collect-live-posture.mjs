#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

export const LIVE_POSTURE_SCHEMA_VERSION = 'live-operational-posture/v1';

export const EVIDENCE_DEFINITIONS = [
  {
    id: 'repository',
    label: 'Repository metadata',
    endpoint: (repo) => `repos/${repo}`,
  },
  {
    id: 'branchProtection',
    label: 'Default branch protection',
    endpoint: (repo, context) => `repos/${repo}/branches/${encodeURIComponent(context.defaultBranch)}/protection`,
  },
  {
    id: 'rulesets',
    label: 'Repository rulesets',
    endpoint: (repo) => `repos/${repo}/rulesets?includes_parents=true`,
  },
  {
    id: 'actionsPermissions',
    label: 'Actions repository permissions',
    endpoint: (repo) => `repos/${repo}/actions/permissions`,
  },
  {
    id: 'workflowPermissions',
    label: 'Default workflow token permissions',
    endpoint: (repo) => `repos/${repo}/actions/permissions/workflow`,
  },
  {
    id: 'forkPrApproval',
    label: 'Fork PR workflow approval policy',
    endpoint: (repo) => `repos/${repo}/actions/permissions/fork-pr-contributor-approval`,
  },
  {
    id: 'secrets',
    label: 'Actions secrets inventory',
    endpoint: (repo) => `repos/${repo}/actions/secrets?per_page=1`,
  },
  {
    id: 'variables',
    label: 'Actions variables inventory',
    endpoint: (repo) => `repos/${repo}/actions/variables?per_page=1`,
  },
  {
    id: 'selfHostedRunners',
    label: 'Self-hosted runner inventory',
    endpoint: (repo) => `repos/${repo}/actions/runners?per_page=1`,
  },
  {
    id: 'workflows',
    label: 'Workflow inventory',
    endpoint: (repo) => `repos/${repo}/actions/workflows?per_page=1`,
  },
  {
    id: 'runnerEgress',
    label: 'Runner egress policy evidence',
    endpoint: null,
  },
];

const EVIDENCE_KEYS = EVIDENCE_DEFINITIONS.map((definition) => definition.id);

function usage() {
  process.stdout.write(`Usage: node scripts/security/collect-live-posture.mjs [options]\n\nOptions:\n  --repo <owner/repo>       GitHub repository to inspect (default: GITHUB_REPOSITORY or origin remote)\n  --fixture <file>          Use a deterministic fixture JSON instead of live GitHub API calls\n  --no-live                 Do not call GitHub; emit an explicit missing-live-evidence report\n  --output-json <file>      JSON report path (default: artifacts/security/live-operational-posture.json)\n  --output-md <file>        Markdown report path (default: artifacts/security/live-operational-posture.md)\n  --generated-at <iso>      Deterministic generatedAt timestamp\n  --gh <path>               gh CLI path/name to use for live collection (default: gh)\n  --help                    Show this help\n`);
}

export function parseArgs(argv) {
  const options = {
    repo: process.env.GITHUB_REPOSITORY || '',
    fixture: '',
    noLive: false,
    outputJson: 'artifacts/security/live-operational-posture.json',
    outputMd: 'artifacts/security/live-operational-posture.md',
    generatedAt: '',
    gh: process.env.GH || 'gh',
    help: false,
    unknown: [],
  };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = () => {
      i += 1;
      if (i >= argv.length) throw new Error(`${arg} requires a value`);
      return argv[i];
    };
    if (arg === '--') continue;
    if (arg === '--repo') options.repo = next();
    else if (arg.startsWith('--repo=')) options.repo = arg.slice('--repo='.length);
    else if (arg === '--fixture') options.fixture = next();
    else if (arg.startsWith('--fixture=')) options.fixture = arg.slice('--fixture='.length);
    else if (arg === '--no-live') options.noLive = true;
    else if (arg === '--output-json') options.outputJson = next();
    else if (arg.startsWith('--output-json=')) options.outputJson = arg.slice('--output-json='.length);
    else if (arg === '--output-md') options.outputMd = next();
    else if (arg.startsWith('--output-md=')) options.outputMd = arg.slice('--output-md='.length);
    else if (arg === '--generated-at') options.generatedAt = next();
    else if (arg.startsWith('--generated-at=')) options.generatedAt = arg.slice('--generated-at='.length);
    else if (arg === '--gh') options.gh = next();
    else if (arg.startsWith('--gh=')) options.gh = arg.slice('--gh='.length);
    else if (arg === '--help' || arg === '-h') options.help = true;
    else options.unknown.push(arg);
  }
  return options;
}

function normalizeRepo(value) {
  const repo = String(value ?? '').trim();
  return /^[^/\s]+\/[^/\s]+$/.test(repo) ? repo : '';
}

function inferRepoFromGitRemote() {
  try {
    const remote = execFileSync('git', ['remote', 'get-url', 'origin'], {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
    }).trim();
    const match = remote.match(/github\.com[:/]([^/\s]+)\/([^/\s]+?)(?:\.git)?$/i);
    if (match) return `${match[1]}/${match[2]}`;
  } catch {
    // Keep repo inference best-effort; caller will emit missing live evidence if repo is unavailable.
  }
  return '';
}

function toArray(value) {
  if (Array.isArray(value)) return value;
  if (Array.isArray(value?.rulesets)) return value.rulesets;
  if (Array.isArray(value?.workflows)) return value.workflows;
  if (Array.isArray(value?.runners)) return value.runners;
  return [];
}

function totalCount(value) {
  if (typeof value?.total_count === 'number') return value.total_count;
  const items = toArray(value);
  return items.length;
}

function makeMissingEvidence(id, reason = 'live evidence not collected') {
  const definition = EVIDENCE_DEFINITIONS.find((candidate) => candidate.id === id);
  return {
    id,
    label: definition?.label ?? id,
    status: 'missing',
    summary: reason,
  };
}

function makeCollectedEvidence(id, data, source = 'fixture') {
  const definition = EVIDENCE_DEFINITIONS.find((candidate) => candidate.id === id);
  return {
    id,
    label: definition?.label ?? id,
    status: 'collected',
    source,
    summary: summarizeEvidencePayload(id, data),
    data,
  };
}

function isNormalizedEvidenceEntry(id, value) {
  return Boolean(
    value
      && typeof value === 'object'
      && (value.id === id || typeof value.status === 'string')
      && typeof value.status === 'string',
  );
}

function normalizeFixtureEvidenceEntry(id, value) {
  if (!isNormalizedEvidenceEntry(id, value)) {
    return makeCollectedEvidence(id, value, 'fixture');
  }
  const definition = EVIDENCE_DEFINITIONS.find((candidate) => candidate.id === id);
  return {
    id,
    label: value.label ?? definition?.label ?? id,
    status: value.status,
    ...(value.source ? { source: value.source } : {}),
    summary: value.summary ?? (value.status === 'collected'
      ? summarizeEvidencePayload(id, value.data)
      : 'live evidence not collected'),
    ...(Object.prototype.hasOwnProperty.call(value, 'data') ? { data: value.data } : {}),
  };
}

function summarizeEvidencePayload(id, data) {
  if (id === 'repository') {
    return `defaultBranch=${data?.default_branch ?? data?.defaultBranch ?? 'unknown'}, visibility=${data?.visibility ?? (data?.private ? 'private' : 'unknown')}`;
  }
  if (id === 'branchProtection') {
    const checks = data?.required_status_checks?.checks?.length ?? data?.required_status_checks?.contexts?.length ?? 0;
    const reviews = data?.required_pull_request_reviews?.required_approving_review_count ?? null;
    return `requiredStatusChecks=${checks}, requiredApprovingReviews=${reviews ?? 'unknown'}`;
  }
  if (id === 'rulesets') return `rulesetCount=${totalCount(data)}`;
  if (id === 'actionsPermissions') return `enabled=${String(data?.enabled ?? 'unknown')}, allowedActions=${data?.allowed_actions ?? 'unknown'}`;
  if (id === 'workflowPermissions') {
    return `defaultWorkflowPermissions=${data?.default_workflow_permissions ?? 'unknown'}, canApprovePrReviews=${String(data?.can_approve_pull_request_reviews ?? 'unknown')}`;
  }
  if (id === 'forkPrApproval') return `approvalPolicy=${data?.approval_policy ?? data?.approvalPolicy ?? 'unknown'}`;
  if (id === 'secrets') return `secretCount=${totalCount(data)}`;
  if (id === 'variables') return `variableCount=${totalCount(data)}`;
  if (id === 'selfHostedRunners') return `selfHostedRunnerCount=${totalCount(data)}`;
  if (id === 'workflows') return `workflowCount=${totalCount(data)}`;
  if (id === 'runnerEgress') return data?.summary ?? data?.policy ?? 'runner egress evidence provided';
  return 'evidence collected';
}

export function evidenceFromFixture(fixture = {}) {
  const evidence = {};
  for (const key of EVIDENCE_KEYS) {
    if (Object.prototype.hasOwnProperty.call(fixture, key)) {
      evidence[key] = normalizeFixtureEvidenceEntry(key, fixture[key]);
    } else {
      evidence[key] = makeMissingEvidence(key);
    }
  }
  return evidence;
}

export function missingLiveEvidence(reason = 'live evidence not collected') {
  return Object.fromEntries(EVIDENCE_KEYS.map((key) => [key, makeMissingEvidence(key, reason)]));
}

function runGhApi(gh, endpoint) {
  try {
    const stdout = execFileSync(gh, ['api', endpoint], {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
      env: process.env,
    });
    return { ok: true, data: stdout.trim() ? JSON.parse(stdout) : {} };
  } catch (error) {
    const stderr = typeof error?.stderr === 'string' ? error.stderr.trim() : '';
    return { ok: false, error: stderr || error?.message || String(error) };
  }
}

export function collectLiveEvidence({ repo, gh = 'gh' }) {
  const normalizedRepo = normalizeRepo(repo) || inferRepoFromGitRemote();
  if (!normalizedRepo) {
    return {
      repo: '',
      evidence: missingLiveEvidence('repository was not provided and could not be inferred'),
    };
  }

  const evidence = {};
  const repoResult = runGhApi(gh, `repos/${normalizedRepo}`);
  if (repoResult.ok) {
    evidence.repository = makeCollectedEvidence('repository', repoResult.data, `gh api repos/${normalizedRepo}`);
  } else {
    evidence.repository = makeMissingEvidence('repository', repoResult.error);
  }
  const defaultBranch = repoResult.ok
    ? String(repoResult.data?.default_branch ?? repoResult.data?.defaultBranch ?? 'main')
    : 'main';

  for (const definition of EVIDENCE_DEFINITIONS) {
    if (definition.id === 'repository') continue;
    if (!definition.endpoint) {
      evidence[definition.id] = makeMissingEvidence(definition.id, 'GitHub API cannot determine this control; provide operator evidence or a fixture value.');
      continue;
    }
    const endpoint = definition.endpoint(normalizedRepo, { defaultBranch });
    const result = runGhApi(gh, endpoint);
    evidence[definition.id] = result.ok
      ? makeCollectedEvidence(definition.id, result.data, `gh api ${endpoint}`)
      : makeMissingEvidence(definition.id, result.error);
  }

  return { repo: normalizedRepo, evidence };
}

function evidenceCollected(evidence, key) {
  return evidence?.[key]?.status === 'collected';
}

function branchProtectionSignals(data) {
  const statusCheckCount = data?.required_status_checks?.checks?.length
    ?? data?.required_status_checks?.contexts?.length
    ?? 0;
  const reviewCount = data?.required_pull_request_reviews?.required_approving_review_count ?? 0;
  return { statusCheckCount, reviewCount };
}

function rulesetCount(data) {
  return totalCount(data);
}

function control(id, category, requirement, status, evidenceRefs, operatorAction, notes = []) {
  return { id, category, requirement, status, evidenceRefs, operatorAction, notes };
}

export function buildChecklist(evidence) {
  const controls = [];
  const branchProtection = evidence.branchProtection?.data;
  const branchSignals = branchProtectionSignals(branchProtection);
  const repoRulesetCount = rulesetCount(evidence.rulesets?.data);
  const hasBranchOrRuleset = branchSignals.statusCheckCount > 0 || branchSignals.reviewCount > 0 || repoRulesetCount > 0;
  const branchEvidenceCollected = evidenceCollected(evidence, 'branchProtection') || evidenceCollected(evidence, 'rulesets');

  controls.push(control(
    'branch-ruleset-protection',
    'branch/ruleset protection',
    'Default branch is protected by branch protection or repository rulesets.',
    hasBranchOrRuleset ? 'satisfied' : (branchEvidenceCollected ? 'needs-review' : 'missing-evidence'),
    ['branchProtection', 'rulesets'],
    'Confirm required review, required status checks, and bypass actors in GitHub settings.',
    [`requiredStatusChecks=${branchSignals.statusCheckCount}`, `requiredApprovingReviews=${branchSignals.reviewCount}`, `rulesetCount=${repoRulesetCount}`],
  ));

  controls.push(control(
    'workflow-token-permissions',
    'workflow permissions',
    'Default GITHUB_TOKEN workflow permission is least-privilege and PR review approval by Actions is explicitly reviewed.',
    evidenceCollected(evidence, 'workflowPermissions')
      ? (String(evidence.workflowPermissions.data?.default_workflow_permissions ?? '').toLowerCase() === 'read' ? 'satisfied' : 'needs-review')
      : 'missing-evidence',
    ['workflowPermissions'],
    'Review repository Actions workflow permissions and document any write-token requirement.',
    [evidence.workflowPermissions?.summary ?? 'workflow permission evidence missing'],
  ));

  controls.push(control(
    'actions-approval-policy',
    'actions approval policy',
    'Fork PR workflow approval policy and allowed Actions policy are known.',
    evidenceCollected(evidence, 'forkPrApproval') && evidenceCollected(evidence, 'actionsPermissions') ? 'satisfied' : 'missing-evidence',
    ['forkPrApproval', 'actionsPermissions'],
    'Verify fork PR approval, allowed Actions policy, and any selected-action allowlist.',
    [evidence.forkPrApproval?.summary ?? 'fork PR approval evidence missing', evidence.actionsPermissions?.summary ?? 'actions permission evidence missing'],
  ));

  controls.push(control(
    'secrets-variables-inventory',
    'secrets / variables',
    'Repository Actions secrets and variables inventories are collected by count/source and reviewed without exposing values.',
    evidenceCollected(evidence, 'secrets') && evidenceCollected(evidence, 'variables') ? 'satisfied' : 'missing-evidence',
    ['secrets', 'variables'],
    'Confirm secret/variable count, naming policy, rotation owner, and absence of broad write-token secrets in PR-exposed workflows.',
    [evidence.secrets?.summary ?? 'secrets evidence missing', evidence.variables?.summary ?? 'variables evidence missing'],
  ));

  const runnerCount = totalCount(evidence.selfHostedRunners?.data);
  controls.push(control(
    'runner-inventory',
    'runner posture',
    'Runner inventory is collected and self-hosted runner exposure is explicitly reviewed.',
    evidenceCollected(evidence, 'selfHostedRunners') ? (runnerCount > 0 ? 'needs-review' : 'satisfied') : 'missing-evidence',
    ['selfHostedRunners'],
    'If self-hosted runners exist, document labels, trust boundary, cleanup, network segmentation, and PR exposure policy.',
    [evidence.selfHostedRunners?.summary ?? 'runner inventory evidence missing'],
  ));

  controls.push(control(
    'runner-egress-policy',
    'runner / egress',
    'Runner egress/network policy is recorded or explicitly marked as unavailable from source review.',
    evidenceCollected(evidence, 'runnerEgress') ? 'needs-review' : 'missing-evidence',
    ['runnerEgress'],
    'Attach operator evidence for outbound network restrictions, proxy/DNS controls, and dependency-fetch exceptions.',
    [evidence.runnerEgress?.summary ?? 'runner egress evidence is not available from GitHub source/API alone'],
  ));

  controls.push(control(
    'workflow-inventory',
    'workflow inventory',
    'Workflow inventory is collected so private/operational workflows can be reconciled with source findings.',
    evidenceCollected(evidence, 'workflows') ? 'satisfied' : 'missing-evidence',
    ['workflows'],
    'Review enabled/disabled workflows and private operational workflows against the security finding register.',
    [evidence.workflows?.summary ?? 'workflow inventory evidence missing'],
  ));

  const missingEvidence = Object.values(evidence).filter((item) => item.status !== 'collected').map((item) => item.id);
  controls.push(control(
    'live-evidence-gap-disclosure',
    'residual risk disclosure',
    'Report explicitly states when live operational evidence has not been collected.',
    missingEvidence.length > 0 ? 'missing-evidence' : 'satisfied',
    missingEvidence,
    'Keep source-audit findings open as residual risk until all live controls have operator evidence.',
    missingEvidence.length > 0 ? [`missingEvidence=${missingEvidence.join(', ')}`] : ['all configured live evidence entries collected'],
  ));

  return controls;
}

export function buildPostureReport({ repository, evidence, generatedAt = new Date().toISOString(), evidenceMode = 'not-collected' }) {
  const normalizedRepository = normalizeRepo(repository) || 'unknown/unknown';
  const normalizedEvidence = { ...missingLiveEvidence(), ...evidence };
  const checklist = buildChecklist(normalizedEvidence);
  const missingEvidence = Object.values(normalizedEvidence).filter((item) => item.status !== 'collected').map((item) => item.id);
  return {
    schemaVersion: LIVE_POSTURE_SCHEMA_VERSION,
    generatedAt,
    repository: normalizedRepository,
    evidenceMode,
    evidence: normalizedEvidence,
    checklist,
    summary: {
      totalControls: checklist.length,
      satisfied: checklist.filter((item) => item.status === 'satisfied').length,
      needsReview: checklist.filter((item) => item.status === 'needs-review').length,
      missingEvidence: checklist.filter((item) => item.status === 'missing-evidence').length,
      missingEvidenceIds: missingEvidence,
    },
  };
}

function escapeMarkdown(value) {
  return String(value ?? '').replace(/\|/g, '\\|').replace(/\n/g, ' ');
}

export function renderMarkdown(report) {
  const lines = [];
  lines.push('# Live Operational Posture Audit');
  lines.push('');
  lines.push(`- schemaVersion: \`${report.schemaVersion}\``);
  lines.push(`- generatedAt: \`${report.generatedAt}\``);
  lines.push(`- repository: \`${report.repository}\``);
  lines.push(`- evidenceMode: \`${report.evidenceMode}\``);
  lines.push(`- controls: ${report.summary.satisfied} satisfied / ${report.summary.needsReview} needs review / ${report.summary.missingEvidence} missing evidence`);
  lines.push('');
  if (report.summary.missingEvidenceIds.length > 0) {
    lines.push('> Live evidence not collected for: ' + report.summary.missingEvidenceIds.map((id) => `\`${id}\``).join(', '));
    lines.push('');
  }
  lines.push('## Checklist');
  lines.push('');
  lines.push('| Control | Category | Status | Evidence | Operator action |');
  lines.push('| --- | --- | --- | --- | --- |');
  for (const item of report.checklist) {
    lines.push(`| ${escapeMarkdown(item.requirement)} | ${escapeMarkdown(item.category)} | \`${item.status}\` | ${escapeMarkdown(item.evidenceRefs.join(', ') || '(none)')} | ${escapeMarkdown(item.operatorAction)} |`);
  }
  lines.push('');
  lines.push('## Evidence inventory');
  lines.push('');
  lines.push('| Evidence | Status | Source | Summary |');
  lines.push('| --- | --- | --- | --- |');
  for (const key of EVIDENCE_KEYS) {
    const item = report.evidence[key];
    lines.push(`| ${escapeMarkdown(item.label ?? key)} | \`${item.status}\` | ${escapeMarkdown(item.source ?? '(not collected)')} | ${escapeMarkdown(item.summary ?? '')} |`);
  }
  lines.push('');
  lines.push('## Operator notes / 運用確認メモ');
  lines.push('');
  lines.push('- Source review alone cannot prove branch/ruleset protection, GitHub Actions approval policy, secret/variable inventory, runner segmentation, or egress controls.');
  lines.push('- Live evidence that is unavailable must remain visible as residual risk until a repository operator attaches evidence.');
  lines.push('- ソース監査だけでは branch/ruleset protection、Actions approval policy、secrets/variables、runner 分離、egress control は証明できないため、未取得項目を residual risk として扱う。');
  lines.push('');
  return `${lines.join('\n')}\n`;
}

function writeReport(report, options) {
  const jsonPath = path.resolve(options.outputJson);
  const mdPath = path.resolve(options.outputMd);
  fs.mkdirSync(path.dirname(jsonPath), { recursive: true });
  fs.mkdirSync(path.dirname(mdPath), { recursive: true });
  fs.writeFileSync(jsonPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
  fs.writeFileSync(mdPath, renderMarkdown(report), 'utf8');
  process.stdout.write(`Wrote live posture report: ${jsonPath}\n`);
  process.stdout.write(`Wrote live posture markdown: ${mdPath}\n`);
}

export function main(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    usage();
    return 0;
  }
  if (options.unknown.length > 0) {
    throw new Error(`unknown arguments: ${options.unknown.join(' ')}`);
  }
  const repo = normalizeRepo(options.repo) || inferRepoFromGitRemote();
  if (options.fixture && options.noLive) {
    throw new Error('--fixture and --no-live are mutually exclusive');
  }
  let evidence;
  let evidenceMode;
  let reportRepo = repo;
  if (options.fixture) {
    const fixture = JSON.parse(fs.readFileSync(options.fixture, 'utf8'));
    evidence = evidenceFromFixture(fixture.evidence ?? fixture);
    reportRepo = normalizeRepo(fixture.repositoryFullName ?? fixture.repository ?? reportRepo) || reportRepo;
    evidenceMode = 'fixture';
  } else if (options.noLive) {
    evidence = missingLiveEvidence('live collection was explicitly disabled with --no-live');
    evidenceMode = 'not-collected';
  } else {
    const result = collectLiveEvidence({ repo: reportRepo, gh: options.gh });
    evidence = result.evidence;
    reportRepo = result.repo || reportRepo;
    evidenceMode = 'live';
  }
  const report = buildPostureReport({
    repository: reportRepo,
    evidence,
    generatedAt: options.generatedAt || new Date().toISOString(),
    evidenceMode,
  });
  writeReport(report, options);
  return 0;
}

const currentFile = fileURLToPath(import.meta.url);
if (process.argv[1] && path.resolve(process.argv[1]) === currentFile) {
  try {
    process.exitCode = main(process.argv.slice(2));
  } catch (error) {
    process.stderr.write(`collect-live-posture: ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}
