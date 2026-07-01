#!/usr/bin/env node
import { existsSync, lstatSync, mkdirSync, readFileSync, realpathSync, statSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const DEFAULT_FIXTURE = 'fixtures/metrics/req2run/offline-input.json';
const DEFAULT_OUTPUT_JSON = 'artifacts/metrics/req2run-metrics.json';
const DEFAULT_OUTPUT_MD = 'artifacts/metrics/req2run-metrics.md';
const NOT_COLLECTED = 'not_collected';
const UNKNOWN = 'unknown';

const METRIC_DEFINITIONS = {
  time_to_first_runnable_verification_minutes: {
    reviewerQuestion: 'How long did it take for a requirement to produce the first runnable verification artifact?',
    calculationMethod: 'Minutes between requirementAcceptedAt and the first passing runnable verification timestamp.',
    interpretation: 'Lower values can indicate that the reference flow turns requirements into runnable evidence with less setup friction.',
    limitation: 'Sensitive to queueing, task size, CI availability, and whether timestamps are synthetic, redacted, or live.',
  },
  spec_task_evidence_coverage: {
    reviewerQuestion: 'How many spec or plan tasks have at least one linked evidence artifact?',
    calculationMethod: 'tasks with one or more evidenceRefs divided by all required tasks in the measurement fixture.',
    interpretation: 'Higher coverage means more of the planned work is reviewable through evidence rather than prose alone.',
    limitation: 'Coverage says evidence exists; it does not prove the evidence is sufficient, current, or correct.',
  },
  deterministic_replay_pass_rate: {
    reviewerQuestion: 'Can the same local inputs be replayed deterministically?',
    calculationMethod: 'passing deterministic replay attempts divided by all replay attempts in the fixture.',
    interpretation: 'Higher pass rate supports adoption readiness because reviewers can reproduce the reported flow locally.',
    limitation: 'Fixture replay is not a live external-agent benchmark and does not measure raw coding-agent quality.',
  },
  manual_intervention_count: {
    reviewerQuestion: 'How many human interventions were required before runnable evidence existed?',
    calculationMethod: 'Count of manualInterventions recorded in the measurement fixture.',
    interpretation: 'Lower counts can indicate a smoother path, while non-zero counts identify where onboarding or docs should improve.',
    limitation: 'Manual intervention taxonomy must be stable before comparing teams or repositories.',
  },
  evidence_review_completeness: {
    reviewerQuestion: 'How complete is the review-ready evidence set for the requirement-to-run path?',
    calculationMethod: 'required evidence items marked present and reviewed divided by all required evidence items.',
    interpretation: 'Higher completeness means the PR review surface has fewer missing local artifacts to inspect.',
    limitation: 'Completeness does not replace human approval and must not be promoted to a blocking gate without policy work.',
  },
};

function usage() {
  process.stdout.write(`Usage: node scripts/metrics/collect-req2run-metrics.mjs [options]\n\nOptions:\n  --fixture <path>              Offline req2run measurement fixture (default: ${DEFAULT_FIXTURE}).\n  --project-root, --work <path> Repository root for path containment (default: .).\n  --generated-at <iso-date>     Deterministic generatedAt timestamp.\n  --output-json <path>          Output JSON path (default: ${DEFAULT_OUTPUT_JSON}).\n  --output-md <path>            Output Markdown path (default: ${DEFAULT_OUTPUT_MD}).\n  --no-write                    Validate and render in memory without writing outputs.\n  --help                        Show this help.\n\nThe collector is offline-only. It reads local fixtures and artifact references, never calls live external agent APIs, and emits report-only adoption-readiness evidence.\n`);
}

function requireValue(argv, index, flag) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`${flag} requires a value`);
  }
  return next;
}

function ensureDateTime(value, flag = 'date-time') {
  const raw = String(value ?? '').trim();
  if (!Number.isFinite(Date.parse(raw))) {
    throw new Error(`${flag} must be an ISO date-time: ${raw || '(empty)'}`);
  }
  return new Date(raw).toISOString();
}

function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    projectRoot: '.',
    fixture: DEFAULT_FIXTURE,
    generatedAt: null,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    noWrite: false,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--no-write') {
      options.noWrite = true;
      continue;
    }
    if (arg === '--project-root' || arg === '--work') {
      options.projectRoot = requireValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--fixture') {
      options.fixture = requireValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = ensureDateTime(requireValue(argv, index, arg), arg);
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = requireValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = requireValue(argv, index, arg);
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (options.help) return options;
  const projectRoot = path.resolve(options.projectRoot || '.');
  return {
    ...options,
    projectRoot,
    fixture: assertProjectContainedPath(projectRoot, options.fixture, '--fixture'),
    outputJson: assertProjectContainedPath(projectRoot, options.outputJson, '--output-json'),
    outputMd: assertProjectContainedPath(projectRoot, options.outputMd, '--output-md'),
  };
}

function isPathWithin(parentPath, childPath) {
  const relative = path.relative(path.resolve(parentPath), path.resolve(childPath));
  return relative === '' || (relative !== '' && !relative.startsWith('..') && !path.isAbsolute(relative));
}

function lstatIfExists(filePath) {
  try {
    return lstatSync(filePath);
  } catch (error) {
    if (error?.code === 'ENOENT') return null;
    throw error;
  }
}

function realpathIfExists(filePath) {
  try {
    return realpathSync.native(filePath);
  } catch (error) {
    if (error?.code === 'ENOENT') return null;
    throw error;
  }
}

function nearestExistingAncestor(filePath) {
  let cursor = path.resolve(filePath);
  while (!lstatIfExists(cursor)) {
    const parent = path.dirname(cursor);
    if (parent === cursor) return null;
    cursor = parent;
  }
  return cursor;
}

function stripFragment(filePath) {
  return String(filePath ?? '').split('#')[0];
}

function assertProjectContainedPath(projectRoot, filePath, label) {
  const root = path.resolve(projectRoot);
  const rawPath = stripFragment(filePath);
  if (!rawPath) return null;
  const resolved = path.resolve(root, rawPath);
  if (!isPathWithin(root, resolved)) {
    throw new Error(`${label} must stay within --project-root: ${filePath}`);
  }
  const existingAncestor = nearestExistingAncestor(resolved);
  if (!existingAncestor) return resolved;
  const realRoot = existsSync(root) ? realpathSync.native(root) : root;
  const realAncestor = realpathIfExists(existingAncestor);
  if (realAncestor && !isPathWithin(realRoot, realAncestor)) {
    throw new Error(`${label} resolves outside --project-root: ${filePath}`);
  }
  return resolved;
}

function ensureProjectContainedOutputPath(projectRoot, filePath, label) {
  const resolved = assertProjectContainedPath(projectRoot, filePath, label);
  const outputStat = lstatIfExists(resolved);
  if (outputStat?.isSymbolicLink()) {
    throw new Error(`${label} must not be a symbolic link: ${filePath}`);
  }
  const outputDir = path.dirname(resolved);
  const existingAncestor = nearestExistingAncestor(outputDir);
  if (!existingAncestor) {
    throw new Error(`${label} has no existing ancestor under --project-root: ${filePath}`);
  }
  const realProjectRoot = realpathSync.native(path.resolve(projectRoot));
  const realAncestor = realpathIfExists(existingAncestor);
  if (!realAncestor || !isPathWithin(realProjectRoot, realAncestor)) {
    throw new Error(`${label} output directory resolves outside --project-root: ${filePath}`);
  }
  mkdirSync(outputDir, { recursive: true });
  const realOutputDir = realpathSync.native(outputDir);
  if (!isPathWithin(realProjectRoot, realOutputDir)) {
    throw new Error(`${label} output directory resolves outside --project-root: ${filePath}`);
  }
  const outputStatAfterMkdir = lstatIfExists(resolved);
  if (outputStatAfterMkdir?.isSymbolicLink()) {
    throw new Error(`${label} must not be a symbolic link: ${filePath}`);
  }
  return resolved;
}

function toPosix(value) {
  return String(value).split(path.sep).join('/');
}

function displayPath(filePath, rootDir = process.cwd()) {
  if (!filePath) return null;
  const root = path.resolve(rootDir);
  const rawPath = stripFragment(filePath);
  const resolved = path.resolve(root, rawPath);
  const relative = path.relative(root, resolved);
  const rendered = relative && !relative.startsWith('..') && !path.isAbsolute(relative) ? relative : resolved;
  const fragment = String(filePath).includes('#') ? `#${String(filePath).split('#').slice(1).join('#')}` : '';
  return `${toPosix(rendered)}${fragment}`;
}

function readJson(filePath) {
  return JSON.parse(readFileSync(filePath, 'utf8'));
}

function writeJson(filePath, payload) {
  writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
}

function writeText(filePath, content) {
  writeFileSync(filePath, content, 'utf8');
}

function asArray(value) {
  return Array.isArray(value) ? value : [];
}

function uniqueStrings(values) {
  return [...new Set(values.map((value) => String(value ?? '').trim()).filter(Boolean))];
}

function metricNumber(value) {
  return Number.isFinite(value) ? Math.round(value * 100) / 100 : NOT_COLLECTED;
}

function ratio(numerator, denominator) {
  if (!Number.isInteger(denominator) || denominator < 1) return null;
  return Math.round((numerator / denominator) * 10000) / 10000;
}

function minutesBetween(start, end) {
  if (!start || !end) return null;
  const startMs = Date.parse(start);
  const endMs = Date.parse(end);
  if (!Number.isFinite(startMs) || !Number.isFinite(endMs) || endMs < startMs) return null;
  return Math.round(((endMs - startMs) / 60000) * 100) / 100;
}

function isPassStatus(value) {
  return ['pass', 'passed', 'success', 'succeeded'].includes(String(value ?? '').toLowerCase());
}

function isReviewedEvidence(item) {
  return item?.present === true && ['reviewed', 'accepted', 'satisfied', 'pass', 'passed'].includes(String(item?.reviewStatus ?? '').toLowerCase());
}

function normalizeSourceArtifacts(fixture, projectRoot, limitations) {
  const artifacts = asArray(fixture.sourceArtifacts).map((artifact) => {
    const rawPath = artifact?.path ?? null;
    const containedPath = rawPath ? assertProjectContainedPath(projectRoot, rawPath, `source artifact ${artifact?.id ?? '(unknown)'}`) : null;
    const exists = containedPath ? existsSync(containedPath) && statSync(containedPath).isFile() : false;
    const present = artifact?.present !== false && exists;
    if (artifact?.required !== false && !present) {
      limitations.push(`required source artifact is missing: ${artifact?.id ?? rawPath ?? '(unknown)'}`);
    }
    return {
      id: String(artifact?.id ?? rawPath ?? UNKNOWN),
      kind: String(artifact?.kind ?? UNKNOWN),
      path: rawPath ? displayPath(rawPath, projectRoot) : null,
      present,
      required: artifact?.required !== false,
      schemaVersion: artifact?.schemaVersion ?? null,
      description: artifact?.description ?? '',
    };
  });
  return artifacts;
}

function taskCoverage(tasks) {
  const requiredTasks = tasks.filter((task) => task?.required !== false);
  const numerator = requiredTasks.filter((task) => asArray(task?.evidenceRefs).length > 0).length;
  return {
    numerator,
    denominator: requiredTasks.length,
    ratio: ratio(numerator, requiredTasks.length),
    missingTaskIds: requiredTasks.filter((task) => asArray(task?.evidenceRefs).length === 0).map((task) => String(task.id ?? UNKNOWN)),
  };
}

function replayPassRate(replayRuns) {
  const attempts = asArray(replayRuns);
  const passed = attempts.filter((run) => isPassStatus(run?.status) || run?.passed === true).length;
  return {
    numerator: passed,
    denominator: attempts.length,
    ratio: ratio(passed, attempts.length),
    failedAttemptIds: attempts.filter((run) => !(isPassStatus(run?.status) || run?.passed === true)).map((run) => String(run.id ?? UNKNOWN)),
  };
}

function evidenceReviewCompleteness(evidenceItems) {
  const requiredItems = asArray(evidenceItems).filter((item) => item?.required !== false);
  const reviewed = requiredItems.filter(isReviewedEvidence).length;
  return {
    numerator: reviewed,
    denominator: requiredItems.length,
    ratio: ratio(reviewed, requiredItems.length),
    missingEvidenceIds: requiredItems.filter((item) => !isReviewedEvidence(item)).map((item) => String(item.id ?? UNKNOWN)),
  };
}

function inferFirstRunnableVerificationAt(fixture) {
  if (fixture.timeline?.firstRunnableVerificationAt) {
    return ensureDateTime(fixture.timeline.firstRunnableVerificationAt, 'timeline.firstRunnableVerificationAt');
  }
  const candidates = asArray(fixture.verificationEvents)
    .filter((event) => event?.runnable === true && isPassStatus(event?.status) && event?.completedAt)
    .map((event) => ensureDateTime(event.completedAt, `verificationEvents.${event?.id ?? '(unknown)'}.completedAt`))
    .sort();
  return candidates[0] ?? null;
}

function buildMetric(definitionKey, valueFields) {
  const definition = METRIC_DEFINITIONS[definitionKey];
  return {
    ...valueFields,
    reviewerQuestion: definition.reviewerQuestion,
    calculationMethod: definition.calculationMethod,
    interpretation: definition.interpretation,
    limitation: definition.limitation,
  };
}

function buildDocument(options, fixture) {
  const limitations = [
    'offline fixture mode: no GitHub API or live external agent API was called.',
    'report-only adoption evidence: this document does not approve, merge, or replace human review.',
    'agent-vendor comparison is out of scope; metrics evaluate ae-framework workflow effectiveness only.',
  ];
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const requirementAcceptedAt = fixture.timeline?.requirementAcceptedAt
    ? ensureDateTime(fixture.timeline.requirementAcceptedAt, 'timeline.requirementAcceptedAt')
    : null;
  const firstRunnableVerificationAt = inferFirstRunnableVerificationAt(fixture);
  const timeToRunnable = minutesBetween(requirementAcceptedAt, firstRunnableVerificationAt);
  if (timeToRunnable === null) {
    limitations.push('time_to_first_runnable_verification_minutes is not_collected because requirement or runnable verification timestamps are unavailable.');
  }

  const sourceArtifacts = normalizeSourceArtifacts(fixture, options.projectRoot, limitations);
  const tasks = asArray(fixture.tasks);
  const evidenceItems = asArray(fixture.evidenceItems);
  const replayRuns = asArray(fixture.replayRuns);
  const manualInterventions = asArray(fixture.manualInterventions);
  const coverage = taskCoverage(tasks);
  const replay = replayPassRate(replayRuns);
  const evidence = evidenceReviewCompleteness(evidenceItems);

  const metrics = {
    time_to_first_runnable_verification_minutes: buildMetric('time_to_first_runnable_verification_minutes', {
      value: metricNumber(timeToRunnable),
      unit: 'minutes',
      from: requirementAcceptedAt,
      to: firstRunnableVerificationAt,
      sourceArtifactRefs: uniqueStrings(['requirement', 'verify-lite', 'loop-summary'].filter((id) => sourceArtifacts.some((artifact) => artifact.id === id))),
    }),
    spec_task_evidence_coverage: buildMetric('spec_task_evidence_coverage', {
      ...coverage,
      sourceArtifactRefs: uniqueStrings(['exec-plan', 'claim-evidence-manifest'].filter((id) => sourceArtifacts.some((artifact) => artifact.id === id))),
    }),
    deterministic_replay_pass_rate: buildMetric('deterministic_replay_pass_rate', {
      ...replay,
      sourceArtifactRefs: uniqueStrings(['loop-summary'].filter((id) => sourceArtifacts.some((artifact) => artifact.id === id))),
    }),
    manual_intervention_count: buildMetric('manual_intervention_count', {
      count: manualInterventions.length,
      sourceArtifactRefs: uniqueStrings(manualInterventions.flatMap((entry) => asArray(entry?.sourceArtifactRefs))),
      interventionIds: manualInterventions.map((entry) => String(entry.id ?? UNKNOWN)),
    }),
    evidence_review_completeness: buildMetric('evidence_review_completeness', {
      ...evidence,
      sourceArtifactRefs: uniqueStrings(evidenceItems.flatMap((entry) => asArray(entry?.sourceArtifactRefs))),
    }),
  };

  const subject = {
    id: fixture.subject?.id ?? 'req2run-offline-fixture',
    title: fixture.subject?.title ?? 'Offline req2run fixture',
    requirementRef: fixture.subject?.requirementRef ?? null,
    referenceFlow: fixture.subject?.referenceFlow ?? 'docs/getting-started/REFERENCE-FLOW.md',
    repository: fixture.subject?.repository ?? null,
  };

  const summary = `Report-only req2run metrics for ${subject.id}: first runnable verification ${metrics.time_to_first_runnable_verification_minutes.value} minutes, task evidence coverage ${coverage.numerator}/${coverage.denominator}, replay pass rate ${replay.numerator}/${replay.denominator}, manual interventions ${manualInterventions.length}, evidence review completeness ${evidence.numerator}/${evidence.denominator}.`;

  return {
    schemaVersion: 'req2run-metrics/v1',
    reportOnly: true,
    generatedAt,
    source: 'offline-fixture',
    subject,
    privacy: {
      rawTextIncluded: fixture.privacy?.rawTextIncluded === true,
      publicRawLogsAllowed: fixture.privacy?.publicRawLogsAllowed === true,
      publicationStatus: fixture.privacy?.publicationStatus ?? 'synthetic',
      redactionMode: fixture.privacy?.redactionMode ?? 'metadata-only',
    },
    collectionBoundaries: {
      workflowEvaluated: 'ae-framework reference flow',
      externalAgentApisCalled: false,
      agentVendorComparison: false,
      approvalAuthority: 'human maintainer; metrics are evidence only',
      reportOnlyReason: 'Req2run metrics are adoption-readiness signals and are not policy-gate block conditions.',
    },
    sourceArtifacts,
    metrics,
    limitations: uniqueStrings(limitations),
    summary,
  };
}

function escapeMd(value) {
  return String(value ?? '')
    .replaceAll('\\', '\\\\')
    .replaceAll('|', '\\|')
    .replaceAll('\n', '<br>');
}

function renderRatio(metric) {
  if (metric.ratio === null || metric.ratio === undefined) return 'not_collected';
  return `${metric.numerator}/${metric.denominator} (${Math.round(metric.ratio * 10000) / 100}%)`;
}

function renderMarkdown(document) {
  const metrics = document.metrics;
  return `# Req2run Metrics\n\n` +
    `Report-only requirement-to-runnable-evidence metrics for ${escapeMd(document.subject.id)}. Metrics evaluate ae-framework workflow effectiveness, not agent vendor quality.\n\n` +
    `- generatedAt: \`${document.generatedAt}\`\n` +
    `- source: \`${document.source}\`\n` +
    `- referenceFlow: \`${escapeMd(document.subject.referenceFlow)}\`\n` +
    `- approvalAuthority: ${escapeMd(document.collectionBoundaries.approvalAuthority)}\n\n` +
    `## Metrics\n\n` +
    `| Metric | Value | Question | Limitation |\n| --- | --- | --- | --- |\n` +
    `| time_to_first_runnable_verification_minutes | ${escapeMd(metrics.time_to_first_runnable_verification_minutes.value)} ${escapeMd(metrics.time_to_first_runnable_verification_minutes.unit)} | ${escapeMd(metrics.time_to_first_runnable_verification_minutes.reviewerQuestion)} | ${escapeMd(metrics.time_to_first_runnable_verification_minutes.limitation)} |\n` +
    `| spec_task_evidence_coverage | ${escapeMd(renderRatio(metrics.spec_task_evidence_coverage))} | ${escapeMd(metrics.spec_task_evidence_coverage.reviewerQuestion)} | ${escapeMd(metrics.spec_task_evidence_coverage.limitation)} |\n` +
    `| deterministic_replay_pass_rate | ${escapeMd(renderRatio(metrics.deterministic_replay_pass_rate))} | ${escapeMd(metrics.deterministic_replay_pass_rate.reviewerQuestion)} | ${escapeMd(metrics.deterministic_replay_pass_rate.limitation)} |\n` +
    `| manual_intervention_count | ${escapeMd(metrics.manual_intervention_count.count)} | ${escapeMd(metrics.manual_intervention_count.reviewerQuestion)} | ${escapeMd(metrics.manual_intervention_count.limitation)} |\n` +
    `| evidence_review_completeness | ${escapeMd(renderRatio(metrics.evidence_review_completeness))} | ${escapeMd(metrics.evidence_review_completeness.reviewerQuestion)} | ${escapeMd(metrics.evidence_review_completeness.limitation)} |\n\n` +
    `## Source artifacts\n\n` +
    `| ID | Kind | Path | Present | Required |\n| --- | --- | --- | --- | --- |\n` +
    `${document.sourceArtifacts.map((artifact) => `| ${escapeMd(artifact.id)} | ${escapeMd(artifact.kind)} | ${escapeMd(artifact.path ?? 'not_collected')} | ${artifact.present ? 'yes' : 'no'} | ${artifact.required ? 'yes' : 'no'} |`).join('\n')}\n\n` +
    `## Limitations\n\n` +
    `${document.limitations.map((entry) => `- ${entry}`).join('\n')}\n`;
}

function messageOf(error) {
  return error instanceof Error ? error.message : String(error);
}

function main() {
  const options = parseArgs();
  if (options.help) {
    usage();
    return;
  }
  const fixture = readJson(options.fixture);
  const document = buildDocument(options, fixture);
  const markdown = renderMarkdown(document);
  if (!options.noWrite) {
    const outputJson = ensureProjectContainedOutputPath(options.projectRoot, options.outputJson, '--output-json');
    const outputMd = ensureProjectContainedOutputPath(options.projectRoot, options.outputMd, '--output-md');
    writeJson(outputJson, document);
    writeText(outputMd, markdown);
  }
  process.stdout.write(`Req2run metrics written.\n- json: ${displayPath(options.outputJson, options.projectRoot)}\n- markdown: ${displayPath(options.outputMd, options.projectRoot)}\n- source: ${document.source}\n`);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  try {
    main();
  } catch (error) {
    process.stderr.write(`Req2run metrics collection failed: ${messageOf(error)}\n`);
    process.exit(1);
  }
}

export {
  METRIC_DEFINITIONS,
  buildDocument,
  parseArgs,
  renderMarkdown,
};
