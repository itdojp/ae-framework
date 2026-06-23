#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import { collectRequiredCheckClassifications } from '../ci/lib/check-classification.mjs';

const DEFAULT_OUTPUT_JSON = 'artifacts/metrics/agent-pr-assurance-metrics.json';
const DEFAULT_OUTPUT_MD = 'artifacts/metrics/agent-pr-assurance-metrics.md';
const DEFAULT_REQUIRED_CHECKS = ['gate', 'policy-gate', 'verify-lite'];
const NOT_COLLECTED = 'not_collected';
const UNKNOWN = 'unknown';

function usage() {
  process.stdout.write(`Usage: node scripts/metrics/collect-agent-pr-assurance-metrics.mjs [options]\n\nOptions:\n  --repo <owner/repo>                 GitHub repository for live mode.\n  --pr <number>                       Pull request number for live mode.\n  --fixture <path>                    Offline fixture containing pullRequest/statusCheckRollup and optional artifact paths.\n  --review-completeness-json <path>   Optional pr-review-completeness JSON.\n  --producer-summary <path>           Optional producer-normalization-summary/v1 input (repeatable).\n  --boundary-map-summary <path>       Optional boundary-map summary/report input (repeatable).\n  --assurance-profile <path>          Optional assurance-profile/v1 input (repeatable).\n  --claim-evidence-manifest <path>    Optional claim-evidence-manifest/v1 input (repeatable).\n  --policy-gate-summary <path>        Optional policy-gate-summary/v1 input (repeatable).\n  --required-check <name>             Required check name to summarize (repeatable; default: ${DEFAULT_REQUIRED_CHECKS.join(', ')}).\n  --gh-bin <path>                     gh executable for live mode (default: gh).\n  --review-ready-at <iso-date-time>   Optional review-ready timestamp for time_to_merge_minutes.\n  --generated-at <iso-date-time>      Deterministic generatedAt timestamp.\n  --output-json <path>                Output JSON path (default: ${DEFAULT_OUTPUT_JSON}).\n  --output-md <path>                  Output Markdown path (default: ${DEFAULT_OUTPUT_MD}).\n  --help                             Show this help.\n\nOffline fixture mode never calls GitHub. Live mode uses read-only \`gh pr view\`; missing optional inputs are emitted as ${NOT_COLLECTED}.\n`);
}

function readRequiredValue(argv, index, flag) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`${flag} requires a value`);
  }
  return next;
}

function parsePositiveInteger(value, flag) {
  const parsed = Number.parseInt(String(value), 10);
  if (!Number.isFinite(parsed) || parsed < 1) {
    throw new Error(`${flag} must be a positive integer: ${value}`);
  }
  return parsed;
}

function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    repo: null,
    pr: null,
    fixture: null,
    reviewCompletenessJson: null,
    producerSummaries: [],
    boundaryMapSummaries: [],
    assuranceProfiles: [],
    claimEvidenceManifests: [],
    policyGateSummaries: [],
    requiredChecks: [],
    ghBin: 'gh',
    reviewReadyAt: null,
    generatedAt: null,
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--repo') {
      options.repo = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--pr') {
      options.pr = parsePositiveInteger(readRequiredValue(argv, index, arg), arg);
      index += 1;
      continue;
    }
    if (arg === '--fixture') {
      options.fixture = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--review-completeness-json') {
      options.reviewCompletenessJson = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--producer-summary') {
      options.producerSummaries.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--boundary-map-summary') {
      options.boundaryMapSummaries.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--assurance-profile') {
      options.assuranceProfiles.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--claim-evidence-manifest') {
      options.claimEvidenceManifests.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--policy-gate-summary') {
      options.policyGateSummaries.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--required-check') {
      options.requiredChecks.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--gh-bin') {
      options.ghBin = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--review-ready-at') {
      options.reviewReadyAt = ensureDateTime(readRequiredValue(argv, index, arg), arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = ensureDateTime(readRequiredValue(argv, index, arg), arg);
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (options.requiredChecks.length === 0) {
    options.requiredChecks = [...DEFAULT_REQUIRED_CHECKS];
  }

  if (options.fixture && (options.repo || options.pr)) {
    throw new Error('--fixture is offline mode; do not combine it with --repo or --pr');
  }
  if (!options.fixture && (!options.repo || !options.pr)) {
    throw new Error('live mode requires --repo and --pr, or use --fixture for offline mode');
  }
  if (options.repo && !/^[^/\s]+\/[^/\s]+$/u.test(options.repo)) {
    throw new Error(`--repo must be owner/name: ${options.repo}`);
  }

  return options;
}

function ensureDateTime(value, flag = 'date-time') {
  const raw = String(value ?? '').trim();
  if (!Number.isFinite(Date.parse(raw))) {
    throw new Error(`${flag} must be an ISO date-time: ${raw || '(empty)'}`);
  }
  return new Date(raw).toISOString();
}

function ensureParent(filePath) {
  fs.mkdirSync(path.dirname(path.resolve(filePath)), { recursive: true });
}

function writeJson(filePath, payload) {
  ensureParent(filePath);
  fs.writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
}

function writeText(filePath, content) {
  ensureParent(filePath);
  fs.writeFileSync(filePath, content, 'utf8');
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(path.resolve(filePath), 'utf8'));
}

function readJsonIfPresent(filePath, label, limitations) {
  if (!filePath) return null;
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) {
    limitations.push(`${label} not collected: ${displayPath(filePath)} does not exist.`);
    return null;
  }
  try {
    return readJson(filePath);
  } catch (error) {
    limitations.push(`${label} not collected: ${displayPath(filePath)} is not valid JSON (${messageOf(error)}).`);
    return null;
  }
}

function displayPath(filePath) {
  if (!filePath) return 'not provided';
  const relative = path.relative(process.cwd(), path.resolve(filePath));
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) {
    return filePath.split(path.sep).join('/');
  }
  return relative.split(path.sep).join('/');
}

function messageOf(error) {
  return error instanceof Error ? error.message : String(error);
}

function ensureArray(value) {
  return Array.isArray(value) ? value : [];
}

function uniqueStrings(values) {
  return [...new Set(values.map((entry) => String(entry ?? '').trim()).filter(Boolean))];
}

function parseFixture(options, limitations) {
  if (!options.fixture) return null;
  const fixture = readJson(options.fixture);
  const artifactPaths = fixture.artifactPaths && typeof fixture.artifactPaths === 'object'
    ? fixture.artifactPaths
    : {};

  options.reviewCompletenessJson ??= artifactPaths.reviewCompletenessJson ?? null;
  options.producerSummaries.push(...ensureArray(artifactPaths.producerSummaries));
  options.boundaryMapSummaries.push(...ensureArray(artifactPaths.boundaryMapSummaries));
  options.assuranceProfiles.push(...ensureArray(artifactPaths.assuranceProfiles));
  options.claimEvidenceManifests.push(...ensureArray(artifactPaths.claimEvidenceManifests));
  options.policyGateSummaries.push(...ensureArray(artifactPaths.policyGateSummaries));
  if (Array.isArray(fixture.requiredChecks) && fixture.requiredChecks.length > 0) {
    options.requiredChecks = uniqueStrings(fixture.requiredChecks);
  }

  const pullRequest = fixture.pullRequest && typeof fixture.pullRequest === 'object'
    ? fixture.pullRequest
    : {};
  const statusCheckRollup = ensureArray(fixture.statusCheckRollup ?? pullRequest.statusCheckRollup);
  limitations.push('offline fixture mode: GitHub API was not called.');
  return {
    mode: 'fixture',
    pullRequest: {
      ...pullRequest,
      statusCheckRollup,
      repository: pullRequest.repository ?? fixture.repository ?? null,
      number: pullRequest.number ?? fixture.prNumber ?? null,
    },
    embeddedReviewCompleteness: fixture.reviewCompleteness ?? null,
  };
}

function collectLivePr(options) {
  const fields = [
    'number',
    'title',
    'url',
    'state',
    'createdAt',
    'mergedAt',
    'isDraft',
    'reviewDecision',
    'mergeStateStatus',
    'headRefOid',
    'statusCheckRollup',
  ].join(',');
  const result = spawnSync(options.ghBin, [
    'pr',
    'view',
    String(options.pr),
    '--repo',
    options.repo,
    '--json',
    fields,
  ], {
    cwd: process.cwd(),
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });

  if (result.status !== 0) {
    throw new Error(`gh pr view failed; live metrics require a readable PR and gh authentication. stderr: ${result.stderr.trim() || '(empty)'}`);
  }

  const pullRequest = JSON.parse(result.stdout);
  return {
    mode: 'live',
    pullRequest: {
      ...pullRequest,
      repository: options.repo,
      statusCheckRollup: ensureArray(pullRequest.statusCheckRollup),
    },
    embeddedReviewCompleteness: null,
  };
}

function metricValue(value, limitations, label) {
  if (value === null || value === undefined) {
    limitations.push(`${label} is ${NOT_COLLECTED}; provide the corresponding artifact or live field to collect it.`);
    return NOT_COLLECTED;
  }
  return value;
}

function readReviewCompleteness(options, collection, limitations) {
  const fromPath = readJsonIfPresent(options.reviewCompletenessJson, 'review completeness', limitations);
  const payload = fromPath ?? collection.embeddedReviewCompleteness;
  if (!payload) {
    return { total: null, unresolved: null, source: NOT_COLLECTED };
  }
  const counts = payload.counts && typeof payload.counts === 'object' ? payload.counts : payload;
  const total = firstInteger([
    counts.review_threads,
    counts.reviewThreads,
    counts.review_thread_count,
    counts.reviewThreadCount,
  ]);
  const unresolved = firstInteger([
    counts.unresolved_threads,
    counts.unresolvedThreads,
    counts.unresolved_thread_count,
    counts.unresolvedThreadCount,
  ]);
  return {
    total,
    unresolved,
    source: fromPath ? displayPath(options.reviewCompletenessJson) : 'offline fixture embedded reviewCompleteness',
  };
}

function firstInteger(candidates) {
  for (const candidate of candidates) {
    if (Number.isInteger(candidate) && candidate >= 0) return candidate;
  }
  return null;
}

function numeric(value) {
  return Number.isFinite(value) ? value : null;
}

function readArtifacts(paths, label, limitations) {
  return uniqueStrings(paths).map((filePath) => ({
    path: displayPath(filePath),
    payload: readJsonIfPresent(filePath, label, limitations),
  })).filter((entry) => entry.payload !== null);
}

function countScopeDrift(boundaryArtifacts, producerArtifacts) {
  if (boundaryArtifacts.length > 0) {
    return boundaryArtifacts.reduce((total, artifact) => {
      const payload = artifact.payload;
      const count = firstInteger([
        payload?.counts?.totalFindings,
        payload?.summary?.totalFindings,
        Array.isArray(payload?.reviewEvidence) ? payload.reviewEvidence.length : null,
        Array.isArray(payload?.findings) ? payload.findings.length : null,
      ]);
      return total + (count ?? 0);
    }, 0);
  }

  return producerArtifacts.reduce((total, artifact) => {
    const findings = ensureArray(artifact.payload?.controlPlaneRouting?.reportOnlyFindings);
    return total + findings.filter((finding) => /scope[-_ ]?drift|boundary/i.test(JSON.stringify(finding))).length;
  }, 0);
}

function countMissingEvidence(producerArtifacts, policyArtifacts, manifestArtifacts) {
  if (producerArtifacts.length > 0) {
    return producerArtifacts.reduce((total, artifact) => {
      const payload = artifact.payload;
      const summaryCount = firstInteger([payload?.summary?.missingEvidence]);
      if (summaryCount !== null) return total + summaryCount;
      return total + ensureArray(payload?.controlPlaneRouting?.missingEvidence).length;
    }, 0);
  }

  if (policyArtifacts.length > 0) {
    return policyArtifacts.reduce((total, artifact) => {
      const findings = ensureArray(artifact.payload?.evaluation?.assurance?.agentAssuranceFindings?.findings);
      return total + findings.filter((finding) => String(finding?.kind ?? '').includes('missing-evidence')).length;
    }, 0);
  }

  if (manifestArtifacts.length > 0) {
    return manifestArtifacts.reduce((total, artifact) => {
      const claims = ensureArray(artifact.payload?.claims);
      return total + claims.filter((claim) => ensureArray(claim?.evidenceRefs).length === 0 || ensureArray(claim?.missingEvidenceRefs).length > 0).length;
    }, 0);
  }

  return null;
}

function countSelectedHighRiskClaims(profileArtifacts, policyArtifacts) {
  if (profileArtifacts.length > 0) {
    return profileArtifacts.reduce((total, artifact) => {
      const claims = ensureArray(artifact.payload?.claims);
      return total + claims.filter((claim) => ['high', 'critical'].includes(String(claim?.criticality ?? '').toLowerCase())).length;
    }, 0);
  }

  if (policyArtifacts.length > 0) {
    return policyArtifacts.reduce((total, artifact) => {
      const claims = ensureArray(artifact.payload?.evaluation?.assurance?.claims);
      return total + claims.filter((claim) => String(claim?.result ?? '') !== 'pass').length;
    }, 0);
  }

  return null;
}


function collectRequiredChecks(statusCheckRollup, requiredNames, pullRequestHeadSha = null) {
  return collectRequiredCheckClassifications(statusCheckRollup, requiredNames, { pullRequestHeadSha });
}

function countCiReruns(requiredChecks) {
  if (requiredChecks.source === NOT_COLLECTED) return null;
  return requiredChecks.required.reduce((total, check) => total + Math.max(0, check.attempts - 1), 0);
}

function buildCiRerunClassificationCounts(requiredChecks) {
  if (requiredChecks.source === NOT_COLLECTED) return null;
  return {
    total: countCiReruns(requiredChecks) ?? 0,
    stale_cancelled: requiredChecks.summary.stale_cancelled_count,
    superseded: requiredChecks.summary.superseded_count,
    same_head_stale: requiredChecks.summary.same_head_stale_count,
    manual_rerun_required: requiredChecks.summary.manual_rerun_required_count,
  };
}

function minutesBetween(start, end) {
  if (!start || !end) return null;
  const startMs = Date.parse(start);
  const endMs = Date.parse(end);
  if (!Number.isFinite(startMs) || !Number.isFinite(endMs) || endMs < startMs) return null;
  return Math.round(((endMs - startMs) / 60000) * 100) / 100;
}

function reviewReadyAtForMetric(options, pullRequest) {
  return options.reviewReadyAt ?? pullRequest.reviewReadyAt ?? null;
}

function buildLowLevelMetrics({ missingEvidenceCount, requiredChecks, selectedHighRiskClaimCount, artifactSources }) {
  const missingEvidence = Number.isInteger(missingEvidenceCount) ? missingEvidenceCount : NOT_COLLECTED;
  const selectedClaims = Number.isInteger(selectedHighRiskClaimCount) ? selectedHighRiskClaimCount : 0;
  const countsCollected = requiredChecks.source !== NOT_COLLECTED;
  const currentFailures = countsCollected ? requiredChecks.summary.semantic_blocking_failure_count : NOT_COLLECTED;
  const staleFailures = countsCollected ? requiredChecks.summary.stale_or_superseded_failure_count : NOT_COLLECTED;
  const operationalNotes = countsCollected ? requiredChecks.summary.operational_note_count : NOT_COLLECTED;
  const artifactCount = artifactSources.length;

  return {
    claim_coverage: {
      numerator: 0,
      denominator: 0,
      ratio: 1,
      inputArtifacts: [],
    },
    unresolved_claim_count: {
      count: missingEvidence,
      inputArtifacts: artifactSources,
    },
    waiver_count: {
      active: 0,
      inputArtifacts: [],
    },
    waiver_expiry_risk: {
      expired: 0,
      expiringSoon: 0,
      windowDays: 14,
    },
    required_lane_compliance: {
      satisfied: 0,
      required: 0,
      ratio: null,
      missingLanes: [],
      notApplicable: true,
    },
    evidence_completeness: {
      present: artifactCount,
      required: artifactCount,
      ratio: 1,
      missingArtifacts: [],
    },
    agent_regression_signal: {
      currentFailures,
      staleOrSupersededFailures: staleFailures,
      operationalNotes,
      currentRequiredFailures: countsCollected ? requiredChecks.summary.current_required_failure_count : NOT_COLLECTED,
      policySemanticFailures: countsCollected ? requiredChecks.summary.policy_semantic_failure_count : NOT_COLLECTED,
      manualRerunRequired: countsCollected ? requiredChecks.summary.manual_rerun_required_count : NOT_COLLECTED,
      classificationSource: requiredChecks.source,
      regressed: Number.isInteger(currentFailures) ? currentFailures > 0 : false,
    },
    blocked_to_merge_eligible_mttr: {
      minutes: null,
      from: 'blocked',
      to: 'merge-eligible',
    },
    false_block_rate: {
      annotatedFalseBlocks: null,
      totalBlocks: selectedClaims > 0 ? 1 : 0,
      ratio: null,
      annotationRequired: true,
    },
  };
}

function buildDocument(options, collection) {
  const limitations = [];
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const reviewCompleteness = readReviewCompleteness(options, collection, limitations);
  const producerArtifacts = readArtifacts(options.producerSummaries, 'producer summary', limitations);
  const boundaryArtifacts = readArtifacts(options.boundaryMapSummaries, 'boundary map summary', limitations);
  const profileArtifacts = readArtifacts(options.assuranceProfiles, 'assurance profile', limitations);
  const manifestArtifacts = readArtifacts(options.claimEvidenceManifests, 'claim evidence manifest', limitations);
  const policyArtifacts = readArtifacts(options.policyGateSummaries, 'policy gate summary', limitations);
  const artifactSources = [
    ...producerArtifacts,
    ...boundaryArtifacts,
    ...profileArtifacts,
    ...manifestArtifacts,
    ...policyArtifacts,
  ].map((artifact) => artifact.path);

  const requiredChecks = collectRequiredChecks(
    collection.pullRequest.statusCheckRollup,
    options.requiredChecks,
    collection.pullRequest.headRefOid ?? null,
  );
  if (requiredChecks.source === NOT_COLLECTED) {
    limitations.push('required_checks are not_collected because no statusCheckRollup was available.');
  }

  const scopeDriftCount = boundaryArtifacts.length > 0 || producerArtifacts.length > 0
    ? countScopeDrift(boundaryArtifacts, producerArtifacts)
    : null;
  const missingEvidenceCount = countMissingEvidence(producerArtifacts, policyArtifacts, manifestArtifacts);
  const selectedHighRiskClaimCount = countSelectedHighRiskClaims(profileArtifacts, policyArtifacts);
  const ciRerunCount = countCiReruns(requiredChecks);
  const ciRerunClassificationCounts = buildCiRerunClassificationCounts(requiredChecks);
  const reviewReadyAt = reviewReadyAtForMetric(options, collection.pullRequest);
  const timeToMerge = minutesBetween(reviewReadyAt, collection.pullRequest.mergedAt);
  if (timeToMerge === null) {
    limitations.push('time_to_merge_minutes is not_collected because review-ready or merge timestamps are unavailable.');
  }

  const productMetrics = {
    review_threads_total: metricValue(reviewCompleteness.total, limitations, 'review_threads_total'),
    review_threads_unresolved_final: metricValue(reviewCompleteness.unresolved, limitations, 'review_threads_unresolved_final'),
    required_checks: requiredChecks,
    scope_drift_finding_count: metricValue(scopeDriftCount, limitations, 'scope_drift_finding_count'),
    missing_evidence_finding_count: metricValue(missingEvidenceCount, limitations, 'missing_evidence_finding_count'),
    selected_high_risk_claim_count: metricValue(selectedHighRiskClaimCount, limitations, 'selected_high_risk_claim_count'),
    ci_rerun_count: metricValue(ciRerunCount, limitations, 'ci_rerun_count'),
    ci_rerun_classification_counts: metricValue(ciRerunClassificationCounts, limitations, 'ci_rerun_classification_counts'),
    time_to_merge_minutes: metricValue(timeToMerge, limitations, 'time_to_merge_minutes'),
    policy_gate_false_positive_count: NOT_COLLECTED,
    policy_gate_false_negative_count: NOT_COLLECTED,
  };

  limitations.push('policy_gate_false_positive_count and policy_gate_false_negative_count require manual annotation; they are not inferred from reruns.');

  const lowLevelMetrics = buildLowLevelMetrics({
    missingEvidenceCount,
    requiredChecks,
    selectedHighRiskClaimCount,
    artifactSources,
  });

  const summary = buildSummary(productMetrics, collection.pullRequest);
  return {
    schemaVersion: '2.1.0',
    tokens: {
      prompt: null,
      completion: null,
      tool: null,
      total: null,
    },
    costUsd: null,
    memoryHitRatio: null,
    turns: {
      count: 0,
      avgLen: 0,
    },
    latencyMs: 0,
    agentPrAssurance: {
      reportOnly: true,
      generatedAt,
      source: collection.mode === 'fixture' ? 'offline-fixture' : 'gh-pr-view',
      pullRequest: {
        repository: collection.pullRequest.repository ?? options.repo ?? UNKNOWN,
        number: collection.pullRequest.number ?? options.pr ?? UNKNOWN,
        title: collection.pullRequest.title ?? UNKNOWN,
        url: collection.pullRequest.url ?? null,
        state: collection.pullRequest.state ?? UNKNOWN,
        createdAt: collection.pullRequest.createdAt ?? null,
        reviewReadyAt,
        mergedAt: collection.pullRequest.mergedAt ?? null,
        headRefOid: collection.pullRequest.headRefOid ?? null,
        mergeStateStatus: collection.pullRequest.mergeStateStatus ?? null,
      },
      collectionSources: {
        reviewCompleteness: reviewCompleteness.source,
        producerSummaries: producerArtifacts.map((artifact) => artifact.path),
        boundaryMapSummaries: boundaryArtifacts.map((artifact) => artifact.path),
        assuranceProfiles: profileArtifacts.map((artifact) => artifact.path),
        claimEvidenceManifests: manifestArtifacts.map((artifact) => artifact.path),
        policyGateSummaries: policyArtifacts.map((artifact) => artifact.path),
      },
      metrics: lowLevelMetrics,
      productMetrics,
      limitations: uniqueStrings(limitations),
      summary,
    },
  };
}

function renderValue(value) {
  if (value && typeof value === 'object') return `\`${JSON.stringify(value)}\``;
  return String(value);
}

function buildSummary(productMetrics, pullRequest) {
  const repo = pullRequest.repository ?? UNKNOWN;
  const number = pullRequest.number ?? UNKNOWN;
  return `Report-only agent PR assurance metrics for ${repo}#${number}: review threads ${renderValue(productMetrics.review_threads_total)}, unresolved final ${renderValue(productMetrics.review_threads_unresolved_final)}, required check semantic failures ${productMetrics.required_checks.summary.semantic_blocking_failure_count}, operational notes ${productMetrics.required_checks.summary.operational_note_count}.`;
}

function requiredCheckRow(entry) {
  return `| ${escapeMd(entry.name)} | ${escapeMd(entry.classification)} | ${escapeMd(entry.review_disposition)} | ${entry.attempts} | ${entry.stale_cancelled_count} | ${entry.superseded_count} | ${entry.same_head_stale_count} | ${escapeMd(entry.latest?.conclusion ?? NOT_COLLECTED)} |`;
}

function renderRequiredCheckTable(entries) {
  const rows = entries.map(requiredCheckRow);
  return `| Check | Classification | Review disposition | Attempts | Stale cancelled | Superseded | Same-head stale | Latest conclusion |\n| --- | --- | --- | ---: | ---: | ---: | ---: | --- |\n${rows.length > 0 ? rows.join('\n') : '| none | none | none | 0 | 0 | 0 | 0 | none |'}`;
}

function renderRequiredCheckDispositionSections(requiredChecks) {
  const groups = [
    ['Blocking required checks', requiredChecks.filter((entry) => entry.review_disposition === 'blocking')],
    ['Operational notes', requiredChecks.filter((entry) => entry.review_disposition === 'operational_note')],
    ['Pending checks', requiredChecks.filter((entry) => entry.review_disposition === 'pending')],
    ['Not collected checks', requiredChecks.filter((entry) => entry.review_disposition === NOT_COLLECTED)],
    ['Unknown checks', requiredChecks.filter((entry) => entry.review_disposition === UNKNOWN)],
    ['Non-blocking checks', requiredChecks.filter((entry) => entry.review_disposition === 'non_blocking')],
  ];
  return groups
    .filter(([, entries]) => entries.length > 0)
    .map(([title, entries]) => `### ${title}\n\n${renderRequiredCheckTable(entries)}`)
    .join('\n\n');
}

function renderMarkdown(document) {
  const assurance = document.agentPrAssurance;
  const metrics = assurance.productMetrics;
  const pr = assurance.pullRequest;
  return `# Agent PR Assurance Metrics\n\n` +
    `Report-only metrics for ${escapeMd(pr.repository)}#${escapeMd(pr.number)}. Producer output and metrics are review evidence, not approval.\n\n` +
    `- generatedAt: \`${assurance.generatedAt}\`\n` +
    `- source: \`${assurance.source}\`\n` +
    `- PR state: \`${escapeMd(pr.state)}\`\n` +
    `- mergeStateStatus: \`${escapeMd(pr.mergeStateStatus ?? NOT_COLLECTED)}\`\n\n` +
    `## Product metrics\n\n` +
    `| Metric | Value |\n| --- | --- |\n` +
    `| review_threads_total | ${escapeMd(metrics.review_threads_total)} |\n` +
    `| review_threads_unresolved_final | ${escapeMd(metrics.review_threads_unresolved_final)} |\n` +
    `| scope_drift_finding_count | ${escapeMd(metrics.scope_drift_finding_count)} |\n` +
    `| missing_evidence_finding_count | ${escapeMd(metrics.missing_evidence_finding_count)} |\n` +
    `| selected_high_risk_claim_count | ${escapeMd(metrics.selected_high_risk_claim_count)} |\n` +
    `| ci_rerun_count | ${escapeMd(metrics.ci_rerun_count)} |\n` +
    `| ci_rerun_classification_counts | ${escapeMd(renderValue(metrics.ci_rerun_classification_counts))} |\n` +
    `| time_to_merge_minutes | ${escapeMd(metrics.time_to_merge_minutes)} |\n` +
    `| policy_gate_false_positive_count | ${escapeMd(metrics.policy_gate_false_positive_count)} |\n` +
    `| policy_gate_false_negative_count | ${escapeMd(metrics.policy_gate_false_negative_count)} |\n\n` +
    `## Required checks\n\n` +
    `Blocking rows are semantic failures. Operational notes are stale, cancelled, superseded, or rerun-needed states and are not policy false-positive annotations.\n\n` +
    `${renderRequiredCheckDispositionSections(metrics.required_checks.required)}\n\n` +
    `## Limitations\n\n` +
    `${assurance.limitations.map((entry) => `- ${entry}`).join('\n')}\n`;
}

function escapeMd(value) {
  return String(value ?? '')
    .replaceAll('\\', '\\\\')
    .replaceAll('|', '\\|')
    .replaceAll('\n', '<br>');
}

function main() {
  const options = parseArgs();
  if (options.help) {
    usage();
    return;
  }
  const bootstrapLimitations = [];
  const fixtureCollection = parseFixture(options, bootstrapLimitations);
  const collection = fixtureCollection ?? collectLivePr(options);
  const document = buildDocument(options, collection);
  document.agentPrAssurance.limitations = uniqueStrings([
    ...bootstrapLimitations,
    ...document.agentPrAssurance.limitations,
  ]);
  writeJson(options.outputJson, document);
  writeText(options.outputMd, renderMarkdown(document));
  process.stdout.write(`Agent PR assurance metrics written.\n- json: ${displayPath(options.outputJson)}\n- markdown: ${displayPath(options.outputMd)}\n- source: ${document.agentPrAssurance.source}\n`);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  try {
    main();
  } catch (error) {
    process.stderr.write(`Agent PR assurance metrics collection failed: ${messageOf(error)}\n`);
    process.exit(1);
  }
}

export {
  collectRequiredChecks,
  buildDocument,
  parseArgs,
};
