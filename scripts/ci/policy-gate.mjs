#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import micromatch from 'micromatch';
import {
  renderMarkdown as renderPlanArtifactValidationMarkdown,
  validatePlanArtifactFile,
} from '../plan-artifact/validate.mjs';
import { execGhJson } from './lib/gh-exec.mjs';
import { normalizeLabelNames } from './lib/automation-guards.mjs';
import {
  DEFAULT_POLICY_PATH,
  collectRequiredLabels,
  getGateCheckPatternsForLabel,
  getMinHumanApprovals,
  getOptionalGateLabels,
  isPlanArtifactRequired,
  isPolicyLabelRequirementEnabled,
  getRequiredChecks,
  getRiskLabels,
  inferRiskLevel,
  isPendingGateFailureEnabled,
  loadRiskPolicy,
} from './lib/risk-policy.mjs';

const OUTPUT_JSON_PATH = 'artifacts/ci/policy-gate-summary.json';
const OUTPUT_MD_PATH = 'artifacts/ci/policy-gate-summary.md';
const SUMMARY_SCHEMA_VERSION = 'policy-gate-summary/v1';
const SUMMARY_CONTRACT_ID = 'policy-gate-summary.v1';
const POLICY_INPUT_PATH = 'artifacts/ci/policy-input-v1.json';
const POLICY_DECISION_PATH = 'artifacts/ci/policy-decision-js-v1.json';
const CLAIM_EVIDENCE_MANIFEST_PATH = 'artifacts/assurance/claim-evidence-manifest.json';
const CLAIM_LEVEL_SUMMARY_PATH = 'artifacts/assurance/claim-level-summary.json';
const PLAN_ARTIFACT_PATH = 'artifacts/plan/plan-artifact.json';
const PLAN_ARTIFACT_SCHEMA_PATH = 'schema/plan-artifact.schema.json';
const PLAN_ARTIFACT_VALIDATION_JSON_PATH = 'artifacts/plan/plan-artifact-validation.json';
const PLAN_ARTIFACT_VALIDATION_MD_PATH = 'artifacts/plan/plan-artifact-validation.md';
const VALID_REVIEW_TOPOLOGIES = new Set(['team', 'solo']);
const VALID_ASSURANCE_MODES = new Set(['report-only', 'strict', 'enforcement', 'enforced']);
const EXPIRING_SOON_DAYS = 14;

function parseArgs(argv) {
  const options = {
    prNumber: null,
    policyPath: DEFAULT_POLICY_PATH,
  };
  for (let index = 2; index < argv.length; index += 1) {
    const value = argv[index];
    if ((value === '--pr' || value === '--pr-number') && argv[index + 1]) {
      options.prNumber = Number(argv[++index]);
      continue;
    }
    if (value.startsWith('--pr=')) {
      options.prNumber = Number(value.slice('--pr='.length));
      continue;
    }
    if ((value === '--policy' || value === '--policy-path') && argv[index + 1]) {
      options.policyPath = argv[++index];
      continue;
    }
    if (value.startsWith('--policy=')) {
      options.policyPath = value.slice('--policy='.length);
    }
  }
  return options;
}

function toPositiveInt(value) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) return null;
  const truncated = Math.trunc(parsed);
  if (truncated <= 0) return null;
  return truncated;
}

function readPrNumberFromEventPath(eventPath) {
  if (!eventPath || !fs.existsSync(eventPath)) return null;
  try {
    const payload = JSON.parse(fs.readFileSync(eventPath, 'utf8'));
    return toPositiveInt(
      payload?.pull_request?.number
      || payload?.workflow_run?.pull_requests?.[0]?.number
      || payload?.issue?.number
      || payload?.number
      || payload?.inputs?.pr_number,
    );
  } catch {
    return null;
  }
}

function resolvePrNumber(explicit) {
  const fromArgs = toPositiveInt(explicit);
  if (fromArgs) return fromArgs;
  const fromEnv = toPositiveInt(process.env.PR_NUMBER);
  if (fromEnv) return fromEnv;
  return readPrNumberFromEventPath(process.env.GITHUB_EVENT_PATH);
}

function fetchPullRequest(repo, prNumber) {
  return execGhJson(['api', `repos/${repo}/pulls/${prNumber}`]);
}

function fetchChangedFiles(repo, prNumber) {
  const files = [];
  let page = 1;
  while (true) {
    const items = execGhJson([
      'api',
      `repos/${repo}/pulls/${prNumber}/files?per_page=100&page=${page}`,
    ]);
    if (!Array.isArray(items) || items.length === 0) break;
    for (const item of items) {
      const filename = String(item?.filename || '').trim();
      if (filename) files.push(filename);
    }
    if (items.length < 100) break;
    page += 1;
  }
  return files.sort();
}

function fetchReviews(repo, prNumber) {
  const reviews = [];
  let page = 1;
  while (true) {
    const items = execGhJson([
      'api',
      `repos/${repo}/pulls/${prNumber}/reviews?per_page=100&page=${page}`,
    ]);
    if (!Array.isArray(items) || items.length === 0) break;
    reviews.push(...items);
    if (items.length < 100) break;
    page += 1;
  }
  return reviews;
}

function fetchStatusRollup(repo, prNumber) {
  const view = execGhJson([
    'pr',
    'view',
    String(prNumber),
    '--repo',
    repo,
    '--json',
    'statusCheckRollup',
  ]);
  return Array.isArray(view?.statusCheckRollup) ? view.statusCheckRollup : [];
}

function isHumanReviewer(review) {
  const login = String(review?.user?.login || '').trim().toLowerCase();
  const type = String(review?.user?.type || '').trim().toLowerCase();
  if (!login) return false;
  if (type === 'bot') return false;
  if (login.endsWith('[bot]')) return false;
  return true;
}

function countHumanApprovals(reviews) {
  const latestByUser = new Map();
  const sorted = Array.isArray(reviews)
    ? [...reviews].sort((a, b) => {
      const aTime = Date.parse(String(a?.submitted_at || a?.submittedAt || ''));
      const bTime = Date.parse(String(b?.submitted_at || b?.submittedAt || ''));
      if (!Number.isNaN(aTime) && !Number.isNaN(bTime) && aTime !== bTime) {
        return aTime - bTime;
      }
      return Number(a?.id || 0) - Number(b?.id || 0);
    })
    : [];
  for (const review of sorted) {
    if (!isHumanReviewer(review)) continue;
    const login = String(review?.user?.login || '').trim().toLowerCase();
    const state = String(review?.state || '').trim().toUpperCase();
    latestByUser.set(login, state);
  }
  let approvals = 0;
  for (const state of latestByUser.values()) {
    if (state === 'APPROVED') approvals += 1;
  }
  return approvals;
}

function normalizeReviewTopology(value) {
  const raw = String(value ?? '').trim().toLowerCase();
  if (!raw) {
    return { value: 'team', warning: null };
  }
  if (VALID_REVIEW_TOPOLOGIES.has(raw)) {
    return { value: raw, warning: null };
  }
  return {
    value: 'team',
    warning: `invalid review topology: ${raw} (fallback to team)`,
  };
}

function parseOptionalNonNegativeInt(value, keyName) {
  const raw = String(value ?? '').trim();
  if (!raw) {
    return { value: null, warning: null };
  }
  if (!/^-?[0-9]+$/.test(raw)) {
    return {
      value: null,
      warning: `${keyName}=${raw} is invalid (expected non-negative integer)`,
    };
  }
  const parsed = Number.parseInt(raw, 10);
  if (!Number.isFinite(parsed) || parsed < 0) {
    return {
      value: null,
      warning: `${keyName}=${raw} is invalid (expected non-negative integer)`,
    };
  }
  return { value: parsed, warning: null };
}

function resolveApprovalGateConfig(policy, options = {}) {
  const topologyState = normalizeReviewTopology(options.reviewTopology);
  const overrideState = parseOptionalNonNegativeInt(
    options.approvalOverride,
    'AE_POLICY_MIN_HUMAN_APPROVALS',
  );

  const warnings = [];
  if (topologyState.warning) warnings.push(topologyState.warning);
  if (overrideState.warning) warnings.push(overrideState.warning);

  const policyMinApprovals = getMinHumanApprovals(policy);
  const topologyMinApprovals = topologyState.value === 'solo' ? 0 : policyMinApprovals;
  const hasOverride = overrideState.value !== null;

  return {
    reviewTopology: topologyState.value,
    policyMinApprovals,
    topologyMinApprovals,
    effectiveMinApprovals: hasOverride ? overrideState.value : topologyMinApprovals,
    minApprovalsSource: hasOverride
      ? 'override'
      : (topologyState.value === 'solo' ? 'topology' : 'policy'),
    warnings,
  };
}

function toCheckEntries(statusRollup) {
  const entries = [];
  for (const item of statusRollup || []) {
    if (!item || typeof item !== 'object') continue;
    if (item.__typename === 'CheckRun') {
      const name = String(item.name || '').trim();
      if (!name) continue;
      const status = String(item.status || '').trim().toUpperCase();
      const conclusion = String(item.conclusion || '').trim().toUpperCase();
      const workflowName = String(item.workflowName || '').trim();
      const startedAt = String(item.startedAt || '').trim();
      const completedAt = String(item.completedAt || '').trim();
      let state = 'neutral';
      if (status !== 'COMPLETED') {
        state = 'pending';
      } else if (conclusion === 'SUCCESS' || conclusion === 'SKIPPED' || conclusion === 'NEUTRAL') {
        state = 'success';
      } else if (!conclusion) {
        state = 'pending';
      } else {
        state = 'failure';
      }
      entries.push({
        name,
        state,
        type: 'check-run',
        status,
        conclusion,
        workflowName,
        startedAt,
        completedAt,
      });
      continue;
    }
    if (item.__typename === 'StatusContext') {
      const name = String(item.context || '').trim();
      if (!name) continue;
      const stateRaw = String(item.state || '').trim().toUpperCase();
      let state = 'neutral';
      if (stateRaw === 'SUCCESS') state = 'success';
      else if (stateRaw === 'PENDING') state = 'pending';
      else if (stateRaw === 'FAILURE' || stateRaw === 'ERROR') state = 'failure';
      entries.push({
        name,
        state,
        type: 'status-context',
        status: stateRaw,
        conclusion: stateRaw,
        workflowName: '',
        startedAt: '',
        completedAt: '',
      });
    }
  }
  return entries;
}

function getCheckEntryTimestamp(entry) {
  const completedAt = Date.parse(String(entry?.completedAt || '').trim());
  if (Number.isFinite(completedAt)) return completedAt;
  const startedAt = Date.parse(String(entry?.startedAt || '').trim());
  if (Number.isFinite(startedAt)) return startedAt;
  return null;
}

function shouldReplaceCollapsedEntry(previous, current, previousIndex, currentIndex) {
  const previousTs = getCheckEntryTimestamp(previous);
  const currentTs = getCheckEntryTimestamp(current);
  if (previousTs !== null && currentTs !== null && previousTs !== currentTs) {
    return currentTs > previousTs;
  }
  return currentIndex >= previousIndex;
}

function collapseCheckEntriesByName(entries) {
  const deduped = new Map();
  for (const [index, entry] of (entries || []).entries()) {
    if (!entry || typeof entry !== 'object') continue;
    const name = String(entry.name || '').trim();
    const type = String(entry.type || '').trim();
    if (!name || !type) continue;
    const key = `${type}::${name}`;
    const previous = deduped.get(key);
    if (!previous || shouldReplaceCollapsedEntry(previous.entry, entry, previous.index, index)) {
      deduped.set(key, { entry, index });
    }
  }
  return Array.from(deduped.values(), (value) => value.entry);
}

function isGlobPattern(pattern) {
  return /[*?[\]{}()!+@]/.test(pattern);
}

function matchesPattern(checkName, pattern) {
  const target = String(checkName || '').trim();
  const value = String(pattern || '').trim();
  if (!target || !value) return false;
  if (isGlobPattern(value)) {
    return micromatch.isMatch(target, value, { dot: true });
  }
  return target === value;
}

function evaluateCheckRequirement(entries, patterns) {
  const patternList = Array.isArray(patterns) ? patterns.map((value) => String(value || '').trim()).filter(Boolean) : [];
  if (patternList.length === 0) {
    return {
      status: 'missing',
      matches: [],
      reason: 'no-check-pattern',
    };
  }

  const matches = entries.filter((entry) => patternList.some((pattern) => matchesPattern(entry.name, pattern)));
  if (matches.length === 0) {
    return {
      status: 'missing',
      matches: [],
      reason: 'not-found',
    };
  }
  if (matches.some((entry) => entry.state === 'failure')) {
    return {
      status: 'failure',
      matches,
      reason: 'failed',
    };
  }
  if (matches.some((entry) => entry.state === 'pending')) {
    return {
      status: 'pending',
      matches,
      reason: 'pending',
    };
  }
  return {
    status: 'success',
    matches,
    reason: 'success',
  };
}

function inspectPlanArtifact(policyPath = DEFAULT_POLICY_PATH) {
  const absoluteInputPath = path.resolve(PLAN_ARTIFACT_PATH);
  const absoluteSchemaPath = path.resolve(PLAN_ARTIFACT_SCHEMA_PATH);
  const baseState = {
    path: absoluteInputPath,
    schemaPath: absoluteSchemaPath,
    present: false,
    result: 'missing',
    validationErrors: [],
    warnings: [],
    riskSelected: null,
    source: null,
  };
  if (!fs.existsSync(absoluteInputPath)) {
    return baseState;
  }

  try {
    const { report, payload } = validatePlanArtifactFile({
      inputPath: PLAN_ARTIFACT_PATH,
      schemaPath: PLAN_ARTIFACT_SCHEMA_PATH,
      policyPath,
      outputJsonPath: PLAN_ARTIFACT_VALIDATION_JSON_PATH,
      outputMarkdownPath: PLAN_ARTIFACT_VALIDATION_MD_PATH,
    });
    const markdown = renderPlanArtifactValidationMarkdown(report);
    ensureDirectory(PLAN_ARTIFACT_VALIDATION_JSON_PATH);
    fs.writeFileSync(PLAN_ARTIFACT_VALIDATION_JSON_PATH, `${JSON.stringify(report, null, 2)}\n`);
    ensureDirectory(PLAN_ARTIFACT_VALIDATION_MD_PATH);
    fs.writeFileSync(PLAN_ARTIFACT_VALIDATION_MD_PATH, markdown);

    const source = payload?.source && typeof payload.source === 'object'
      ? {
        repository: String(payload.source.repository || '').trim() || null,
        prNumber: Number.isFinite(Number(payload.source.prNumber))
          ? Math.trunc(Number(payload.source.prNumber))
          : null,
        baseRef: String(payload.source.baseRef || '').trim() || null,
        headRef: String(payload.source.headRef || '').trim() || null,
      }
      : null;

    return {
      ...baseState,
      present: true,
      result: report.result,
      validationErrors: Array.isArray(report.errors) ? report.errors : [],
      warnings: Array.isArray(report.warnings) ? report.warnings : [],
      riskSelected: String(payload?.risk?.selected || '').trim() || null,
      source,
    };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    const report = {
      schemaVersion: 'plan-artifact-validation/v1',
      generatedAt: new Date().toISOString(),
      result: 'fail',
      inputPath: absoluteInputPath,
      schemaPath: absoluteSchemaPath,
      errors: [message],
      warnings: [],
    };
    const markdown = renderPlanArtifactValidationMarkdown(report);
    ensureDirectory(PLAN_ARTIFACT_VALIDATION_JSON_PATH);
    fs.writeFileSync(PLAN_ARTIFACT_VALIDATION_JSON_PATH, `${JSON.stringify(report, null, 2)}\n`);
    ensureDirectory(PLAN_ARTIFACT_VALIDATION_MD_PATH);
    fs.writeFileSync(PLAN_ARTIFACT_VALIDATION_MD_PATH, markdown);
    return {
      ...baseState,
      present: true,
      result: 'fail',
      validationErrors: [message],
    };
  }
}

function evaluatePlanArtifactRequirement(policy, isHighRisk, planArtifact) {
  const riskLabels = getRiskLabels(policy);
  const required = isHighRisk && isPlanArtifactRequired(policy);
  const normalized = planArtifact && typeof planArtifact === 'object'
    ? {
      path: String(planArtifact.path || path.resolve(PLAN_ARTIFACT_PATH)),
      schemaPath: String(planArtifact.schemaPath || path.resolve(PLAN_ARTIFACT_SCHEMA_PATH)),
      present: Boolean(planArtifact.present),
      result: String(planArtifact.result || (planArtifact.present ? 'fail' : 'missing')),
      validationErrors: Array.isArray(planArtifact.validationErrors) ? planArtifact.validationErrors : [],
      warnings: Array.isArray(planArtifact.warnings) ? planArtifact.warnings : [],
      riskSelected: String(planArtifact.riskSelected || '').trim() || null,
      source: planArtifact.source && typeof planArtifact.source === 'object' ? planArtifact.source : null,
    }
    : {
      path: path.resolve(PLAN_ARTIFACT_PATH),
      schemaPath: path.resolve(PLAN_ARTIFACT_SCHEMA_PATH),
      present: false,
      result: 'missing',
      validationErrors: [],
      warnings: [],
      riskSelected: null,
      source: null,
    };

  const errors = [];
  const warnings = [];

  if (required && !normalized.present) {
    errors.push(`missing required plan artifact: ${PLAN_ARTIFACT_PATH}`);
  }
  if (normalized.present) {
    if (normalized.result === 'fail') {
      if (required) {
        errors.push(`plan artifact validation failed: ${normalized.validationErrors.join('; ') || 'unknown error'}`);
      } else {
        warnings.push(`plan artifact validation failed (optional for low-risk PR): ${normalized.validationErrors.join('; ') || 'unknown error'}`);
      }
    }
    if (required && normalized.riskSelected && normalized.riskSelected !== riskLabels.high) {
      errors.push(`plan artifact risk.selected must be ${riskLabels.high}, found ${normalized.riskSelected}`);
    }
    for (const warning of normalized.warnings) {
      warnings.push(`plan artifact: ${warning}`);
    }
  }

  return {
    ...normalized,
    required,
    errors,
    warnings,
  };
}

function normalizeAssuranceMode(value) {
  const raw = String(value ?? '').trim().toLowerCase();
  if (!raw) {
    return { value: 'report-only', warning: null };
  }
  if (raw === 'enforcement' || raw === 'enforced') {
    return { value: 'strict', warning: null };
  }
  if (VALID_ASSURANCE_MODES.has(raw)) {
    return { value: raw, warning: null };
  }
  return {
    value: 'report-only',
    warning: `invalid assurance mode: ${raw} (fallback to report-only)`,
  };
}

function resolveAssuranceMode(value) {
  const modeState = normalizeAssuranceMode(value);
  return modeState;
}

function normalizeIdRefs(value) {
  if (!Array.isArray(value)) return [];
  return normalizeUniqueStringArray(value.map((entry) => (entry && typeof entry === 'object' ? entry.id : entry)));
}

function normalizeDateOnly(value) {
  const raw = String(value ?? '').trim();
  return /^\d{4}-\d{2}-\d{2}$/.test(raw) ? raw : null;
}

function compareDateOnly(left, right) {
  if (!left || !right) return 0;
  return left.localeCompare(right);
}

function toDateOnly(value) {
  const parsed = new Date(value);
  if (Number.isNaN(parsed.getTime())) {
    return new Date().toISOString().slice(0, 10);
  }
  return parsed.toISOString().slice(0, 10);
}

function addDaysToDateOnly(value, days) {
  const parsed = Date.parse(`${value}T00:00:00.000Z`);
  if (!Number.isFinite(parsed)) return value;
  return new Date(parsed + days * 24 * 60 * 60 * 1000).toISOString().slice(0, 10);
}

function normalizeWaiverStatus(waiver, nowDate) {
  const rawStatus = String(waiver?.status ?? 'unknown').trim().toLowerCase() || 'unknown';
  if (rawStatus === 'orphan') return 'orphan';
  const expires = normalizeDateOnly(waiver?.expires);
  if (rawStatus === 'expired' || (expires && compareDateOnly(expires, nowDate) < 0)) {
    return 'expired';
  }
  if (rawStatus === 'active' && expires && compareDateOnly(expires, addDaysToDateOnly(nowDate, EXPIRING_SOON_DAYS)) <= 0) {
    return 'expiringSoon';
  }
  if (rawStatus === 'active') return 'active';
  return 'unknown';
}

function normalizeAssuranceResult(value, fallback = 'report-only') {
  const raw = String(value ?? '').trim().toLowerCase();
  return ['pass', 'waived', 'report-only', 'block'].includes(raw) ? raw : fallback;
}


function normalizeManifestSecuritySummary(value) {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return null;
  const integerField = (field) => {
    const number = Number(value?.[field] ?? 0);
    if (!Number.isFinite(number) || number <= 0) return 0;
    return Math.trunc(number);
  };
  return {
    claims: integerField('claims'),
    findings: integerField('findings'),
    reviews: integerField('reviews'),
    candidate: integerField('candidate'),
    needsHumanReview: integerField('needsHumanReview'),
    confirmed: integerField('confirmed'),
    rejected: integerField('rejected'),
    waived: integerField('waived'),
    outOfScope: integerField('outOfScope'),
    highOrCriticalOpen: integerField('highOrCriticalOpen'),
    assumptionValidationRequired: integerField('assumptionValidationRequired'),
    assumptionResidualRisk: integerField('assumptionResidualRisk'),
  };
}

function normalizeClaimWaivers(claim, nowDate) {
  return (Array.isArray(claim?.waiverRefs) ? claim.waiverRefs : [])
    .filter((waiver) => waiver && typeof waiver === 'object')
    .map((waiver) => ({
      id: String(waiver.id || '').trim(),
      sourceArtifactId: String(waiver.sourceArtifactId || waiver.temporaryOverridePath || '').trim(),
      status: normalizeWaiverStatus(waiver, nowDate),
      owner: String(waiver.owner || '').trim() || null,
      expires: normalizeDateOnly(waiver.expires),
      reason: String(waiver.reason || '').trim() || null,
    }))
    .filter((waiver) => waiver.id);
}

function waiverValidationErrors(waiver, claim) {
  const claimId = String(claim?.claimId || '').trim() || '(unknown claim)';
  const errors = [];
  if (waiver.status === 'expired') {
    errors.push(`assurance waiver ${waiver.id} for ${claimId} is expired; next action: renew or remove the waiver and provide required evidence`);
  } else if (waiver.status === 'orphan') {
    errors.push(`assurance waiver ${waiver.id} for ${claimId} is orphaned; next action: link it to an active claim and evidence record`);
  } else if (waiver.status === 'unknown') {
    errors.push(`assurance waiver ${waiver.id} for ${claimId} has unknown status; next action: set status to active or expired`);
  }
  if (!waiver.owner) {
    errors.push(`assurance waiver ${waiver.id} for ${claimId} is missing owner; next action: add waiver owner`);
  }
  if (!waiver.reason) {
    errors.push(`assurance waiver ${waiver.id} for ${claimId} is missing reason; next action: add waiver rationale`);
  }
  if (!waiver.expires) {
    errors.push(`assurance waiver ${waiver.id} for ${claimId} is missing expiry; next action: add waiver expiry date`);
  }
  if (!waiver.sourceArtifactId) {
    errors.push(`assurance waiver ${waiver.id} for ${claimId} is missing source artifact; next action: link the waiver to its source artifact`);
  }
  if ((claim.evidenceRefs.length + claim.missingEvidenceRefs.length) === 0) {
    errors.push(`assurance waiver ${waiver.id} for ${claimId} is missing related evidence link; next action: link evidence or missing-evidence refs`);
  }
  return errors;
}

function normalizeAssuranceClaim(claim, nowDate) {
  const id = String(claim?.id || claim?.claimId || '').trim();
  const status = String(claim?.status || 'unresolved').trim() || 'unresolved';
  const evidenceRefs = normalizeIdRefs(claim?.evidenceRefs);
  const missingEvidenceRefs = normalizeIdRefs(claim?.missingEvidenceRefs);
  const waiverRefs = normalizeClaimWaivers(claim, nowDate);
  let result = 'report-only';
  if (waiverRefs.some((waiver) => waiver.status === 'expired' || waiver.status === 'orphan')) {
    result = 'block';
  } else if (status === 'unresolved') {
    result = 'block';
  } else if (status === 'waived' || waiverRefs.some((waiver) => waiver.status === 'active' || waiver.status === 'expiringSoon')) {
    result = 'waived';
  } else if (status === 'satisfied' && missingEvidenceRefs.length === 0) {
    result = 'pass';
  }

  return {
    claimId: id,
    result,
    status,
    evidenceRefs,
    missingEvidenceRefs,
    waiverRefs: waiverRefs.map((waiver) => waiver.id),
    waivers: waiverRefs,
  };
}

function normalizeClaimLevelSummaryClaim(claim, nowDate) {
  const id = String(claim?.claimId || claim?.id || '').trim();
  const status = String(claim?.state || claim?.status || 'unresolved').trim() || 'unresolved';
  const evidenceRefs = normalizeIdRefs(claim?.evidenceRefs);
  const missingEvidenceRefs = normalizeIdRefs(claim?.missingEvidenceRefs);
  const waiverRefs = normalizeClaimWaivers(claim, nowDate);
  const decisionResult = normalizeAssuranceResult(claim?.decision?.result, 'report-only');
  let result = decisionResult;

  if (status === 'failed' || status === 'unresolved') {
    result = 'block';
  } else if (missingEvidenceRefs.length > 0 && status !== 'waived' && status !== 'not-applicable') {
    result = 'block';
  } else if (status === 'waived' || waiverRefs.some((waiver) => waiver.status === 'active' || waiver.status === 'expiringSoon')) {
    result = 'waived';
  } else if (['satisfied', 'tested', 'model-checked', 'proved'].includes(status) && missingEvidenceRefs.length === 0) {
    result = 'pass';
  } else if (status === 'not-applicable') {
    result = 'report-only';
  }

  return {
    claimId: id,
    result,
    status,
    evidenceRefs,
    missingEvidenceRefs,
    waiverRefs: waiverRefs.map((waiver) => waiver.id),
    waivers: waiverRefs,
  };
}

function inspectClaimEvidenceManifest(manifestPath = CLAIM_EVIDENCE_MANIFEST_PATH, now = new Date().toISOString()) {
  const absolutePath = path.resolve(manifestPath);
  const nowDate = toDateOnly(now);
  const baseState = {
    path: absolutePath,
    present: false,
    schemaVersion: null,
    generatedAt: null,
    summary: {
      totalClaims: 0,
      fullySupported: 0,
      partiallySupported: 0,
      waived: 0,
      unresolved: 0,
    },
    claims: [],
    warnings: [],
    errors: [],
  };

  if (!fs.existsSync(absolutePath)) {
    return baseState;
  }

  try {
    const payload = JSON.parse(fs.readFileSync(absolutePath, 'utf8'));
    const claims = (Array.isArray(payload?.claims) ? payload.claims : [])
      .map((claim) => normalizeAssuranceClaim(claim, nowDate))
      .filter((claim) => claim.claimId);
    const securitySummary = normalizeManifestSecuritySummary(payload?.summary?.security);
    return {
      ...baseState,
      present: true,
      schemaVersion: String(payload?.schemaVersion || '').trim() || null,
      generatedAt: String(payload?.generatedAt || '').trim() || null,
      summary: {
        totalClaims: Number(payload?.summary?.totalClaims ?? claims.length) || 0,
        fullySupported: Number(payload?.summary?.fullySupported ?? 0) || 0,
        partiallySupported: Number(payload?.summary?.partiallySupported ?? 0) || 0,
        waived: Number(payload?.summary?.waived ?? 0) || 0,
        unresolved: Number(payload?.summary?.unresolved ?? 0) || 0,
        ...(securitySummary ? { security: securitySummary } : {}),
      },
      claims,
    };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return {
      ...baseState,
      present: true,
      errors: [`failed to parse claim evidence manifest: ${message}`],
    };
  }
}

function inspectClaimLevelSummary(summaryPath = CLAIM_LEVEL_SUMMARY_PATH, now = new Date().toISOString()) {
  const absolutePath = path.resolve(summaryPath);
  const nowDate = toDateOnly(now);
  const baseState = {
    path: absolutePath,
    present: false,
    schemaVersion: null,
    generatedAt: null,
    summary: {
      totalClaims: 0,
      fullySupported: 0,
      partiallySupported: 0,
      waived: 0,
      unresolved: 0,
    },
    claims: [],
    warnings: [],
    errors: [],
  };

  if (!fs.existsSync(absolutePath)) {
    return baseState;
  }

  try {
    const payload = JSON.parse(fs.readFileSync(absolutePath, 'utf8'));
    const claims = (Array.isArray(payload?.claims) ? payload.claims : [])
      .map((claim) => normalizeClaimLevelSummaryClaim(claim, nowDate))
      .filter((claim) => claim.claimId);
    return {
      ...baseState,
      present: true,
      schemaVersion: String(payload?.schemaVersion || '').trim() || null,
      generatedAt: String(payload?.generatedAt || '').trim() || null,
      summary: {
        totalClaims: Number(payload?.summary?.totalClaims ?? claims.length) || 0,
        fullySupported: Number(payload?.summary?.satisfied ?? 0) + Number(payload?.summary?.tested ?? 0) + Number(payload?.summary?.modelChecked ?? 0) + Number(payload?.summary?.proved ?? 0) || 0,
        partiallySupported: Number(payload?.summary?.runtimeMitigated ?? 0) || 0,
        waived: Number(payload?.summary?.waived ?? 0) || 0,
        unresolved: Number(payload?.summary?.unresolved ?? 0) + Number(payload?.summary?.failed ?? 0) || 0,
      },
      claims,
    };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return {
      ...baseState,
      present: true,
      errors: [`failed to parse claim-level summary: ${message}`],
    };
  }
}

function inspectAssuranceEvidence(now = new Date().toISOString()) {
  const claimLevelSummary = inspectClaimLevelSummary(CLAIM_LEVEL_SUMMARY_PATH, now);
  if (claimLevelSummary.present) {
    return claimLevelSummary;
  }
  return inspectClaimEvidenceManifest(CLAIM_EVIDENCE_MANIFEST_PATH, now);
}

function flattenAssuranceWaivers(claims) {
  return (Array.isArray(claims) ? claims : []).flatMap((claim) =>
    (Array.isArray(claim.waivers) ? claim.waivers : []).map((waiver) => ({
      ...waiver,
      claimId: claim.claimId,
    })),
  );
}

function buildAssuranceEvaluation(manifestState, options = {}) {
  const modeState = normalizeAssuranceMode(options.assuranceMode);
  const warnings = [...(Array.isArray(manifestState?.warnings) ? manifestState.warnings : [])];
  const errors = [...(Array.isArray(manifestState?.errors) ? manifestState.errors : [])];
  if (modeState.warning) warnings.push(modeState.warning);
  if (!manifestState?.present) {
    warnings.push(`claim evidence manifest not found: ${manifestState?.path || path.resolve(CLAIM_EVIDENCE_MANIFEST_PATH)}`);
    if (modeState.value === 'strict') {
      errors.push(`required assurance artifact missing: ${manifestState?.path || path.resolve(CLAIM_LEVEL_SUMMARY_PATH)}; next action: generate claim-level summary or claim-evidence manifest`);
    }
  }

  const claims = Array.isArray(manifestState?.claims) ? manifestState.claims : [];
  const waivers = flattenAssuranceWaivers(claims);
  for (const claim of claims) {
    for (const waiver of Array.isArray(claim.waivers) ? claim.waivers : []) {
      errors.push(...waiverValidationErrors(waiver, claim));
    }
    if (claim.result === 'block') {
      if (claim.status === 'failed') {
        errors.push(`assurance claim ${claim.claimId} has failed evidence; next action: fix the failing evidence or provide a valid waiver`);
      } else if (claim.missingEvidenceRefs.length > 0) {
        errors.push(`assurance claim ${claim.claimId} is missing required evidence: ${claim.missingEvidenceRefs.join(', ')}; next action: add evidence or provide a valid waiver`);
      } else {
        errors.push(`assurance claim ${claim.claimId} is unresolved; next action: satisfy, waive, or mark the claim not applicable`);
      }
    }
  }
  const hasBlockingWaiver = waivers.some((waiver) => waiver.status === 'expired' || waiver.status === 'orphan' || waiver.status === 'unknown');
  const result = errors.length > 0 || hasBlockingWaiver || claims.some((claim) => claim.result === 'block')
    ? 'block'
    : (claims.some((claim) => claim.result === 'waived')
      ? 'waived'
      : (claims.length > 0 && claims.every((claim) => claim.result === 'pass') ? 'pass' : 'report-only'));

  const securitySummary = normalizeManifestSecuritySummary(manifestState?.summary?.security);
  if (securitySummary?.highOrCriticalOpen > 0) {
    warnings.push(`security high/critical findings require review: ${securitySummary.highOrCriticalOpen}`);
  }
  if (securitySummary?.needsHumanReview > 0) {
    warnings.push(`security findings need human review: ${securitySummary.needsHumanReview}`);
  }

  const summary = {
    totalClaims: Number(manifestState?.summary?.totalClaims ?? claims.length) || 0,
    pass: claims.filter((claim) => claim.result === 'pass').length,
    waived: claims.filter((claim) => claim.result === 'waived').length,
    reportOnly: claims.filter((claim) => claim.result === 'report-only').length,
    block: claims.filter((claim) => claim.result === 'block').length,
    activeWaivers: waivers.filter((waiver) => waiver.status === 'active').length,
    expiringSoonWaivers: waivers.filter((waiver) => waiver.status === 'expiringSoon').length,
    expiredWaivers: waivers.filter((waiver) => waiver.status === 'expired').length,
    orphanWaivers: waivers.filter((waiver) => waiver.status === 'orphan').length,
    ...(securitySummary ? { security: securitySummary } : {}),
  };

  return {
    mode: modeState.value,
    result,
    manifest: {
      path: manifestState?.path || path.resolve(CLAIM_EVIDENCE_MANIFEST_PATH),
      present: Boolean(manifestState?.present),
      schemaVersion: manifestState?.schemaVersion ?? null,
      generatedAt: manifestState?.generatedAt ?? null,
    },
    summary,
    claims: claims.map((claim) => {
      const normalizedClaim = { ...claim };
      delete normalizedClaim.waivers;
      return normalizedClaim;
    }),
    waivers,
    warnings,
    errors,
  };
}

function hasTemplateSection(body, sectionName) {
  if (!body) return false;
  const escaped = sectionName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const headingPattern = new RegExp(`^\\s*#{1,6}\\s*${escaped}(?:\\s+.*)?$`, 'im');
  if (headingPattern.test(body)) return true;
  if (/^[A-Za-z0-9_\\s]+$/.test(sectionName)) {
    const boundaryPattern = new RegExp(`(^|[^A-Za-z0-9_])${escaped}($|[^A-Za-z0-9_])`, 'i');
    return boundaryPattern.test(body);
  }
  return String(body).toLowerCase().includes(String(sectionName).toLowerCase());
}

function evaluatePolicyGate({
  policy,
  pullRequest,
  changedFiles,
  reviews,
  statusRollup,
  reviewTopology,
  approvalOverride,
  assuranceMode,
  assurance,
  planArtifact,
}) {
  const errors = [];
  const warnings = [];
  const riskLabels = getRiskLabels(policy);
  const currentLabels = normalizeLabelNames(pullRequest?.labels || []);
  const currentLabelSet = new Set(currentLabels);
  const currentRiskLabels = currentLabels.filter(
    (label) => label === riskLabels.low || label === riskLabels.high,
  );

  if (currentRiskLabels.length === 0) {
    errors.push(`missing risk label: ${riskLabels.low} or ${riskLabels.high}`);
  } else if (currentRiskLabels.length > 1) {
    errors.push(`multiple risk labels: ${currentRiskLabels.join(', ')}`);
  }

  const inferred = inferRiskLevel(policy, changedFiles);
  const selectedRiskLabel = currentRiskLabels.length === 1 ? currentRiskLabels[0] : null;
  if (selectedRiskLabel && selectedRiskLabel !== inferred.level) {
    errors.push(`risk label mismatch: expected ${inferred.level}, found ${selectedRiskLabel}`);
  }

  const entries = collapseCheckEntriesByName(toCheckEntries(statusRollup));
  const requiredChecks = getRequiredChecks(policy)
    .filter((value) => value !== 'policy-gate');
  const requiredCheckResults = requiredChecks.map((checkName) => ({
    checkName,
    result: evaluateCheckRequirement(entries, [checkName]),
  }));
  for (const item of requiredCheckResults) {
    if (item.result.status === 'failure') {
      errors.push(`required check failed: ${item.checkName}`);
      continue;
    }
    if (item.result.status === 'pending' || item.result.status === 'missing') {
      warnings.push(`required check not ready yet: ${item.checkName} (${item.result.status})`);
    }
  }

  const approvalConfig = resolveApprovalGateConfig(policy, {
    reviewTopology,
    approvalOverride,
  });
  warnings.push(...approvalConfig.warnings);

  const minApprovals = approvalConfig.effectiveMinApprovals;
  const approvals = countHumanApprovals(reviews);
  const { requiredLabels } = collectRequiredLabels(policy, changedFiles);
  const policyLabelsRequired = isPolicyLabelRequirementEnabled(policy);
  const missingRequiredLabels = requiredLabels.filter((label) => !currentLabelSet.has(label));

  const highRiskLabel = riskLabels.high;
  const isHighRisk = selectedRiskLabel === highRiskLabel || inferred.level === highRiskLabel;
  const gateCheckResults = [];
  const planArtifactEvaluation = evaluatePlanArtifactRequirement(policy, isHighRisk, planArtifact);
  errors.push(...planArtifactEvaluation.errors);
  warnings.push(...planArtifactEvaluation.warnings);

  const assuranceModeState = resolveAssuranceMode(assuranceMode);
  if (assuranceModeState.warning) warnings.push(`assurance: ${assuranceModeState.warning}`);
  const assuranceEvaluation = buildAssuranceEvaluation(
    assurance || inspectAssuranceEvidence(),
    { assuranceMode: assuranceModeState.value },
  );
  warnings.push(...assuranceEvaluation.warnings.map((warning) => `assurance: ${warning}`));
  if (assuranceEvaluation.mode === 'strict' && assuranceEvaluation.result === 'block') {
    errors.push(...assuranceEvaluation.errors.map((error) => `assurance: ${error}`));
    if (!errors.includes('assurance decision is block')) {
      errors.push('assurance decision is block');
    }
  } else if (assuranceEvaluation.errors.length > 0) {
    warnings.push(...assuranceEvaluation.errors.map((error) => `assurance: ${error}`));
  }

  if (isHighRisk) {
    if (approvals < minApprovals) {
      errors.push(`human approvals are insufficient: required ${minApprovals}, got ${approvals}`);
    }
    if (policyLabelsRequired && missingRequiredLabels.length > 0) {
      errors.push(`missing required labels: ${missingRequiredLabels.join(', ')}`);
    } else if (!policyLabelsRequired && missingRequiredLabels.length > 0) {
      warnings.push(`policy labels missing (allowed by config): ${missingRequiredLabels.join(', ')}`);
    }
    for (const label of requiredLabels) {
      if (!currentLabelSet.has(label)) continue;
      const patterns = getGateCheckPatternsForLabel(policy, label);
      const result = evaluateCheckRequirement(entries, patterns);
      gateCheckResults.push({ label, patterns, result });
      if (result.status === 'failure' || result.status === 'missing') {
        errors.push(`required gate check not green for label ${label} (${result.status})`);
      } else if (result.status === 'pending') {
        if (isPendingGateFailureEnabled(policy)) {
          errors.push(`required gate check pending for label ${label}`);
        } else {
          warnings.push(`required gate check pending for label ${label}`);
        }
      }
      if (patterns.length === 0) {
        warnings.push(`no gate_checks mapping configured for label ${label}`);
      }
    }
  }

  const body = String(pullRequest?.body || '');
  if (!hasTemplateSection(body, 'Rollback')) {
    warnings.push('PR body is missing Rollback section');
  }
  if (!hasTemplateSection(body, 'Acceptance') && !hasTemplateSection(body, '受入基準')) {
    warnings.push('PR body is missing Acceptance section');
  }

  return {
    ok: errors.length === 0,
    errors,
    warnings,
    inferredRisk: inferred,
    selectedRiskLabel,
    currentRiskLabels,
    reviewTopology: approvalConfig.reviewTopology,
    approvals,
    minApprovals,
    policyMinApprovals: approvalConfig.policyMinApprovals,
    topologyMinApprovals: approvalConfig.topologyMinApprovals,
    effectiveMinApprovals: approvalConfig.effectiveMinApprovals,
    minApprovalsSource: approvalConfig.minApprovalsSource,
    requiredLabels,
    missingRequiredLabels,
    requiredCheckResults,
    gateCheckResults,
    planArtifact: planArtifactEvaluation,
    assurance: assuranceEvaluation,
  };
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function appendStepSummary(markdown) {
  const summaryPath = process.env.GITHUB_STEP_SUMMARY;
  if (!summaryPath) return;
  ensureDirectory(summaryPath);
  fs.appendFileSync(summaryPath, markdown);
}

function formatMarkdownCell(value) {
  const normalized = String(value ?? '').replace(/\s+/g, ' ').trim();
  return normalized || '(none)';
}

function formatAssuranceWaiverLine(waiver) {
  return [
    `id=${formatMarkdownCell(waiver?.id)}`,
    `claim=${formatMarkdownCell(waiver?.claimId)}`,
    `status=${formatMarkdownCell(waiver?.status)}`,
    `owner=${formatMarkdownCell(waiver?.owner)}`,
    `expires=${formatMarkdownCell(waiver?.expires)}`,
    `reason=${formatMarkdownCell(waiver?.reason)}`,
  ].join(', ');
}

function buildMarkdownSummary(prNumber, evaluation) {
  const lines = [
    '### Policy Gate',
    `- PR: #${prNumber}`,
    `- result: ${evaluation.ok ? 'PASS' : 'FAIL'}`,
    `- selected risk label: ${evaluation.selectedRiskLabel || '(none)'}`,
    `- inferred risk: ${evaluation.inferredRisk.level}`,
    `- review topology: ${evaluation.reviewTopology}`,
    `- approvals: ${evaluation.approvals}/${evaluation.effectiveMinApprovals} (source: ${evaluation.minApprovalsSource}, policy: ${evaluation.policyMinApprovals})`,
  ];

  if (evaluation.requiredLabels.length > 0) {
    lines.push(`- required labels (by diff): ${evaluation.requiredLabels.join(', ')}`);
  }
  if (evaluation.missingRequiredLabels.length > 0) {
    lines.push(`- missing required labels: ${evaluation.missingRequiredLabels.join(', ')}`);
  }
  if (evaluation.planArtifact) {
    lines.push(`- plan artifact: ${evaluation.planArtifact.result}${evaluation.planArtifact.required ? ' (required)' : ' (optional)'}`);
    if (evaluation.planArtifact.present) {
      lines.push(`  - path: ${evaluation.planArtifact.path}`);
      if (evaluation.planArtifact.riskSelected) {
        lines.push(`  - declared risk: ${evaluation.planArtifact.riskSelected}`);
      }
      if (evaluation.planArtifact.source?.repository && evaluation.planArtifact.source?.prNumber) {
        lines.push(`  - declared source: ${evaluation.planArtifact.source.repository}#${evaluation.planArtifact.source.prNumber}`);
      }
    }
  }
  if (evaluation.assurance) {
    lines.push(`- assurance: ${evaluation.assurance.result} (${evaluation.assurance.mode})`);
    lines.push(`  - assurance artifact: ${evaluation.assurance.manifest.present ? 'present' : 'missing'} (${evaluation.assurance.manifest.schemaVersion ?? 'n/a'})`);
    lines.push(`  - claims: pass=${evaluation.assurance.summary.pass}, waived=${evaluation.assurance.summary.waived}, report-only=${evaluation.assurance.summary.reportOnly}, block=${evaluation.assurance.summary.block}`);
    if (evaluation.assurance.summary.security) {
      const security = evaluation.assurance.summary.security;
      lines.push(`  - security findings: total=${security.findings}, needs-human-review=${security.needsHumanReview}, high/critical-open=${security.highOrCriticalOpen}, out-of-scope=${security.outOfScope}, rejected=${security.rejected}, assumption-validation-required=${security.assumptionValidationRequired}, assumption-residual-risk=${security.assumptionResidualRisk}`);
    }
    if (evaluation.assurance.waivers.length > 0) {
      lines.push(`  - waivers: active=${evaluation.assurance.summary.activeWaivers}, expiringSoon=${evaluation.assurance.summary.expiringSoonWaivers}, expired=${evaluation.assurance.summary.expiredWaivers}, orphan=${evaluation.assurance.summary.orphanWaivers}`);
      for (const waiver of evaluation.assurance.waivers) {
        lines.push(`    - ${formatAssuranceWaiverLine(waiver)}`);
      }
    }
  }

  if (evaluation.requiredCheckResults.length > 0) {
    lines.push('- required checks:');
    for (const item of evaluation.requiredCheckResults) {
      lines.push(`  - ${item.checkName}: ${item.result.status}`);
    }
  }

  if (evaluation.gateCheckResults.length > 0) {
    lines.push('- gate checks (high-risk labels):');
    for (const item of evaluation.gateCheckResults) {
      lines.push(`  - ${item.label}: ${item.result.status}`);
    }
  }

  if (evaluation.errors.length > 0) {
    lines.push('- blocking errors:');
    for (const error of evaluation.errors) {
      lines.push(`  - ${error}`);
    }
  }
  if (evaluation.warnings.length > 0) {
    lines.push('- warnings:');
    for (const warning of evaluation.warnings) {
      lines.push(`  - ${warning}`);
    }
  }
  return `${lines.join('\n')}\n`;
}

function persistReport(report, markdown) {
  ensureDirectory(OUTPUT_JSON_PATH);
  fs.writeFileSync(OUTPUT_JSON_PATH, `${JSON.stringify(report, null, 2)}\n`);
  ensureDirectory(OUTPUT_MD_PATH);
  fs.writeFileSync(OUTPUT_MD_PATH, markdown);
}

function buildPolicyGateReport({
  generatedAtUtc = new Date().toISOString(),
  repository,
  prNumber,
  changedFiles,
  evaluation,
}) {
  return {
    schemaVersion: SUMMARY_SCHEMA_VERSION,
    contractId: SUMMARY_CONTRACT_ID,
    generatedAtUtc,
    repository,
    prNumber,
    changedFiles,
    evaluation,
  };
}

function normalizeStringArray(value) {
  if (!Array.isArray(value)) return [];
  return value
    .map((item) => String(item || '').trim())
    .filter(Boolean);
}

function normalizeUniqueStringArray(value) {
  return [...new Set(normalizeStringArray(value))];
}

function buildPolicyInputPolicy(policy) {
  const riskLabels = getRiskLabels(policy);
  const optionalGates = normalizeUniqueStringArray(getOptionalGateLabels(policy));
  const requiredChecks = normalizeUniqueStringArray(getRequiredChecks(policy));
  const highRiskPaths = normalizeUniqueStringArray(policy?.classification?.high_risk_paths);
  const forceHighRiskWhen = normalizeUniqueStringArray(policy?.classification?.force_high_risk_when);
  const labelRequirements = Array.isArray(policy?.label_requirements) ? policy.label_requirements : [];
  const normalizedLabelRequirements = labelRequirements.map((rule, index) => ({
    id: String(rule?.id || `rule-${index + 1}`).trim() || `rule-${index + 1}`,
    whenAnyChanged: normalizeUniqueStringArray(rule?.when_any_changed),
    requireLabels: normalizeUniqueStringArray(rule?.require_labels),
  }));

  const gateCheckKeys = new Set([
    ...optionalGates,
    ...Object.keys(policy?.gate_checks || {}),
  ]);
  const gateChecks = {};
  for (const label of [...gateCheckKeys].map((item) => String(item || '').trim()).filter(Boolean).sort()) {
    gateChecks[label] = {
      patterns: normalizeUniqueStringArray(getGateCheckPatternsForLabel(policy, label)),
    };
  }

  return {
    labels: {
      risk: riskLabels,
      optionalGates,
    },
    requiredChecks,
    highRisk: {
      minHumanApprovals: getMinHumanApprovals(policy),
      requirePolicyLabels: isPolicyLabelRequirementEnabled(policy),
      requirePlanArtifact: isPlanArtifactRequired(policy),
      failWhenRequiredGateIsPending: isPendingGateFailureEnabled(policy),
    },
    classification: {
      highRiskPaths,
      forceHighRiskWhen,
    },
    labelRequirements: normalizedLabelRequirements,
    gateChecks,
  };
}

function normalizePolicyInputReviews(reviews) {
  const list = Array.isArray(reviews) ? reviews : [];
  return list
    .map((review) => {
      const id = Number(review?.id || 0);
      const state = String(review?.state || '').trim();
      const submittedAtRaw = review?.submitted_at || review?.submittedAt || null;
      const submittedAt = submittedAtRaw ? String(submittedAtRaw).trim() : null;
      const login = String(review?.user?.login || '').trim();
      const type = String(review?.user?.type || '').trim();
      if (!Number.isFinite(id) || id <= 0) return null;
      if (!state) return null;
      if (!login) return null;
      if (!type) return null;
      return {
        id: Math.trunc(id),
        state,
        submittedAt,
        user: { login, type },
      };
    })
    .filter(Boolean);
}

function normalizePolicyInputStatusRollup(statusRollup) {
  const list = Array.isArray(statusRollup) ? statusRollup : [];
  return list
    .map((item) => {
      if (!item || typeof item !== 'object') return null;
      const typename = String(item.__typename || '').trim();
      if (typename === 'CheckRun') {
        const name = String(item.name || '').trim();
        const status = String(item.status || '').trim();
        const conclusion = item.conclusion === null || item.conclusion === undefined
          ? null
          : String(item.conclusion || '').trim();
        const workflowName = String(item.workflowName || '').trim();
        const startedAtRaw = item.startedAt ?? item.started_at ?? null;
        const completedAtRaw = item.completedAt ?? item.completed_at ?? null;
        const startedAt = startedAtRaw === null || startedAtRaw === undefined
          ? null
          : (String(startedAtRaw || '').trim() || null);
        const completedAt = completedAtRaw === null || completedAtRaw === undefined
          ? null
          : (String(completedAtRaw || '').trim() || null);
        if (!name || !status) return null;
        return {
          __typename: 'CheckRun',
          name,
          status,
          conclusion,
          workflowName,
          startedAt,
          completedAt,
        };
      }
      if (typename === 'StatusContext') {
        const context = String(item.context || '').trim();
        const state = String(item.state || '').trim();
        if (!context || !state) return null;
        return {
          __typename: 'StatusContext',
          context,
          state,
        };
      }
      return null;
    })
    .filter(Boolean);
}

function buildPolicyInputV1({
  repo,
  prNumber,
  policyPath,
  policy,
  pullRequest,
  changedFiles,
  reviews,
  statusRollup,
  reviewTopology,
  approvalOverride,
  assuranceMode,
  assurance,
  now = new Date().toISOString(),
}) {
  const normalizedAssuranceMode = resolveAssuranceMode(assuranceMode).value;
  const input = {
    schemaVersion: '1.0.0',
    contractId: 'policy-input.v1',
    generatedAtUtc: now,
    repository: String(repo || '').trim(),
    prNumber: Number(prNumber) || 0,
    policyPath: String(policyPath || '').trim(),
    policy: buildPolicyInputPolicy(policy),
    pullRequest: {
      number: Number(prNumber) || 0,
      labels: normalizeUniqueStringArray(normalizeLabelNames(pullRequest?.labels || [])),
      body: String(pullRequest?.body || ''),
    },
    changedFiles: normalizeUniqueStringArray(changedFiles),
    reviews: normalizePolicyInputReviews(reviews),
    statusRollup: normalizePolicyInputStatusRollup(statusRollup),
    config: {
      reviewTopology: reviewTopology ?? null,
      approvalOverride: approvalOverride ?? null,
      assuranceMode: normalizedAssuranceMode,
    },
  };
  if (assurance) {
    input.assurance = assurance;
  }
  return input;
}

function buildPolicyDecisionV1({
  repo,
  prNumber,
  inputPath,
  engine,
  evaluation,
  now = new Date().toISOString(),
}) {
  return {
    schemaVersion: '1.0.0',
    contractId: 'policy-decision.v1',
    generatedAtUtc: now,
    repository: String(repo || '').trim(),
    prNumber: Number(prNumber) || 0,
    inputPath: String(inputPath || '').trim(),
    engine,
    evaluation,
  };
}

function persistPolicyContracts(policyInput, policyDecision) {
  ensureDirectory(POLICY_INPUT_PATH);
  fs.writeFileSync(POLICY_INPUT_PATH, `${JSON.stringify(policyInput, null, 2)}\n`);
  ensureDirectory(POLICY_DECISION_PATH);
  fs.writeFileSync(POLICY_DECISION_PATH, `${JSON.stringify(policyDecision, null, 2)}\n`);
}

async function run(options = parseArgs(process.argv)) {
  const repo = String(process.env.GITHUB_REPOSITORY || '').trim();
  if (!repo) {
    throw new Error('GITHUB_REPOSITORY is required');
  }
  const prNumber = resolvePrNumber(options.prNumber);
  if (!prNumber) {
    throw new Error('PR number is required (PR_NUMBER, --pr, or GITHUB_EVENT_PATH)');
  }

  const policy = loadRiskPolicy(options.policyPath);
  const pullRequest = fetchPullRequest(repo, prNumber);
  const changedFiles = fetchChangedFiles(repo, prNumber);
  const reviews = fetchReviews(repo, prNumber);
  const statusRollup = fetchStatusRollup(repo, prNumber);
  const planArtifact = inspectPlanArtifact(options.policyPath);
  const now = new Date().toISOString();
  const assurance = inspectAssuranceEvidence(now);

  const evaluation = evaluatePolicyGate({
    policy,
    pullRequest,
    changedFiles,
    reviews,
    statusRollup,
    reviewTopology: process.env.AE_REVIEW_TOPOLOGY,
    approvalOverride: process.env.AE_POLICY_MIN_HUMAN_APPROVALS,
    assuranceMode: process.env.AE_POLICY_ASSURANCE_MODE,
    assurance,
    planArtifact,
  });

  const policyInput = buildPolicyInputV1({
    repo,
    prNumber,
    policyPath: options.policyPath,
    policy,
    pullRequest,
    changedFiles,
    reviews,
    statusRollup,
    reviewTopology: process.env.AE_REVIEW_TOPOLOGY,
    approvalOverride: process.env.AE_POLICY_MIN_HUMAN_APPROVALS,
    assuranceMode: resolveAssuranceMode(process.env.AE_POLICY_ASSURANCE_MODE).value,
    assurance,
    now,
  });
  const policyDecision = buildPolicyDecisionV1({
    repo,
    prNumber,
    inputPath: POLICY_INPUT_PATH,
    engine: {
      kind: 'js',
      status: 'supported',
      version: process.version,
    },
    evaluation,
    now,
  });
  persistPolicyContracts(policyInput, policyDecision);

  const report = buildPolicyGateReport({
    generatedAtUtc: now,
    repository: repo,
    prNumber,
    changedFiles,
    evaluation,
  });
  const markdown = buildMarkdownSummary(prNumber, evaluation);
  persistReport(report, markdown);
  appendStepSummary(markdown);
  process.stdout.write(`${markdown}\n`);

  if (!evaluation.ok) {
    process.exitCode = 1;
  }
  return report;
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
    process.stderr.write(`[policy-gate] ${message}\n`);
    process.exit(1);
  }
}

export {
  buildAssuranceEvaluation,
  buildMarkdownSummary,
  buildPolicyInputV1,
  collapseCheckEntriesByName,
  evaluateCheckRequirement,
  evaluatePolicyGate,
  buildPolicyGateReport,
  inspectAssuranceEvidence,
  inspectClaimEvidenceManifest,
  inspectClaimLevelSummary,
  run,
  toCheckEntries,
};
