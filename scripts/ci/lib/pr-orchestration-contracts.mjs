import fs from 'node:fs';
import path from 'node:path';

function toNonEmptyString(value, fallback = '') {
  const normalized = String(value || '').trim();
  return normalized || fallback;
}

function splitRepository(repository) {
  const normalized = toNonEmptyString(repository);
  const [owner = '', name = ''] = normalized.split('/');
  return {
    owner: toNonEmptyString(owner, 'unknown-owner'),
    name: toNonEmptyString(name, 'unknown-repo'),
  };
}

function resolvePrState(status, reason) {
  const normalizedStatus = toNonEmptyString(status).toLowerCase();
  const normalizedReason = toNonEmptyString(reason).toLowerCase();
  if (normalizedStatus === 'done') {
    if (normalizedReason === 'already merged') return 'merged';
    return 'merge_eligible';
  }
  if (normalizedStatus === 'skip') {
    if (normalizedReason === 'draft pr') return 'draft';
    return 'ready_for_review';
  }
  return 'blocked';
}

function resolvePreviousState(state, reason) {
  const normalizedReason = toNonEmptyString(reason).toLowerCase();
  if (state === 'merged') return 'merge_eligible';
  if (state === 'merge_eligible') return 'gate_recheck';
  if (state === 'draft') return 'draft';
  if (state === 'ready_for_review') return 'ready_for_review';
  if (normalizedReason.startsWith('actionable review tasks pending:')) return 'review_feedback_pending';
  if (normalizedReason.startsWith('actionable execution failed:')) return 'action_execution';
  if (normalizedReason.startsWith('actionable execution incomplete:')) return 'action_execution';
  return 'gate_recheck';
}

function resolveReasonCode(reason) {
  const normalized = toNonEmptyString(reason).toLowerCase();
  if (!normalized) return 'autopilot.unknown';
  if (normalized === 'merge conflict') return 'vcs.merge_conflict';
  if (normalized === 'max rounds reached without convergence') return 'autopilot.max_rounds_exceeded';
  if (normalized === 'draft pr') return 'pr.draft';
  if (normalized === 'missing label autopilot:on') return 'policy.autopilot_label_missing';
  if (normalized === 'already merged') return 'pr.already_merged';
  if (normalized === 'auto-merge enabled') return 'merge.auto_merge_enabled';
  if (normalized === 'checks healthy, waiting for required checks/merge queue') return 'checks.waiting_queue';
  if (normalized === 'actionable review task scan truncated (pagination required)') return 'review.scan_truncated';
  if (normalized.startsWith('missing policy labels:')) return 'policy.required_labels_missing';
  if (normalized.startsWith('auto-label failed:')) return 'policy.auto_label_failed';
  if (normalized.startsWith('policy-label detection failed:')) return 'policy.label_detection_failed';
  if (normalized.startsWith('actionable review tasks pending:')) return 'review.actionable_pending';
  if (normalized.startsWith('actionable execution failed:')) return 'review.actionable_execution_failed';
  if (normalized.startsWith('actionable execution incomplete:')) return 'review.actionable_execution_incomplete';
  return 'autopilot.unknown';
}

function resolveBlockedOwner(reason) {
  const normalized = toNonEmptyString(reason).toLowerCase();
  if (
    normalized === 'merge conflict'
    || normalized.startsWith('missing policy labels:')
    || normalized.startsWith('actionable review tasks pending:')
    || normalized === 'draft pr'
    || normalized === 'missing label autopilot:on'
  ) {
    return 'human';
  }
  if (
    normalized.startsWith('policy-label detection failed:')
    || normalized.startsWith('auto-label failed:')
    || normalized === 'actionable review task scan truncated (pagination required)'
  ) {
    return 'ai';
  }
  return 'either';
}

function inferActionTaskKind(action) {
  const normalized = toNonEmptyString(action).toLowerCase();
  if (normalized.includes('auto-label policy labels')) return 'label_sync';
  if (normalized.includes('detect actionable')) return 'review_fetch';
  if (normalized.includes('apply copilot auto-fix')) return 'suggestion_apply';
  if (normalized.includes('actionable execution')) return 'suggestion_apply';
  if (normalized.includes('dispatch')) return 'workflow_dispatch';
  if (normalized.includes('evaluate auto-merge eligibility')) return 'gate_recheck';
  return 'artifact_collect';
}

function mapActionTasks(actions) {
  const list = Array.isArray(actions) ? actions : [];
  if (list.length === 0) {
    return [
      {
        id: 't1',
        kind: 'gate_recheck',
        title: 'No lane actions recorded; keep current status',
        owner: 'either',
        status: 'planned',
      },
    ];
  }
  return list.map((action, index) => ({
    id: `t${index + 1}`,
    kind: inferActionTaskKind(action),
    title: toNonEmptyString(action, `lane-action-${index + 1}`),
    owner: 'ai',
    status: 'completed',
  }));
}

function ensureParentDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

export function buildPrStateV1({
  repository,
  prNumber,
  headRefName,
  headRefOid,
  result,
  requiredChecks = ['gate'],
  workflow = process.env.GITHUB_WORKFLOW || '',
  runId = process.env.GITHUB_RUN_ID || '',
  now = new Date().toISOString(),
}) {
  const safeResult = result && typeof result === 'object' ? result : {};
  const state = resolvePrState(safeResult.status, safeResult.reason);
  const previousState = resolvePreviousState(state, safeResult.reason);
  const reasonCode = resolveReasonCode(safeResult.reason);
  const checks = Array.isArray(requiredChecks) && requiredChecks.length > 0
    ? requiredChecks
    : ['gate'];
  const checkResults = checks.map((name) => {
    if (name === 'gate') {
      return {
        name,
        status: toNonEmptyString(safeResult.gateStatus, 'missing'),
      };
    }
    return { name, status: 'missing' };
  });
  const blocked = state === 'blocked'
    ? {
      reasonCode,
      message: toNonEmptyString(safeResult.reason, 'blocked'),
      unblockActions: Array.isArray(safeResult.unblockActions) && safeResult.unblockActions.length > 0
        ? safeResult.unblockActions.map((item) => toNonEmptyString(item)).filter(Boolean)
        : ['Inspect required checks and rerun `/autopilot run`.'],
      ownerHint: resolveBlockedOwner(safeResult.reason),
    }
    : null;

  return {
    schemaVersion: '1.0.0',
    contractId: 'pr-state.v1',
    repository: splitRepository(repository),
    pullRequest: {
      number: Number(prNumber) || 0,
      headSha: toNonEmptyString(headRefOid, 'unknown'),
      baseRef: toNonEmptyString(process.env.GITHUB_BASE_REF || 'main'),
      headRef: toNonEmptyString(headRefName, 'unknown'),
    },
    state,
    previousState,
    transition: {
      event: reasonCode,
      source: 'codex-autopilot-lane',
      actor: toNonEmptyString(process.env.GITHUB_ACTOR || 'github-actions[bot]'),
      at: now,
    },
    blocked,
    requiredChecks: checks,
    checkResults,
    evidence: {
      summaryPaths: [
        'artifacts/ci/automation-report.json',
      ],
      artifactRunId: toNonEmptyString(runId, 'local-run'),
    },
    metadata: {
      runId: toNonEmptyString(runId, 'local-run'),
      workflow: toNonEmptyString(workflow, 'codex-autopilot-lane'),
      createdAt: now,
      updatedAt: now,
      traceId: toNonEmptyString(process.env.AE_TRACE_ID || ''),
    },
  };
}

export function buildExecutionPlanV1({
  repository,
  prNumber,
  headRefOid,
  result,
  now = new Date().toISOString(),
  workflow = process.env.GITHUB_WORKFLOW || '',
  runId = process.env.GITHUB_RUN_ID || '',
}) {
  const safeResult = result && typeof result === 'object' ? result : {};
  const status = toNonEmptyString(safeResult.status, 'blocked').toLowerCase();
  const targetState = resolvePrState(status, safeResult.reason);
  const tasks = mapActionTasks(safeResult.actions || []);
  if (status === 'blocked') {
    tasks.push({
      id: `t${tasks.length + 1}`,
      kind: 'block_emit',
      title: 'Emit blocked summary and unblock guidance',
      owner: 'ai',
      status: 'completed',
      result: {
        status: 'success',
        message: toNonEmptyString(safeResult.reason, 'blocked'),
      },
    });
  } else {
    tasks.push({
      id: `t${tasks.length + 1}`,
      kind: 'comment_emit',
      title: 'Emit lane summary comment',
      owner: 'ai',
      status: toNonEmptyString(process.env.AE_AUTOPILOT_DRY_RUN) === '1' ? 'skipped' : 'completed',
      result: {
        status: toNonEmptyString(process.env.AE_AUTOPILOT_DRY_RUN) === '1' ? 'skipped' : 'success',
      },
    });
  }

  return {
    schemaVersion: '1.0.0',
    contractId: 'execution-plan.v1',
    planId: `autopilot-pr-${Number(prNumber) || 0}-${toNonEmptyString(runId, 'local-run')}`,
    repository: splitRepository(repository),
    pullRequest: {
      number: Number(prNumber) || 0,
      headSha: toNonEmptyString(headRefOid, 'unknown'),
    },
    trigger: {
      kind: 'autopilot',
      source: 'codex-autopilot-lane',
      at: now,
    },
    targetState,
    tasks,
    metadata: {
      runId: toNonEmptyString(runId, 'local-run'),
      workflow: toNonEmptyString(workflow, 'codex-autopilot-lane'),
      generatedAt: now,
      generator: 'scripts/ci/codex-autopilot-lane.mjs',
    },
  };
}

export function writePrOrchestrationContracts({
  enabled,
  prState,
  executionPlan,
  prStatePath,
  executionPlanPath,
}) {
  if (!enabled) {
    return {
      written: false,
      prStatePath: '',
      executionPlanPath: '',
    };
  }
  const resolvedPrStatePath = path.resolve(toNonEmptyString(prStatePath, 'artifacts/ci/pr-state-v1.json'));
  const resolvedExecutionPlanPath = path.resolve(
    toNonEmptyString(executionPlanPath, 'artifacts/ci/execution-plan-v1.json'),
  );
  ensureParentDirectory(resolvedPrStatePath);
  ensureParentDirectory(resolvedExecutionPlanPath);
  fs.writeFileSync(resolvedPrStatePath, `${JSON.stringify(prState, null, 2)}\n`, 'utf8');
  fs.writeFileSync(resolvedExecutionPlanPath, `${JSON.stringify(executionPlan, null, 2)}\n`, 'utf8');
  return {
    written: true,
    prStatePath: resolvedPrStatePath,
    executionPlanPath: resolvedExecutionPlanPath,
  };
}

export {
  resolvePrState,
  resolveReasonCode,
  inferActionTaskKind,
};
