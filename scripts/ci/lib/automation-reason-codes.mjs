import { resolveReasonCode as resolveAutopilotReasonCode } from './pr-orchestration-contracts.mjs';

function toNonEmptyString(value, fallback = '') {
  const normalized = String(value || '').trim();
  return normalized || fallback;
}

function normalize(value) {
  return toNonEmptyString(value).toLowerCase();
}

function resolveCommonReasonCode(reason) {
  const normalized = normalize(reason);

  if (normalized === 'github_repository is required') return 'automation.missing_repository';
  if (normalized === 'github_repository format is invalid') return 'automation.invalid_repository_format';
  if (normalized === 'pr_number is required') return 'automation.missing_pr_number';
  if (normalized === 'pr_number is required and must be a positive integer') return 'automation.missing_pr_number';

  if (normalized.includes('ae_automation_global_disable is enabled')) return 'automation.globally_disabled';
  if (normalized.includes('is disabled after config resolution')) return 'automation.disabled_by_config';
  if (normalized.includes('is not in ai_review_actors/copilot_actors')) return 'automation.actor_not_allowed';

  if (normalized === 'no pr targets found') return 'automation.no_targets';
  if (normalized === 'workflow_run has no associated pull request') return 'automation.workflow_run_no_pr';
  if (normalized === 'all targets skipped') return 'automation.targets_skipped';

  if (/^[1-9][0-9]* target\(s\) failed$/u.test(normalized)) return 'automation.targets_failed';
  if (/^[1-9][0-9]* target\(s\) blocked$/u.test(normalized)) return 'automation.targets_blocked';

  return '';
}

export function resolveAutomationReasonCode({ tool, status, reason }) {
  const toolNormalized = normalize(tool);
  const statusNormalized = normalize(status);
  const reasonNormalized = toNonEmptyString(reason);

  const common = resolveCommonReasonCode(reasonNormalized);
  if (common) return common;

  if (toolNormalized === 'codex-autopilot-lane' && statusNormalized !== 'resolved') {
    return resolveAutopilotReasonCode(reasonNormalized);
  }

  if (statusNormalized && statusNormalized !== 'resolved') {
    return 'automation.unknown';
  }
  return '';
}
