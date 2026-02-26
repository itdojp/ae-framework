import fs from 'node:fs';
import path from 'node:path';
import micromatch from 'micromatch';
import yaml from 'yaml';

const DEFAULT_POLICY_PATH = 'policy/risk-policy.yml';

const FORCE_CONDITION_TO_RULE_ID = {
  contains_dependency_manifest_change: 'dependency-supply-chain',
  contains_external_interface_change: 'external-interface',
  contains_context_boundary_change: 'context-pack-boundary',
};

function normalizeStringArray(value) {
  if (!Array.isArray(value)) return [];
  return value
    .map((item) => String(item || '').trim())
    .filter(Boolean);
}

function normalizeChangedFiles(changedFiles) {
  if (!Array.isArray(changedFiles)) return [];
  return changedFiles
    .map((item) => String(item || '').trim())
    .filter(Boolean)
    .sort();
}

function toSortedUnique(values) {
  return [...new Set(values)].sort();
}

function loadRiskPolicy(policyPath = DEFAULT_POLICY_PATH) {
  const resolvedPath = path.resolve(policyPath);
  const raw = fs.readFileSync(resolvedPath, 'utf8');
  const parsed = yaml.parse(raw);
  if (!parsed || typeof parsed !== 'object') {
    throw new Error(`Invalid risk policy: ${resolvedPath}`);
  }
  return parsed;
}

function getRiskLabels(policy) {
  const low = String(policy?.labels?.risk?.low || 'risk:low').trim() || 'risk:low';
  const high = String(policy?.labels?.risk?.high || 'risk:high').trim() || 'risk:high';
  return { low, high };
}

function getOptionalGateLabels(policy) {
  return normalizeStringArray(policy?.labels?.optional_gates);
}

function getRequiredChecks(policy) {
  return normalizeStringArray(policy?.required_checks);
}

function getMinHumanApprovals(policy) {
  const value = Number(policy?.high_risk?.min_human_approvals ?? 1);
  if (!Number.isFinite(value) || value < 0) {
    return 1;
  }
  return Math.trunc(value);
}

function isPolicyLabelRequirementEnabled(policy) {
  const value = policy?.high_risk?.require_policy_labels;
  if (typeof value === 'boolean') return value;
  return true;
}

function isPendingGateFailureEnabled(policy) {
  return Boolean(policy?.high_risk?.fail_when_required_gate_is_pending);
}

function matchChangedFiles(changedFiles, patterns) {
  const normalizedFiles = normalizeChangedFiles(changedFiles);
  const normalizedPatterns = normalizeStringArray(patterns);
  if (normalizedFiles.length === 0 || normalizedPatterns.length === 0) {
    return [];
  }
  return normalizedFiles.filter((file) => micromatch.isMatch(file, normalizedPatterns, { dot: true }));
}

function evaluateLabelRequirements(policy, changedFiles) {
  const rules = Array.isArray(policy?.label_requirements) ? policy.label_requirements : [];
  return rules.map((rule, index) => {
    const id = String(rule?.id || `rule-${index + 1}`);
    const whenAnyChanged = normalizeStringArray(rule?.when_any_changed);
    const requiredLabels = normalizeStringArray(rule?.require_labels);
    const matchedFiles = matchChangedFiles(changedFiles, whenAnyChanged);
    return {
      id,
      whenAnyChanged,
      requiredLabels,
      matchedFiles,
      matched: matchedFiles.length > 0,
    };
  });
}

function collectRequiredLabels(policy, changedFiles) {
  const evaluations = evaluateLabelRequirements(policy, changedFiles);
  const required = [];
  for (const evaluation of evaluations) {
    if (!evaluation.matched) continue;
    required.push(...evaluation.requiredLabels);
  }
  return {
    requiredLabels: toSortedUnique(required),
    evaluations,
  };
}

function inferRiskLevel(policy, changedFiles) {
  const labels = getRiskLabels(policy);
  const normalizedChangedFiles = normalizeChangedFiles(changedFiles);
  const highRiskPathMatches = matchChangedFiles(
    normalizedChangedFiles,
    normalizeStringArray(policy?.classification?.high_risk_paths),
  );
  const forceConditions = normalizeStringArray(policy?.classification?.force_high_risk_when);
  const { evaluations } = collectRequiredLabels(policy, normalizedChangedFiles);
  const evaluationMap = new Map(evaluations.map((item) => [item.id, item]));

  const forceHighRiskTriggers = forceConditions
    .map((condition) => {
      const mappedRuleId = FORCE_CONDITION_TO_RULE_ID[condition];
      if (!mappedRuleId) return null;
      const matchedRule = evaluationMap.get(mappedRuleId);
      if (!matchedRule || !matchedRule.matched) return null;
      return {
        condition,
        ruleId: mappedRuleId,
        matchedFiles: matchedRule.matchedFiles,
      };
    })
    .filter(Boolean);

  const inferredHigh = highRiskPathMatches.length > 0 || forceHighRiskTriggers.length > 0;
  return {
    level: inferredHigh ? labels.high : labels.low,
    labels,
    highRiskPathMatches,
    forceHighRiskTriggers,
  };
}

function getGateCheckPatternsForLabel(policy, label) {
  const key = String(label || '').trim();
  if (!key) return [];
  const raw = policy?.gate_checks?.[key];
  if (Array.isArray(raw)) {
    return normalizeStringArray(raw);
  }
  if (raw && typeof raw === 'object') {
    return normalizeStringArray(raw.any_of || raw.checks || raw.patterns);
  }
  return [];
}

export {
  DEFAULT_POLICY_PATH,
  collectRequiredLabels,
  evaluateLabelRequirements,
  getGateCheckPatternsForLabel,
  getMinHumanApprovals,
  getOptionalGateLabels,
  isPolicyLabelRequirementEnabled,
  getRequiredChecks,
  getRiskLabels,
  inferRiskLevel,
  isPendingGateFailureEnabled,
  loadRiskPolicy,
  matchChangedFiles,
};
