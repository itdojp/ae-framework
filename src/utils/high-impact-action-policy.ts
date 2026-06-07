export type HighImpactActionKind =
  | 'process'
  | 'package-manager'
  | 'container'
  | 'filesystem-write'
  | 'github-write'
  | 'auto-fix'
  | 'codegen-materialize';

export interface HighImpactActionApproval {
  approved?: boolean | undefined;
  scope?: string | undefined;
  approvedBy?: string | undefined;
  reason?: string | undefined;
}

export interface HighImpactActionPolicyInput {
  actionKind: HighImpactActionKind;
  actionName: string;
  apply?: boolean | undefined;
  dryRun?: boolean | undefined;
  approvalScope?: string | undefined;
  requiredApprovalScope?: string | undefined;
  approval?: HighImpactActionApproval | undefined;
  env?: NodeJS.ProcessEnv | undefined;
  agentContext?: boolean | undefined;
  ciContext?: boolean | undefined;
  untrustedCheckout?: boolean | undefined;
  trustedWorkspace?: boolean | undefined;
  trustedRef?: boolean | undefined;
  blockAmbientSecrets?: boolean | undefined;
  allowAmbientSecrets?: boolean | undefined;
  enforceApproval?: boolean | undefined;
}

export interface HighImpactActionPolicyDecision {
  actionKind: HighImpactActionKind;
  actionName: string;
  apply: boolean;
  dryRun: boolean;
  allowed: boolean;
  approvalRequired: boolean;
  blocked: boolean;
  reason: string;
  requiredApprovalScope: string;
  approvalScope?: string | undefined;
  trustedWorkspace: boolean;
  trustedRef: boolean;
  agentContext: boolean;
  ciContext: boolean;
  untrustedCheckout: boolean;
  ambientSecretNames: string[];
}

export const DEFAULT_HIGH_IMPACT_APPROVAL_SCOPES: Readonly<Record<HighImpactActionKind, string>> = {
  process: 'high-impact:process',
  'package-manager': 'high-impact:package-manager',
  container: 'high-impact:container',
  'filesystem-write': 'high-impact:filesystem-write',
  'github-write': 'high-impact:github-write',
  'auto-fix': 'high-impact:auto-fix',
  'codegen-materialize': 'high-impact:codegen-materialize',
};

const SECRET_ENV_NAME_PATTERN = /(?:^|_)(?:token|secret|password|passwd|credential|credentials|cookie|session|authorization|auth|private(?:_key)?|access_key|api_key)(?:_|$)/i;
const SECRET_ENV_EXACT_NAMES = new Set([
  'ACTIONS_ID_TOKEN_REQUEST_TOKEN',
  'GH_TOKEN',
  'GITHUB_TOKEN',
  'NODE_AUTH_TOKEN',
  'NPM_TOKEN',
]);

const isTruthyEnvValue = (value: string | undefined): boolean => {
  if (value === undefined) return false;
  const normalized = value.trim().toLowerCase();
  return normalized.length > 0 && !['0', 'false', 'no', 'off'].includes(normalized);
};

const isPullRequestEvent = (env: NodeJS.ProcessEnv): boolean => {
  const eventName = env['GITHUB_EVENT_NAME'];
  return eventName === 'pull_request' || eventName === 'pull_request_target';
};

export function isHighImpactAgentContext(env: NodeJS.ProcessEnv = process.env): boolean {
  return isTruthyEnvValue(env['AE_AGENT_CONTEXT'])
    || isTruthyEnvValue(env['CODEX_AGENT_CONTEXT'])
    || isTruthyEnvValue(env['AE_QUALITY_AGENT_CONTEXT'])
    || isTruthyEnvValue(env['AE_GUARD_AGENT_CONTEXT'])
    || isTruthyEnvValue(env['AE_MCP_AGENT_CONTEXT'])
    || isTruthyEnvValue(env['AE_CODEX_AGENT_CONTEXT']);
}

export function isHighImpactCiContext(env: NodeJS.ProcessEnv = process.env): boolean {
  return isTruthyEnvValue(env['CI']) || isTruthyEnvValue(env['GITHUB_ACTIONS']);
}

export function isHighImpactUntrustedCheckout(env: NodeJS.ProcessEnv = process.env): boolean {
  return isTruthyEnvValue(env['AE_UNTRUSTED_CHECKOUT'])
    || isTruthyEnvValue(env['AE_GUARD_UNTRUSTED_CHECKOUT'])
    || isTruthyEnvValue(env['AE_CI_UNTRUSTED_CHECKOUT'])
    || (isPullRequestEvent(env) && env['GITHUB_REF_PROTECTED'] !== 'true');
}

export function findAmbientSecretNames(env: NodeJS.ProcessEnv = process.env): string[] {
  const names: string[] = [];
  for (const [name, value] of Object.entries(env)) {
    if (value === undefined || value.length === 0) continue;
    if (SECRET_ENV_EXACT_NAMES.has(name) || SECRET_ENV_NAME_PATTERN.test(name)) {
      names.push(name);
    }
  }
  return names.sort();
}

export function createHighImpactChildEnv(source: NodeJS.ProcessEnv = process.env): NodeJS.ProcessEnv {
  const env: NodeJS.ProcessEnv = {};
  for (const [name, value] of Object.entries(source)) {
    if (value === undefined) continue;
    if (SECRET_ENV_EXACT_NAMES.has(name) || SECRET_ENV_NAME_PATTERN.test(name)) {
      continue;
    }
    env[name] = value;
  }
  return env;
}

const getEffectiveApprovalScope = (input: HighImpactActionPolicyInput): string | undefined => {
  if (input.approvalScope !== undefined) {
    return input.approvalScope;
  }
  return input.approval?.scope;
};

const hasExplicitApproval = (
  input: HighImpactActionPolicyInput,
  requiredApprovalScope: string,
): boolean => {
  if (input.approval !== undefined) {
    return input.approval.approved === true && input.approval.scope === requiredApprovalScope;
  }
  return input.approvalScope === requiredApprovalScope;
};

const inferTrustedWorkspace = (
  input: HighImpactActionPolicyInput,
  env: NodeJS.ProcessEnv,
  untrustedCheckout: boolean,
): boolean => {
  if (input.trustedWorkspace !== undefined) {
    return input.trustedWorkspace;
  }
  if (untrustedCheckout) {
    return false;
  }
  if (isTruthyEnvValue(env['AE_TRUSTED_WORKSPACE']) || isTruthyEnvValue(env['AE_HIGH_IMPACT_TRUSTED_WORKSPACE'])) {
    return true;
  }
  return true;
};

const inferTrustedRef = (
  input: HighImpactActionPolicyInput,
  env: NodeJS.ProcessEnv,
  untrustedCheckout: boolean,
): boolean => {
  if (input.trustedRef !== undefined) {
    return input.trustedRef;
  }
  if (untrustedCheckout) {
    return false;
  }
  if (isTruthyEnvValue(env['AE_TRUSTED_REF']) || isTruthyEnvValue(env['AE_HIGH_IMPACT_TRUSTED_REF'])) {
    return true;
  }
  if (isTruthyEnvValue(env['GITHUB_ACTIONS'])) {
    return env['GITHUB_REF_PROTECTED'] === 'true' && !isPullRequestEvent(env);
  }
  return true;
};

const buildDecision = (
  input: HighImpactActionPolicyInput,
  values: Omit<HighImpactActionPolicyDecision, 'actionKind' | 'actionName' | 'requiredApprovalScope'> & { requiredApprovalScope: string },
): HighImpactActionPolicyDecision => {
  const decision: HighImpactActionPolicyDecision = {
    actionKind: input.actionKind,
    actionName: input.actionName,
    apply: values.apply,
    dryRun: values.dryRun,
    allowed: values.allowed,
    approvalRequired: values.approvalRequired,
    blocked: values.blocked,
    reason: values.reason,
    requiredApprovalScope: values.requiredApprovalScope,
    trustedWorkspace: values.trustedWorkspace,
    trustedRef: values.trustedRef,
    agentContext: values.agentContext,
    ciContext: values.ciContext,
    untrustedCheckout: values.untrustedCheckout,
    ambientSecretNames: values.ambientSecretNames,
  };
  if (values.approvalScope !== undefined) {
    decision.approvalScope = values.approvalScope;
  }
  return decision;
};

export function evaluateHighImpactActionPolicy(input: HighImpactActionPolicyInput): HighImpactActionPolicyDecision {
  const env = input.env ?? process.env;
  const requiredApprovalScope = input.requiredApprovalScope ?? DEFAULT_HIGH_IMPACT_APPROVAL_SCOPES[input.actionKind];
  const approvalScope = getEffectiveApprovalScope(input);
  const apply = input.apply === true;
  const explicitDryRun = input.dryRun === true;
  const agentContext = input.agentContext ?? isHighImpactAgentContext(env);
  const ciContext = input.ciContext ?? isHighImpactCiContext(env);
  const untrustedCheckout = input.untrustedCheckout ?? isHighImpactUntrustedCheckout(env);
  const trustedWorkspace = inferTrustedWorkspace(input, env, untrustedCheckout);
  const trustedRef = inferTrustedRef(input, env, untrustedCheckout);
  const ambientSecretNames = findAmbientSecretNames(env);
  const shouldBlockAmbientSecrets = input.blockAmbientSecrets ?? (agentContext || ciContext || untrustedCheckout);
  const enforceApproval = input.enforceApproval ?? true;
  const approved = hasExplicitApproval(input, requiredApprovalScope);

  const common = {
    apply,
    requiredApprovalScope,
    approvalScope,
    trustedWorkspace,
    trustedRef,
    agentContext,
    ciContext,
    untrustedCheckout,
    ambientSecretNames,
  };

  if (explicitDryRun) {
    return buildDecision(input, {
      ...common,
      dryRun: true,
      allowed: false,
      approvalRequired: false,
      blocked: false,
      reason: 'explicit-dry-run',
    });
  }

  if (!apply) {
    return buildDecision(input, {
      ...common,
      dryRun: true,
      allowed: false,
      approvalRequired: false,
      blocked: false,
      reason: 'plan-only-without-explicit-apply',
    });
  }

  if (untrustedCheckout || !trustedWorkspace || !trustedRef) {
    return buildDecision(input, {
      ...common,
      dryRun: true,
      allowed: false,
      approvalRequired: false,
      blocked: false,
      reason: 'untrusted-workspace-or-ref-forces-dry-run',
    });
  }

  if (enforceApproval && !approved) {
    return buildDecision(input, {
      ...common,
      dryRun: false,
      allowed: false,
      approvalRequired: true,
      blocked: false,
      reason: `missing-explicit-approval:${requiredApprovalScope}`,
    });
  }

  if (shouldBlockAmbientSecrets && input.allowAmbientSecrets !== true && ambientSecretNames.length > 0) {
    return buildDecision(input, {
      ...common,
      dryRun: true,
      allowed: false,
      approvalRequired: false,
      blocked: true,
      reason: 'ambient-secrets-present',
    });
  }

  return buildDecision(input, {
    ...common,
    dryRun: false,
    allowed: true,
    approvalRequired: false,
    blocked: false,
    reason: approved ? 'approved-trusted-execution' : 'trusted-execution-without-enforced-approval',
  });
}

export function formatHighImpactDecisionMessage(decision: HighImpactActionPolicyDecision): string {
  switch (decision.reason) {
    case 'explicit-dry-run':
      return `${decision.actionName} is in explicit dry-run mode; ${decision.actionKind} action will not execute.`;
    case 'plan-only-without-explicit-apply':
      return `${decision.actionName} defaults to dry-run; rerun with explicit apply and approval scope '${decision.requiredApprovalScope}' to execute ${decision.actionKind} action.`;
    case 'untrusted-workspace-or-ref-forces-dry-run':
      return `${decision.actionName} is running from an untrusted workspace/ref; ${decision.actionKind} action is forced to dry-run.`;
    case 'ambient-secrets-present':
      return `${decision.actionName} cannot execute ${decision.actionKind} action while ambient secrets are present: ${decision.ambientSecretNames.join(', ')}`;
    default:
      if (decision.approvalRequired) {
        return `${decision.actionName} requires explicit approval scope '${decision.requiredApprovalScope}' before executing ${decision.actionKind} action.`;
      }
      return `${decision.actionName} ${decision.reason}`;
  }
}
