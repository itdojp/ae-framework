import { describe, expect, it } from 'vitest';
import {
  createHighImpactChildEnv,
  evaluateHighImpactActionPolicy,
  findAmbientSecretNames,
  formatHighImpactDecisionMessage,
  isHighImpactUntrustedCheckout,
  type HighImpactActionKind,
} from '../../../src/utils/high-impact-action-policy.js';

describe('high-impact action approval policy', () => {
  it('TGT-020-F001: forces package-manager execution in untrusted checkouts to dry-run even with approval', () => {
    const decision = evaluateHighImpactActionPolicy({
      actionKind: 'package-manager',
      actionName: 'npm test --silent',
      apply: true,
      approvalScope: 'guard-script-execution',
      requiredApprovalScope: 'guard-script-execution',
      env: { AE_UNTRUSTED_CHECKOUT: '1' },
    });

    expect(decision).toMatchObject({
      allowed: false,
      dryRun: true,
      approvalRequired: false,
      reason: 'untrusted-workspace-or-ref-forces-dry-run',
      untrustedCheckout: true,
    });
  });

  it('TGT-AGENT-025-F001: defaults agent-context high-impact actions to plan-only dry-run without apply', () => {
    const decision = evaluateHighImpactActionPolicy({
      actionKind: 'process',
      actionName: 'agent spawned verifier',
      env: { AE_AGENT_CONTEXT: '1' },
    });

    expect(decision).toMatchObject({
      allowed: false,
      dryRun: true,
      reason: 'plan-only-without-explicit-apply',
      agentContext: true,
    });
  });

  it('requires explicit approval before npm/cargo/docker/GitHub write/auto-fix actions are allowed', () => {
    const cases: Array<{ kind: HighImpactActionKind; name: string }> = [
      { kind: 'package-manager', name: 'npm install' },
      { kind: 'package-manager', name: 'cargo test' },
      { kind: 'container', name: 'docker run' },
      { kind: 'github-write', name: 'gh api --method POST repos/o/r/issues/1/comments' },
      { kind: 'auto-fix', name: 'fix apply' },
    ];

    for (const { kind, name } of cases) {
      const decision = evaluateHighImpactActionPolicy({
        actionKind: kind,
        actionName: name,
        apply: true,
        env: {},
      });
      expect(decision.allowed, name).toBe(false);
      expect(decision.approvalRequired, name).toBe(true);
      expect(decision.reason, name).toContain('missing-explicit-approval');
    }
  });

  it('allows trusted execution only when the required approval scope matches', () => {
    const decision = evaluateHighImpactActionPolicy({
      actionKind: 'auto-fix',
      actionName: 'cegis-auto-fix-apply',
      apply: true,
      approvalScope: 'cegis-auto-fix',
      requiredApprovalScope: 'cegis-auto-fix',
      env: {},
    });

    expect(decision).toMatchObject({
      allowed: true,
      dryRun: false,
      approvalRequired: false,
      reason: 'approved-trusted-execution',
    });
  });

  it('records trusted local compatibility when approval enforcement is intentionally disabled', () => {
    const decision = evaluateHighImpactActionPolicy({
      actionKind: 'package-manager',
      actionName: 'trusted-local-quality-gate',
      apply: true,
      enforceApproval: false,
      env: {},
    });

    expect(decision).toMatchObject({
      allowed: true,
      dryRun: false,
      approvalRequired: false,
      reason: 'trusted-execution-without-enforced-approval',
    });
  });

  it('TGT-AGENT-041-F001: treats unprotected pull_request refs as untrusted for GitHub write actions', () => {
    const env = {
      GITHUB_ACTIONS: 'true',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_REF_PROTECTED: 'false',
    };
    expect(isHighImpactUntrustedCheckout(env)).toBe(true);

    const decision = evaluateHighImpactActionPolicy({
      actionKind: 'github-write',
      actionName: 'gh pr merge --auto',
      apply: true,
      approvalScope: 'github-write',
      requiredApprovalScope: 'github-write',
      env,
    });

    expect(decision).toMatchObject({
      allowed: false,
      dryRun: true,
      reason: 'untrusted-workspace-or-ref-forces-dry-run',
    });
  });

  it('blocks approved agent-context execution when ambient secrets are present and redacts child environments', () => {
    const env = {
      PATH: '/usr/bin',
      HOME: '/home/operator',
      GITHUB_TOKEN: 'ghs-secret-value',
      NPM_TOKEN: 'npm-secret-value',
      CUSTOM_API_KEY: 'api-secret-value',
    };

    expect(findAmbientSecretNames(env)).toEqual(['CUSTOM_API_KEY', 'GITHUB_TOKEN', 'NPM_TOKEN']);

    const decision = evaluateHighImpactActionPolicy({
      actionKind: 'process',
      actionName: 'agent verifier process',
      apply: true,
      approvalScope: 'high-impact:process',
      env,
      agentContext: true,
    });

    expect(decision).toMatchObject({
      allowed: false,
      blocked: true,
      dryRun: true,
      reason: 'ambient-secrets-present',
    });
    expect(formatHighImpactDecisionMessage(decision)).not.toContain('ghs-secret-value');
    expect(createHighImpactChildEnv(env)).toEqual({ PATH: '/usr/bin', HOME: '/home/operator' });
  });

  it('TGT-AGENT-233-F001: codegen materialization can be explicitly approved on a trusted workspace/ref', () => {
    const decision = evaluateHighImpactActionPolicy({
      actionKind: 'codegen-materialize',
      actionName: 'spec codegen materialize',
      apply: true,
      approval: {
        approved: true,
        scope: 'spec-codegen-materialize',
      },
      requiredApprovalScope: 'spec-codegen-materialize',
      env: {},
    });

    expect(decision.allowed).toBe(true);
    expect(decision.dryRun).toBe(false);
  });
});
