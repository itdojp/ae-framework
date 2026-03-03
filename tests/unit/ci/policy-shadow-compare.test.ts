import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import {
  compareEvaluationSnapshots,
  runPolicyShadowComparison,
} from '../../../scripts/ci/policy-shadow-compare.mjs';

type CommandResult = {
  status?: number | null;
  stdout?: string;
  stderr?: string;
  error?: NodeJS.ErrnoException;
};

function writeJson(filePath: string, value: unknown): void {
  writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`);
}

function createSandbox() {
  const root = mkdtempSync(path.join(tmpdir(), 'ae-policy-shadow-'));
  const artifactsDir = path.join(root, 'artifacts', 'ci');
  const policyDir = path.join(root, 'policy');
  mkdirSync(artifactsDir, { recursive: true });
  mkdirSync(policyDir, { recursive: true });

  const inputPath = path.join(artifactsDir, 'policy-input-v1.json');
  const jsDecisionPath = path.join(artifactsDir, 'policy-decision-js-v1.json');
  const opaDecisionPath = path.join(artifactsDir, 'policy-decision-opa-v1.json');
  const reportPath = path.join(artifactsDir, 'policy-shadow-compare-v1.json');
  const regoPath = path.join(policyDir, 'risk-policy.rego');

  writeFileSync(regoPath, 'package ae.policy\nimport rego.v1\ndecision := {}\n');

  const input = {
    repository: 'itdojp/ae-framework',
    prNumber: 17,
  };
  const evaluation = {
    ok: true,
    errors: [],
    warnings: [],
    inferredRisk: {
      level: 'risk:low',
      labels: { low: 'risk:low', high: 'risk:high' },
      highRiskPathMatches: [],
      forceHighRiskTriggers: [],
    },
    selectedRiskLabel: 'risk:low',
    currentRiskLabels: ['risk:low'],
    reviewTopology: 'team',
    approvals: 0,
    minApprovals: 1,
    policyMinApprovals: 1,
    topologyMinApprovals: 1,
    effectiveMinApprovals: 1,
    minApprovalsSource: 'policy',
    requiredLabels: [],
    missingRequiredLabels: [],
    requiredCheckResults: [
      {
        checkName: 'verify-lite',
        result: {
          status: 'success',
          matches: [],
          reason: 'success',
        },
      },
    ],
    gateCheckResults: [],
  };

  writeJson(inputPath, input);
  writeJson(jsDecisionPath, {
    schemaVersion: '1.0.0',
    contractId: 'policy-decision.v1',
    generatedAtUtc: '2026-03-03T00:00:00.000Z',
    repository: input.repository,
    prNumber: input.prNumber,
    inputPath,
    engine: {
      kind: 'js',
      status: 'supported',
      version: 'node',
    },
    evaluation,
  });

  return {
    root,
    inputPath,
    jsDecisionPath,
    opaDecisionPath,
    reportPath,
    regoPath,
    evaluation,
  };
}

const cleanupTargets: string[] = [];

afterEach(() => {
  while (cleanupTargets.length > 0) {
    const target = cleanupTargets.pop();
    if (!target) continue;
    rmSync(target, { recursive: true, force: true });
  }
});

describe('policy-shadow-compare', () => {
  it('fails open with unsupported artifact when OPA is unavailable', async () => {
    const sandbox = createSandbox();
    cleanupTargets.push(sandbox.root);

    const commandRunner = (): CommandResult => ({
      status: null,
      stdout: '',
      stderr: '',
      error: Object.assign(new Error('not found'), { code: 'ENOENT' }),
    });

    const result = await runPolicyShadowComparison({
      inputPath: sandbox.inputPath,
      jsDecisionPath: sandbox.jsDecisionPath,
      opaDecisionPath: sandbox.opaDecisionPath,
      reportPath: sandbox.reportPath,
      regoPath: sandbox.regoPath,
      query: 'data.ae.policy.decision',
      opaBin: 'opa',
      strict: false,
    }, {
      commandRunner,
    });

    expect(result.exitCode).toBe(0);

    const report = JSON.parse(readFileSync(sandbox.reportPath, 'utf8'));
    expect(report.status).toBe('unsupported');
    expect(report.reason).toContain('opa command not found');

    const decision = JSON.parse(readFileSync(sandbox.opaDecisionPath, 'utf8'));
    expect(decision.engine.status).toBe('unsupported');
    expect(decision.evaluation).toBeNull();
    expect(decision.unsupportedReason).toContain('opa command not found');
  });

  it('compares JS and OPA evaluation snapshots in shadow mode', async () => {
    const sandbox = createSandbox();
    cleanupTargets.push(sandbox.root);

    const commandRunner = (_command: string, args: string[]): CommandResult => {
      if (args[0] === 'version') {
        return {
          status: 0,
          stdout: JSON.stringify({ version: '1.2.3' }),
          stderr: '',
        };
      }
      if (args[0] === 'eval') {
        return {
          status: 0,
          stdout: JSON.stringify({
            result: [
              {
                expressions: [
                  {
                    value: sandbox.evaluation,
                  },
                ],
              },
            ],
          }),
          stderr: '',
        };
      }
      return {
        status: 1,
        stdout: '',
        stderr: 'unexpected args',
      };
    };

    const result = await runPolicyShadowComparison({
      inputPath: sandbox.inputPath,
      jsDecisionPath: sandbox.jsDecisionPath,
      opaDecisionPath: sandbox.opaDecisionPath,
      reportPath: sandbox.reportPath,
      regoPath: sandbox.regoPath,
      query: 'data.ae.policy.decision',
      opaBin: 'opa',
      strict: false,
    }, {
      commandRunner,
    });

    expect(result.exitCode).toBe(0);

    const report = JSON.parse(readFileSync(sandbox.reportPath, 'utf8'));
    expect(report.status).toBe('match');
    expect(report.engine.status).toBe('supported');
    expect(report.engine.version).toBe('1.2.3');
    expect(report.comparison.match).toBe(true);
    expect(report.comparison.mismatches).toHaveLength(0);
  });

  it('returns non-zero in strict mode when mismatch exists', async () => {
    const sandbox = createSandbox();
    cleanupTargets.push(sandbox.root);

    const mismatchedEvaluation = {
      ...sandbox.evaluation,
      approvals: 2,
    };

    const commandRunner = (_command: string, args: string[]): CommandResult => {
      if (args[0] === 'version') {
        return {
          status: 0,
          stdout: JSON.stringify({ version: '1.2.3' }),
          stderr: '',
        };
      }
      if (args[0] === 'eval') {
        return {
          status: 0,
          stdout: JSON.stringify({
            result: [
              {
                expressions: [
                  {
                    value: mismatchedEvaluation,
                  },
                ],
              },
            ],
          }),
          stderr: '',
        };
      }
      return {
        status: 1,
        stdout: '',
        stderr: 'unexpected args',
      };
    };

    const result = await runPolicyShadowComparison({
      inputPath: sandbox.inputPath,
      jsDecisionPath: sandbox.jsDecisionPath,
      opaDecisionPath: sandbox.opaDecisionPath,
      reportPath: sandbox.reportPath,
      regoPath: sandbox.regoPath,
      query: 'data.ae.policy.decision',
      opaBin: 'opa',
      strict: true,
    }, {
      commandRunner,
    });

    expect(result.exitCode).toBe(1);

    const report = JSON.parse(readFileSync(sandbox.reportPath, 'utf8'));
    expect(report.status).toBe('mismatch');
    expect(report.comparison.match).toBe(false);
    expect(report.comparison.mismatches.some((item: { field: string }) => item.field === 'approvals')).toBe(true);
  });

  it('normalizes order before comparing snapshots', () => {
    const comparison = compareEvaluationSnapshots(
      {
        ok: true,
        errors: ['b', 'a'],
        warnings: ['z', 'y'],
        inferredRisk: { level: 'risk:low' },
        selectedRiskLabel: 'risk:low',
        currentRiskLabels: ['risk:low'],
        reviewTopology: 'team',
        approvals: 0,
        minApprovals: 1,
        effectiveMinApprovals: 1,
        minApprovalsSource: 'policy',
        requiredLabels: ['run-security', 'enforce-testing'],
        missingRequiredLabels: [],
        requiredCheckResults: [
          { checkName: 'verify-lite', result: { status: 'success' } },
        ],
        gateCheckResults: [
          { label: 'run-security', result: { status: 'pending' } },
        ],
      },
      {
        ok: true,
        errors: ['a', 'b'],
        warnings: ['y', 'z'],
        inferredRisk: { level: 'risk:low' },
        selectedRiskLabel: 'risk:low',
        currentRiskLabels: ['risk:low'],
        reviewTopology: 'team',
        approvals: 0,
        minApprovals: 1,
        effectiveMinApprovals: 1,
        minApprovalsSource: 'policy',
        requiredLabels: ['enforce-testing', 'run-security'],
        missingRequiredLabels: [],
        requiredCheckResults: [
          { checkName: 'verify-lite', result: { status: 'success' } },
        ],
        gateCheckResults: [
          { label: 'run-security', result: { status: 'pending' } },
        ],
      },
    );

    expect(comparison.match).toBe(true);
    expect(comparison.mismatches).toHaveLength(0);
  });
});
