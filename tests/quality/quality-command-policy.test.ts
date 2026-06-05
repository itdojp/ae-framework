import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { EventEmitter } from 'node:events';
import { mkdirSync, rmSync, existsSync, readFileSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawn } from 'node:child_process';
import { QualityPolicyLoader } from '../../src/quality/policy-loader.js';
import { QualityGateRunner } from '../../src/quality/quality-gate-runner.js';
import {
  QUALITY_GATE_EXECUTION_APPROVAL_SCOPE,
  resolveQualityReportOutputDir,
  resolveQualityWorkspacePath,
  createQualityPathContext,
  isQualityCiContext,
} from '../../src/quality/quality-command-policy.js';

class FakeChildProcess extends EventEmitter {
  stdout = new EventEmitter();
  stderr = new EventEmitter();
  kill = vi.fn();
}

const createPolicy = (
  command: string,
  securityCommand = 'pnpm audit --prod --json'
) => ({
  version: '1.0.0-test',
  lastUpdated: '2026-06-03T00:00:00Z',
  description: 'Quality command policy test fixture',
  environments: {
    development: {
      description: 'Development environment',
      enforcementLevel: 'warning' as const,
    },
    testing: {
      description: 'Testing environment',
      enforcementLevel: 'blocking' as const,
    },
  },
  qualityGates: {
    linting: {
      name: 'Code Linting',
      description: 'Code-owned lint gate',
      category: 'code-quality',
      enabled: true,
      thresholds: {
        development: {
          maxErrors: 0,
          maxWarnings: 0,
          blockOnFail: true,
        },
        testing: {
          maxErrors: 0,
          maxWarnings: 0,
          blockOnFail: true,
        },
      },
      tools: ['eslint'],
      commands: {
        test: command,
      },
    },
    security: {
      name: 'Security Vulnerabilities',
      description: 'Code-owned security gate',
      category: 'security',
      enabled: true,
      thresholds: {
        development: {
          maxCritical: 0,
          maxHigh: 0,
          maxMedium: 0,
          blockOnFail: true,
        },
        testing: {
          maxCritical: 0,
          maxHigh: 0,
          maxMedium: 0,
          blockOnFail: true,
        },
      },
      tools: ['pnpm audit'],
      commands: {
        test: securityCommand,
      },
    },
  },
  compositeGates: {},
  integrations: {
    ci: {
      githubActions: {
        enabled: true,
        workflow: '.github/workflows/quality.yml',
        triggerOn: ['pull_request'],
        parallelExecution: true,
      },
      preCommitHooks: {
        enabled: false,
        hooks: [],
        blocking: false,
      },
    },
    monitoring: {
      opentelemetry: {
        enabled: false,
        metricsPrefix: 'quality',
        tracingEnabled: false,
      },
      dashboards: {},
    },
  },
  notifications: {},
  reporting: {
    formats: ['json'],
    outputDirectory: 'artifacts/quality/reports',
    retention: {
      days: 30,
      maxReports: 100,
    },
    aggregation: {
      enabled: false,
      interval: 'daily',
      metrics: ['pass_rate'],
    },
  },
});

describe('quality gate command policy', () => {
  let testRoot: string;
  let policyPath: string;
  let previousQualityAgentContext: string | undefined;
  let previousAgentContext: string | undefined;
  let previousCiContext: string | undefined;

  const writePolicy = (
    command = 'node scripts/quality/check-lint-summary.mjs',
    securityCommand = 'pnpm audit --prod --json'
  ) => {
    policyPath = join(process.cwd(), testRoot, 'quality-policy.json');
    mkdirSync(join(process.cwd(), testRoot), { recursive: true });
    const policy = createPolicy(command, securityCommand);
    rmSync(policyPath, { force: true });
    writeFileSync(policyPath, JSON.stringify(policy, null, 2), 'utf8');
    return new QualityPolicyLoader(policyPath);
  };

  const createSpawnMock = () => vi.fn((_command: string, _args?: readonly string[]) => {
    const child = new FakeChildProcess();
    queueMicrotask(() => {
      child.stdout.emit('data', '0 error\n0 warning\n');
      child.emit('close', 0);
    });
    return child;
  });

  beforeEach(() => {
    testRoot = ['artifacts', 'quality', `unit-${Date.now()}-${Math.random().toString(16).slice(2)}`].join('/');
    previousQualityAgentContext = process.env['AE_QUALITY_AGENT_CONTEXT'];
    previousAgentContext = process.env['AE_AGENT_CONTEXT'];
    previousCiContext = process.env['CI'];
    delete process.env['AE_QUALITY_AGENT_CONTEXT'];
    delete process.env['AE_AGENT_CONTEXT'];
    delete process.env['CI'];
  });

  afterEach(() => {
    if (previousQualityAgentContext === undefined) {
      delete process.env['AE_QUALITY_AGENT_CONTEXT'];
    } else {
      process.env['AE_QUALITY_AGENT_CONTEXT'] = previousQualityAgentContext;
    }
    if (previousAgentContext === undefined) {
      delete process.env['AE_AGENT_CONTEXT'];
    } else {
      process.env['AE_AGENT_CONTEXT'] = previousAgentContext;
    }
    if (previousCiContext === undefined) {
      delete process.env['CI'];
    } else {
      process.env['CI'] = previousCiContext;
    }
    rmSync(join(process.cwd(), testRoot), { recursive: true, force: true });
  });

  it('executes the code-owned argv for an allowlisted gate without shell mode', async () => {
    const spawnMock = createSpawnMock();
    const runner = new QualityGateRunner(writePolicy(), {
      spawnProcess: spawnMock as unknown as typeof spawn,
    });

    const report = await runner.executeGates({
      environment: 'testing',
      gates: ['linting'],
      parallel: false,
      outputDir: `${testRoot}/reports`,
      noHistory: true,
      printSummary: false,
      silent: true,
    });

    expect(report.failedGates).toBe(0);
    expect(spawnMock).toHaveBeenCalledWith(
      'node',
      ['scripts/quality/check-lint-summary.mjs'],
      expect.objectContaining({ shell: false })
    );
    expect(existsSync(join(process.cwd(), testRoot, 'reports', 'quality-report-testing-latest.json'))).toBe(true);
  });

  it('rejects untrusted repository policy command text before spawning a process', async () => {
    const spawnMock = createSpawnMock();
    const runner = new QualityGateRunner(writePolicy('node -e "console.log(process.env)"'), {
      spawnProcess: spawnMock as unknown as typeof spawn,
    });
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    try {
      await expect(runner.executeGates({
        environment: 'testing',
        gates: ['linting'],
        parallel: false,
        outputDir: `${testRoot}/reports`,
        printSummary: false,
        silent: true,
      })).rejects.toThrow('policy command is not trusted');
      expect(spawnMock).not.toHaveBeenCalled();
    } finally {
      consoleErrorSpy.mockRestore();
    }
  });

  it('preflights all selected gate commands before spawning earlier gates', async () => {
    const spawnMock = createSpawnMock();
    const runner = new QualityGateRunner(
      writePolicy('node scripts/quality/check-lint-summary.mjs', 'node -e "console.log(process.env)"'),
      {
        spawnProcess: spawnMock as unknown as typeof spawn,
      }
    );
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    try {
      await expect(runner.executeGates({
        environment: 'testing',
        gates: ['linting', 'security'],
        parallel: false,
        outputDir: `${testRoot}/reports`,
        printSummary: false,
        silent: true,
      })).rejects.toThrow('policy command is not trusted');
      expect(spawnMock).not.toHaveBeenCalled();
    } finally {
      consoleErrorSpy.mockRestore();
    }
  });

  it('defaults agent contexts to dry-run and avoids process and report writes', async () => {
    process.env['AE_QUALITY_AGENT_CONTEXT'] = '1';
    const spawnMock = createSpawnMock();
    const runner = new QualityGateRunner(writePolicy(), {
      spawnProcess: spawnMock as unknown as typeof spawn,
    });

    const report = await runner.executeGates({
      environment: 'testing',
      gates: ['linting'],
      parallel: false,
      outputDir: `${testRoot}/reports`,
      printSummary: false,
      silent: true,
    });

    expect(spawnMock).not.toHaveBeenCalled();
    expect(report.results[0]?.details).toMatchObject({
      dryRun: true,
      command: 'node scripts/quality/check-lint-summary.mjs',
    });
    expect(existsSync(join(process.cwd(), testRoot, 'reports', 'quality-report-testing-latest.json'))).toBe(false);
  });

  it('requires trusted approval before agent-context apply can execute', async () => {
    process.env['AE_QUALITY_AGENT_CONTEXT'] = '1';
    const spawnMock = createSpawnMock();
    const runner = new QualityGateRunner(writePolicy(), {
      spawnProcess: spawnMock as unknown as typeof spawn,
    });

    await expect(runner.executeGates({
      environment: 'testing',
      gates: ['linting'],
      apply: true,
      outputDir: `${testRoot}/reports`,
      printSummary: false,
      silent: true,
    })).rejects.toThrow(`approval scope '${QUALITY_GATE_EXECUTION_APPROVAL_SCOPE}'`);
    expect(spawnMock).not.toHaveBeenCalled();
  });

  it('executes in agent context when apply uses the trusted approval scope', async () => {
    process.env['AE_QUALITY_AGENT_CONTEXT'] = '1';
    const spawnMock = createSpawnMock();
    const runner = new QualityGateRunner(writePolicy(), {
      spawnProcess: spawnMock as unknown as typeof spawn,
    });

    const report = await runner.executeGates({
      environment: 'testing',
      gates: ['linting'],
      apply: true,
      approvalScope: QUALITY_GATE_EXECUTION_APPROVAL_SCOPE,
      outputDir: `${testRoot}/reports`,
      noHistory: true,
      printSummary: false,
      silent: true,
    });

    expect(report.failedGates).toBe(0);
    expect(spawnMock).toHaveBeenCalledTimes(1);
    const latest = readFileSync(join(process.cwd(), testRoot, 'reports', 'quality-report-testing-latest.json'), 'utf8');
    expect(JSON.parse(latest).environment).toBe('testing');
  });

  it('constrains quality report output to the approved artifact root', () => {
    const context = createQualityPathContext();
    expect(() => resolveQualityReportOutputDir('reports/quality-gates', context)).toThrow(
      'approved quality artifact root'
    );
    expect(() => resolveQualityReportOutputDir('/tmp/quality-gates', context)).toThrow(
      'relative to the approved quality artifact root'
    );
  });

  it('constrains quality workspace paths to relative non-traversing paths', () => {
    const context = createQualityPathContext();

    expect(resolveQualityWorkspacePath('src/index.ts', context, 'auto-fix target')).toMatchObject({
      workspaceRelativePath: 'src/index.ts',
    });
    expect(() => resolveQualityWorkspacePath('/tmp/outside.ts', context, 'auto-fix target')).toThrow(
      'relative to the approved workspace'
    );
    expect(() => resolveQualityWorkspacePath('../outside.ts', context, 'auto-fix target')).toThrow(
      'dot-segment path components'
    );
    expect(() => resolveQualityWorkspacePath('.git/config', context, 'auto-fix target')).toThrow(
      'Git metadata'
    );
  });

  it('rejects quality workspace paths that escape through symlinks', () => {
    const root = join(process.cwd(), testRoot, 'workspace');
    const outside = join(process.cwd(), testRoot, 'outside');
    mkdirSync(root, { recursive: true });
    mkdirSync(outside, { recursive: true });
    try {
      symlinkSync(outside, join(root, 'escape'), 'dir');
    } catch {
      return;
    }

    const context = createQualityPathContext({ workspaceRoot: root });

    expect(() => resolveQualityWorkspacePath('escape/file.ts', context, 'auto-fix target')).toThrow(
      'outside the approved workspace'
    );
  });

  it('detects CI automation context without changing agent-context detection', () => {
    expect(isQualityCiContext()).toBe(false);
    process.env['CI'] = 'true';
    expect(isQualityCiContext()).toBe(true);
  });
});
