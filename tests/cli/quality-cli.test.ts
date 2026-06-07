import { mkdirSync, rmSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { afterEach, beforeAll, beforeEach, describe, expect, it, vi } from 'vitest';

const safeExitMock = vi.fn();
const executeGatesMock = vi.fn();
const executeFixesMock = vi.fn();

vi.mock('../../src/utils/safe-exit.js', () => ({
  safeExit: (...args: unknown[]) => safeExitMock(...args),
}));

vi.mock('../../src/quality/quality-gate-runner.js', () => ({
  QualityGateRunner: class {
    executeGates(...args: unknown[]) {
      return executeGatesMock(...args);
    }
  },
}));

vi.mock('../../src/cegis/auto-fix-engine.js', () => ({
  AutoFixEngine: class {
    executeFixes(...args: unknown[]) {
      return executeFixesMock(...args);
    }
  },
}));

let createQualityCommand: () => any;
let previousEnv: NodeJS.ProcessEnv;

beforeAll(async () => {
  ({ createQualityCommand } = await import('../../src/cli/quality-cli.js'));
});

beforeEach(() => {
  previousEnv = { ...process.env };
  process.env = {
    PATH: previousEnv['PATH'],
    HOME: previousEnv['HOME'],
    NODE_ENV: previousEnv['NODE_ENV'],
  };
  safeExitMock.mockReset();
  executeGatesMock.mockReset();
  executeFixesMock.mockReset();
});

afterEach(() => {
  process.env = previousEnv;
});

const createReport = (overrides: Partial<Record<string, unknown>> = {}) => ({
  timestamp: '2026-02-18T00:00:00.000Z',
  environment: 'development',
  overallScore: 100,
  totalGates: 1,
  passedGates: 1,
  failedGates: 0,
  results: [],
  summary: {
    byCategory: {},
    executionTime: 1000,
    blockers: [],
  },
  ...overrides,
});

const createBlockingReport = () => createReport({
  overallScore: 70,
  passedGates: 0,
  failedGates: 1,
  summary: {
    byCategory: {},
    executionTime: 1000,
    blockers: ['coverage'],
  },
});

const createLegacyFailure = (file: string) => ({
  id: '00000000-0000-4000-8000-000000000001',
  title: 'Type error',
  description: "Cannot find name 'missingValue'",
  severity: 'major',
  category: 'type_error',
  location: {
    file,
    line: 1,
    column: 1,
  },
  context: {
    environment: 'development',
    phase: 'code',
    timestamp: '2026-06-05T00:00:00.000Z',
    component: 'quality-reconcile-test',
  },
  evidence: {
    logs: [],
  },
  createdAt: '2026-06-05T00:00:00.000Z',
  updatedAt: '2026-06-05T00:00:00.000Z',
  tags: [],
  status: 'open',
  schemaVersion: '1.0.0',
});

const writeFailureInput = (testRoot: string, file: string): string => {
  const relativePath = path.posix.join(testRoot, 'failures.json');
  const absolutePath = path.join(process.cwd(), relativePath);
  mkdirSync(path.dirname(absolutePath), { recursive: true });
  writeFileSync(absolutePath, JSON.stringify([createLegacyFailure(file)], null, 2), 'utf8');
  return relativePath;
};

const findJsonPayload = (calls: Array<[unknown, ...unknown[]]>): Record<string, unknown> => {
  for (const call of calls) {
    const [first] = call;
    if (typeof first !== 'string') {
      continue;
    }
    const text = first.trim();
    if (!text.startsWith('{')) {
      continue;
    }
    try {
      return JSON.parse(text) as Record<string, unknown>;
    } catch {
      // continue
    }
  }
  throw new Error('JSON payload not found in console.log calls');
};

describe('quality CLI format option', () => {
  it('run --format json emits report JSON and passes silent/summary options to runner', async () => {
    executeGatesMock.mockResolvedValueOnce(createReport());
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});

    const command = createQualityCommand();
    await command.parseAsync(['node', 'cli', 'run', '--format', 'json', '--dry-run']);

    expect(executeGatesMock).toHaveBeenCalledWith(
      expect.objectContaining({
        dryRun: true,
        printSummary: false,
        silent: true,
      }),
    );
    const payload = findJsonPayload(consoleLogSpy.mock.calls as Array<[unknown, ...unknown[]]>);
    expect(payload['environment']).toBe('development');
    expect(payload['overallScore']).toBe(100);
    expect(safeExitMock).not.toHaveBeenCalled();
    consoleLogSpy.mockRestore();
  });

  it('run rejects unsupported --format with exit code 2', async () => {
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    const command = createQualityCommand();
    await command.parseAsync(['node', 'cli', 'run', '--format', 'xml']);

    expect(executeGatesMock).not.toHaveBeenCalled();
    expect(safeExitMock).toHaveBeenCalledWith(2);
    consoleErrorSpy.mockRestore();
  });

  it('run defaults agent-context execution to dry-run before delegating to the runner', async () => {
    const previous = process.env['AE_QUALITY_AGENT_CONTEXT'];
    process.env['AE_QUALITY_AGENT_CONTEXT'] = '1';
    executeGatesMock.mockResolvedValueOnce(createReport());
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});

    try {
      const command = createQualityCommand();
      await command.parseAsync(['node', 'cli', 'run', '--format', 'json']);

      expect(executeGatesMock).toHaveBeenCalledWith(
        expect.objectContaining({
          dryRun: true,
          apply: false,
        }),
      );
      expect(safeExitMock).not.toHaveBeenCalled();
    } finally {
      consoleLogSpy.mockRestore();
      if (previous === undefined) {
        delete process.env['AE_QUALITY_AGENT_CONTEXT'];
      } else {
        process.env['AE_QUALITY_AGENT_CONTEXT'] = previous;
      }
    }
  });

  it('run preserves CI execution for direct quality gates without explicit untrusted marker', async () => {
    process.env['GITHUB_ACTIONS'] = 'true';
    process.env['GITHUB_EVENT_NAME'] = 'pull_request';
    process.env['GITHUB_REF_PROTECTED'] = 'false';
    executeGatesMock.mockResolvedValueOnce(createReport());
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});

    try {
      const command = createQualityCommand();
      await command.parseAsync(['node', 'cli', 'run', '--format', 'json']);

      expect(executeGatesMock).toHaveBeenCalledWith(
        expect.objectContaining({
          dryRun: false,
          apply: true,
        }),
      );
      expect(safeExitMock).not.toHaveBeenCalled();
    } finally {
      consoleLogSpy.mockRestore();
    }
  });

  it('run rejects agent-context --apply without the trusted approval scope', async () => {
    const previous = process.env['AE_QUALITY_AGENT_CONTEXT'];
    process.env['AE_QUALITY_AGENT_CONTEXT'] = '1';
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    try {
      const command = createQualityCommand();
      await command.parseAsync(['node', 'cli', 'run', '--apply']);

      expect(executeGatesMock).not.toHaveBeenCalled();
      expect(safeExitMock).toHaveBeenCalledWith(1);
      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('approval-scope quality-gate-execution')
      );
    } finally {
      consoleErrorSpy.mockRestore();
      if (previous === undefined) {
        delete process.env['AE_QUALITY_AGENT_CONTEXT'];
      } else {
        process.env['AE_QUALITY_AGENT_CONTEXT'] = previous;
      }
    }
  });

  it('run forwards trusted agent-context approval for explicit apply', async () => {
    const previous = process.env['AE_QUALITY_AGENT_CONTEXT'];
    process.env['AE_QUALITY_AGENT_CONTEXT'] = '1';
    executeGatesMock.mockResolvedValueOnce(createReport());
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});

    try {
      const command = createQualityCommand();
      await command.parseAsync([
        'node',
        'cli',
        'run',
        '--format',
        'json',
        '--apply',
        '--approval-scope',
        'quality-gate-execution',
      ]);

      expect(executeGatesMock).toHaveBeenCalledWith(
        expect.objectContaining({
          dryRun: false,
          apply: true,
          approvalScope: 'quality-gate-execution',
        }),
      );
      expect(safeExitMock).not.toHaveBeenCalled();
    } finally {
      consoleLogSpy.mockRestore();
      if (previous === undefined) {
        delete process.env['AE_QUALITY_AGENT_CONTEXT'];
      } else {
        process.env['AE_QUALITY_AGENT_CONTEXT'] = previous;
      }
    }
  });

  it('reconcile --format json emits final report JSON and keeps blocker exit code', async () => {
    executeGatesMock.mockResolvedValueOnce(
      createReport({
        overallScore: 70,
        passedGates: 0,
        failedGates: 1,
        summary: {
          byCategory: {},
          executionTime: 1000,
          blockers: ['coverage'],
        },
      }),
    );
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});

    const command = createQualityCommand();
    await command.parseAsync([
      'node',
      'cli',
      'reconcile',
      '--format',
      'json',
      '--dry-run',
      '--max-rounds',
      '1',
    ]);

    expect(executeGatesMock).toHaveBeenCalledWith(
      expect.objectContaining({
        printSummary: false,
        silent: true,
      }),
    );
    const payload = findJsonPayload(consoleLogSpy.mock.calls as Array<[unknown, ...unknown[]]>);
    expect(payload['failedGates']).toBe(1);
    expect(safeExitMock).toHaveBeenCalledWith(1);
    consoleLogSpy.mockRestore();
  });

  it('reconcile defaults CI automation to dry-run and skips auto-fix without explicit apply', async () => {
    const previousCi = process.env['CI'];
    process.env['CI'] = 'true';
    executeGatesMock.mockResolvedValueOnce(createBlockingReport());
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});

    try {
      const command = createQualityCommand();
      await command.parseAsync([
        'node',
        'cli',
        'reconcile',
        '--format',
        'json',
        '--max-rounds',
        '2',
      ]);

      expect(executeGatesMock).toHaveBeenCalledWith(
        expect.objectContaining({
          dryRun: true,
          apply: false,
        }),
      );
      expect(executeFixesMock).not.toHaveBeenCalled();
      expect(safeExitMock).toHaveBeenCalledWith(1);
    } finally {
      consoleLogSpy.mockRestore();
      if (previousCi === undefined) {
        delete process.env['CI'];
      } else {
        process.env['CI'] = previousCi;
      }
    }
  });

  it('reconcile rejects CI --apply without trusted approval before running gates', async () => {
    const previousCi = process.env['CI'];
    process.env['CI'] = 'true';
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    try {
      const command = createQualityCommand();
      await command.parseAsync(['node', 'cli', 'reconcile', '--apply']);

      expect(executeGatesMock).not.toHaveBeenCalled();
      expect(executeFixesMock).not.toHaveBeenCalled();
      expect(safeExitMock).toHaveBeenCalledWith(1);
      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('agent or CI context')
      );
    } finally {
      consoleErrorSpy.mockRestore();
      if (previousCi === undefined) {
        delete process.env['CI'];
      } else {
        process.env['CI'] = previousCi;
      }
    }
  });

  it('reconcile rejects artifact-derived traversal paths before invoking auto-fix', async () => {
    const testRoot = ['artifacts', 'quality', `quality-cli-invalid-${Date.now()}-${Math.random().toString(16).slice(2)}`].join('/');
    const inputPath = writeFailureInput(testRoot, '../outside.ts');
    executeGatesMock.mockResolvedValueOnce(createBlockingReport());
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    try {
      const command = createQualityCommand();
      await command.parseAsync([
        'node',
        'cli',
        'reconcile',
        '--apply',
        '--approval-scope',
        'quality-gate-execution',
        '--max-rounds',
        '2',
        '--fix-input',
        inputPath,
        '--fix-output',
        path.posix.join(testRoot, 'auto-fix'),
      ]);

      expect(executeFixesMock).not.toHaveBeenCalled();
      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('Unable to load failure artifacts')
      );
      expect(consoleErrorSpy).toHaveBeenCalledWith(
        expect.stringContaining('dot-segment path components')
      );
      expect(safeExitMock).toHaveBeenCalledWith(1);
    } finally {
      consoleLogSpy.mockRestore();
      consoleErrorSpy.mockRestore();
      rmSync(path.join(process.cwd(), testRoot), { recursive: true, force: true });
    }
  });

  it('reconcile passes normalized workspace-relative artifact paths and workspace root to auto-fix', async () => {
    const testRoot = ['artifacts', 'quality', `quality-cli-valid-${Date.now()}-${Math.random().toString(16).slice(2)}`].join('/');
    const targetPath = 'src/cli/quality-cli.ts';
    const inputPath = writeFailureInput(testRoot, targetPath);
    executeGatesMock.mockResolvedValueOnce(createBlockingReport());
    executeFixesMock.mockResolvedValueOnce({
      appliedFixes: [],
      skippedFixes: [],
      summary: {
        totalFailures: 1,
        fixesApplied: 0,
        fixesSkipped: 0,
        filesModified: 0,
        success: true,
        errors: [],
        warnings: [],
      },
      recommendations: [],
      success: false,
      appliedActions: [],
      generatedFiles: [],
      backupFiles: [],
      errors: [],
    });
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});

    try {
      const command = createQualityCommand();
      await command.parseAsync([
        'node',
        'cli',
        'reconcile',
        '--apply',
        '--approval-scope',
        'quality-gate-execution',
        '--max-rounds',
        '2',
        '--fix-input',
        inputPath,
        '--fix-output',
        path.posix.join(testRoot, 'auto-fix'),
      ]);

      expect(executeFixesMock).toHaveBeenCalledTimes(1);
      const [failures, options] = executeFixesMock.mock.calls[0] as [Array<{ location?: { filePath?: string } }>, Record<string, unknown>];
      expect(failures[0]?.location?.filePath).toBe(targetPath);
      expect(options).toEqual(expect.objectContaining({
        outputDir: path.posix.join(testRoot, 'auto-fix'),
        workspaceRoot: process.cwd(),
      }));
    } finally {
      consoleLogSpy.mockRestore();
      rmSync(path.join(process.cwd(), testRoot), { recursive: true, force: true });
    }
  });
});
