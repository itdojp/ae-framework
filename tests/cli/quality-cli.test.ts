import { beforeAll, beforeEach, describe, expect, it, vi } from 'vitest';

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

beforeAll(async () => {
  ({ createQualityCommand } = await import('../../src/cli/quality-cli.js'));
});

beforeEach(() => {
  safeExitMock.mockReset();
  executeGatesMock.mockReset();
  executeFixesMock.mockReset();
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
});
