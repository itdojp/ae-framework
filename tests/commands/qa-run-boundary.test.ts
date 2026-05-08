import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';

const { execaMock, loadConfigWithSourceMock, getThresholdMock, readFileMock, statMock } = vi.hoisted(() => ({
  execaMock: vi.fn(),
  loadConfigWithSourceMock: vi.fn(),
  getThresholdMock: vi.fn(),
  readFileMock: vi.fn(),
  statMock: vi.fn(),
}));

vi.mock('execa', () => ({
  execa: execaMock,
}));

vi.mock('../../src/core/config.js', () => ({
  loadConfigWithSource: loadConfigWithSourceMock,
}));

vi.mock('../../src/utils/quality-policy-loader.js', () => ({
  getThreshold: getThresholdMock,
}));

vi.mock('node:fs/promises', () => ({
  readFile: readFileMock,
  stat: statMock,
}));

import { qaRun } from '../../src/commands/qa/run.js';

const originalEnv = { ...process.env };
let packageJson: Record<string, unknown>;

function basePackageJson(overrides: Record<string, unknown> = {}): Record<string, unknown> {
  return {
    name: 'qa-run-fixture',
    private: true,
    scripts: {
      test: 'vitest run',
      'test:fast': 'vitest run tests/unit',
    },
    devDependencies: {
      vitest: '^2.1.9',
    },
    ...overrides,
  };
}

beforeEach(() => {
  execaMock.mockReset();
  loadConfigWithSourceMock.mockReset();
  getThresholdMock.mockReset();
  readFileMock.mockReset();
  statMock.mockReset();
  process.env = { ...originalEnv };
  delete process.env['CI'];
  delete process.env['AE_QA_LIGHT'];
  delete process.env['AE_QUALITY_PROFILE'];
  packageJson = basePackageJson();
  loadConfigWithSourceMock.mockResolvedValue({
    config: {
      qa: {
        coverageThreshold: {
          branches: 70,
          lines: 80,
          functions: 80,
          statements: 80,
        },
      },
    },
    source: { path: null, raw: {} },
  });
  getThresholdMock.mockReturnValue(null);
  execaMock.mockResolvedValue({ exitCode: 0, stdout: '' });
  statMock.mockImplementation(async (filePath: string) => {
    if (filePath === 'pnpm-lock.yaml') {
      return {};
    }
    throw new Error(`missing: ${filePath}`);
  });
  readFileMock.mockImplementation(async (filePath: string) => {
    if (filePath === 'package.json') {
      return `${JSON.stringify(packageJson, null, 2)}\n`;
    }
    throw new Error(`missing: ${filePath}`);
  });
});

afterEach(() => {
  process.env = { ...originalEnv };
});

describe('qaRun command boundary', () => {
  it('routes vitest light mode through the package-manager fast script', async () => {
    process.env['AE_QA_LIGHT'] = '1';

    await qaRun();

    expect(execaMock).toHaveBeenCalledWith('pnpm', ['run', 'test:fast'], { stdio: 'inherit' });
  });

  it('routes CI mode through the fast script even when light option is omitted', async () => {
    process.env['CI'] = 'true';

    await qaRun();

    expect(execaMock).toHaveBeenCalledWith('pnpm', ['run', 'test:fast'], { stdio: 'inherit' });
  });

  it('routes jest full mode with policy coverage thresholds when available', async () => {
    packageJson = basePackageJson({
      scripts: {
        test: 'jest',
      },
      devDependencies: {
        jest: '^29.7.0',
      },
    });
    getThresholdMock.mockImplementation((_gate: string, metric: string) => ({
      branches: 61,
      lines: 62,
      functions: 63,
      statements: 64,
    }[metric]));

    await qaRun({ light: false });

    expect(execaMock).toHaveBeenCalledWith('pnpm', [
      'run',
      'test',
      '--',
      '--coverage',
      '--coverageThreshold={"global":{"lines":62,"functions":63,"branches":61,"statements":64}}',
    ], { stdio: 'inherit' });
  });

  it('propagates runner failures as command boundary errors', async () => {
    execaMock.mockRejectedValueOnce(new Error('test command failed'));

    await expect(qaRun({ light: true })).rejects.toThrow('test command failed');
  });
});
