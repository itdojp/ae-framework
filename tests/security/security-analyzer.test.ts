import { beforeEach, describe, expect, it, vi } from 'vitest';

const execFileSyncMock = vi.fn();
const spawnMock = vi.fn();

vi.mock('node:child_process', () => ({
  execFileSync: (...args) => execFileSyncMock(...args),
  spawn: (...args) => spawnMock(...args),
}));

describe('SecurityAnalyzer.runSecretsScanning', () => {
  beforeEach(() => {
    execFileSyncMock.mockReset();
    spawnMock.mockReset();
  });

  it('downgrades missing gitleaks executable to warning', async () => {
    const { SecurityAnalyzer } = await import('../../scripts/security-analyzer.js');
    const analyzer = new SecurityAnalyzer();
    analyzer.scanForPatterns = vi.fn().mockResolvedValue([]);
    execFileSyncMock.mockImplementationOnce(() => {
      const error = new Error('spawn gitleaks ENOENT');
      error.code = 'ENOENT';
      throw error;
    });

    await expect(analyzer.runSecretsScanning()).resolves.toEqual({
      status: 'warning',
      tool: 'gitleaks',
      details: ['Gitleaks executable is not available in this environment'],
    });
  });

  it('keeps real gitleaks findings as failed', async () => {
    const { SecurityAnalyzer } = await import('../../scripts/security-analyzer.js');
    const analyzer = new SecurityAnalyzer();
    analyzer.scanForPatterns = vi.fn().mockResolvedValue([]);
    execFileSyncMock.mockImplementationOnce(() => {
      const error = new Error('gitleaks detected leaks');
      error.status = 1;
      error.stdout = 'Finding: redacted';
      throw error;
    });

    await expect(analyzer.runSecretsScanning()).resolves.toEqual({
      status: 'failed',
      tool: 'gitleaks',
      details: ['Secrets detected by gitleaks - see redacted details above'],
    });
  });
});
