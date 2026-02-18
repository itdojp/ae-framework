import { describe, expect, it, vi } from 'vitest';
import {
  CLI_CANDIDATES,
  ensureCLI,
  findCLI,
  isExecutedAsMain,
} from '../../../scripts/codex/quickstart.mjs';

describe('codex quickstart cli resolution', () => {
  it('prefers the first CLI candidate when both are present', () => {
    const rootDir = '/tmp/repo';
    const existsFn = vi.fn(() => true);
    const cliPath = findCLI(rootDir, existsFn);
    expect(cliPath).toContain(CLI_CANDIDATES[0]);
  });

  it('returns null when no candidate exists', () => {
    const cliPath = findCLI('/tmp/repo', () => false);
    expect(cliPath).toBeNull();
  });

  it('does not build when CLI already exists', () => {
    const spawn = vi.fn();
    const result = ensureCLI({
      rootDir: '/tmp/repo',
      existsFn: () => true,
      spawn,
      skipBuild: false,
    });
    expect(result.ok).toBe(true);
    expect(result.built).toBe(false);
    expect(spawn).not.toHaveBeenCalled();
  });

  it('fails fast when CODEX_SKIP_BUILD=1 and dist is missing', () => {
    const result = ensureCLI({
      rootDir: '/tmp/repo',
      existsFn: () => false,
      skipBuild: true,
    });
    expect(result.ok).toBe(false);
    expect(result.error).toContain('CODEX_SKIP_BUILD=1');
  });

  it('builds once and resolves CLI when build succeeds', () => {
    const rootDir = '/tmp/repo';
    const expectedCliPath = `${rootDir}/${CLI_CANDIDATES[0]}`;
    let built = false;
    const spawn = vi.fn(() => {
      built = true;
      return { status: 0 };
    });
    const existsFn = vi.fn((candidatePath: string) => built && candidatePath === expectedCliPath);

    const result = ensureCLI({
      rootDir,
      existsFn,
      spawn,
      skipBuild: false,
    });

    expect(spawn).toHaveBeenCalledOnce();
    expect(spawn).toHaveBeenCalledWith(
      'pnpm',
      ['-s', 'run', 'build'],
      expect.objectContaining({ cwd: rootDir, stdio: 'inherit' }),
    );
    expect(result.ok).toBe(true);
    expect(result.built).toBe(true);
    expect(result.cliPath).toContain(CLI_CANDIDATES[0]);
  });

  it('returns failure when build succeeds but CLI is still missing', () => {
    const spawn = vi.fn(() => ({ status: 0 }));
    const result = ensureCLI({
      rootDir: '/tmp/repo',
      existsFn: () => false,
      spawn,
      skipBuild: false,
    });

    expect(spawn).toHaveBeenCalledOnce();
    expect(result.ok).toBe(false);
    expect(result.error).toContain('ae CLI not found after build');
  });

  it('returns failure when build exits with non-zero status', () => {
    const spawn = vi.fn(() => ({ status: 2 }));
    const result = ensureCLI({
      rootDir: '/tmp/repo',
      existsFn: () => false,
      spawn,
      skipBuild: false,
    });
    expect(result.ok).toBe(false);
    expect(result.error).toContain('exit code 2');
  });

  it('returns failure with exit code 127 when pnpm is not found (ENOENT)', () => {
    const spawn = vi.fn(() => ({ status: 1, error: { code: 'ENOENT' } }));
    const result = ensureCLI({
      rootDir: '/tmp/repo',
      existsFn: () => false,
      spawn,
      skipBuild: false,
    });

    expect(result.ok).toBe(false);
    expect(result.error).toContain('exit code 127');
  });

  it('treats URL-escaped module path and argv path as the same file', () => {
    const metaUrl = 'file:///tmp/with%20space/quickstart.mjs';
    const argvPath = '/tmp/with space/quickstart.mjs';
    expect(isExecutedAsMain(metaUrl, argvPath)).toBe(true);
  });
});
