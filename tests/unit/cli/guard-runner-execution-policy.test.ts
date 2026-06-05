import { afterEach, describe, expect, it, vi } from 'vitest';
import type { AEFrameworkConfig, Guard } from '../../../src/cli/types.js';

const childProcessMock = vi.hoisted(() => ({
  execSync: vi.fn(),
  spawnSync: vi.fn(),
}));

vi.mock('child_process', () => ({
  execSync: childProcessMock.execSync,
  spawnSync: childProcessMock.spawnSync,
}));

import {
  createGuardNpmInvocation,
  createGuardProcessEnv,
  getGuardScriptExecutionPolicy,
  GuardRunner,
  GUARD_SCRIPT_EXECUTION_APPROVAL_SCOPE,
} from '../../../src/cli/guards/GuardRunner.js';

const config = {} as AEFrameworkConfig;

const testExecutionGuard: Guard = {
  name: 'Test Execution Guard',
  description: 'Ensure tests pass',
  rule: 'All tests pass',
  enforcement: 'strict',
};

const coverageGuard: Guard = {
  name: 'Coverage Guard',
  description: 'Ensure coverage is high enough',
  rule: 'Coverage threshold is satisfied',
  enforcement: 'warning',
};

describe('GuardRunner process-starting guard execution policy', () => {
  afterEach(() => {
    vi.clearAllMocks();
  });

  it('defaults agent-context test execution to dry-run without spawning npm scripts', async () => {
    const runner = new GuardRunner(config, {
      env: { AE_GUARD_AGENT_CONTEXT: '1', PATH: '/usr/bin' },
    });

    const result = await runner.run(testExecutionGuard);

    expect(result.success).toBe(true);
    expect(result.message).toContain('Dry-run preview');
    expect(result.message).toContain('npm test --silent');
    expect(childProcessMock.spawnSync).not.toHaveBeenCalled();
  });

  it('defaults untrusted-checkout coverage execution to dry-run without spawning npm scripts', async () => {
    const runner = new GuardRunner(config, {
      env: { AE_GUARD_UNTRUSTED_CHECKOUT: 'true', PATH: '/usr/bin' },
    });

    const result = await runner.run(coverageGuard);

    expect(result.success).toBe(true);
    expect(result.message).toContain('Dry-run preview');
    expect(result.message).toContain('npm run coverage --silent');
    expect(childProcessMock.spawnSync).not.toHaveBeenCalled();
  });

  it('rejects agent-context apply without trusted approval before spawning npm scripts', async () => {
    const runner = new GuardRunner(config, {
      agentContext: true,
      apply: true,
      env: { PATH: '/usr/bin' },
    });

    const result = await runner.run(testExecutionGuard);

    expect(result.success).toBe(false);
    expect(result.message).toContain(`--approval-scope ${GUARD_SCRIPT_EXECUTION_APPROVAL_SCOPE}`);
    expect(result.message).not.toContain('Tests failed');
    expect(childProcessMock.spawnSync).not.toHaveBeenCalled();
  });

  it('executes approved guard scripts with argv-safe spawn and redacted environment', async () => {
    childProcessMock.spawnSync.mockReturnValueOnce({
      status: 0,
      stdout: '2 passing\n',
      stderr: '',
    });

    const runner = new GuardRunner(config, {
      agentContext: true,
      apply: true,
      approvalScope: GUARD_SCRIPT_EXECUTION_APPROVAL_SCOPE,
      cwd: '/repo',
      env: {
        PATH: '/usr/bin',
        HOME: '/home/operator',
        GITHUB_TOKEN: 'ghs-secret',
        SECRET_VALUE: 'secret',
        NPM_TOKEN: 'npm-secret',
      },
    });

    const result = await runner.run(testExecutionGuard);

    expect(result).toEqual({ success: true, message: 'All tests pass' });
    expect(childProcessMock.spawnSync).toHaveBeenCalledWith(
      'npm',
      ['test', '--silent'],
      expect.objectContaining({
        cwd: '/repo',
        encoding: 'utf8',
        shell: false,
        stdio: 'pipe',
      })
    );
    const spawnOptions = childProcessMock.spawnSync.mock.calls[0]?.[2] as { env?: NodeJS.ProcessEnv };
    expect(spawnOptions.env).toMatchObject({ PATH: '/usr/bin', HOME: '/home/operator' });
    expect(spawnOptions.env?.['GITHUB_TOKEN']).toBeUndefined();
    expect(spawnOptions.env?.['SECRET_VALUE']).toBeUndefined();
    expect(spawnOptions.env?.['NPM_TOKEN']).toBeUndefined();
  });



  it('routes Windows npm execution through cmd.exe without enabling shell mode', () => {
    expect(createGuardNpmInvocation(
      ['test', '--silent'],
      'win32',
      { ComSpec: 'C:\\Windows\\System32\\cmd.exe' }
    )).toEqual({
      command: 'C:\\Windows\\System32\\cmd.exe',
      args: ['/d', '/s', '/c', 'npm.cmd', 'test', '--silent'],
    });
  });

  it('falls back to npm test coverage command through argv-safe spawn', async () => {
    childProcessMock.spawnSync
      .mockReturnValueOnce({ status: 1, stdout: 'coverage unavailable', stderr: '' })
      .mockReturnValueOnce({ status: 0, stdout: 'All files      85\n', stderr: '' });

    const runner = new GuardRunner(config, {
      env: { PATH: '/usr/bin' },
    });

    const result = await runner.run(coverageGuard);

    expect(result.success).toBe(true);
    expect(result.message).toContain('Coverage: 85%');
    expect(childProcessMock.spawnSync).toHaveBeenNthCalledWith(
      1,
      'npm',
      ['run', 'coverage', '--silent'],
      expect.objectContaining({ shell: false })
    );
    expect(childProcessMock.spawnSync).toHaveBeenNthCalledWith(
      2,
      'npm',
      ['test', '--', '--coverage', '--silent'],
      expect.objectContaining({ shell: false })
    );
  });

  it('derives dry-run policy from shared agent and untrusted checkout environment markers', () => {
    expect(getGuardScriptExecutionPolicy({ env: { AE_AGENT_CONTEXT: '1' } })).toMatchObject({
      agentContext: true,
      dryRun: true,
      approvalRequired: false,
    });
    expect(getGuardScriptExecutionPolicy({ apply: true, env: { AE_UNTRUSTED_CHECKOUT: '1' } })).toMatchObject({
      agentContext: true,
      dryRun: false,
      approvalRequired: true,
    });
  });

  it('filters common ambient secret variables from guard process environments', () => {
    expect(createGuardProcessEnv({
      PATH: '/usr/bin',
      API_KEY: 'api-secret',
      MY_PASSWORD: 'password',
      SESSION_COOKIE: 'cookie',
      npm_config_cache: '.cache',
    })).toEqual({
      PATH: '/usr/bin',
      npm_config_cache: '.cache',
    });
  });
});
