import { describe, expect, test, vi } from 'vitest';
import { RedGreenCycleArgsSchema } from '../../../src/mcp-server/schemas.js';
import { TDDGuardServer } from '../../../src/mcp-server/tdd-server.js';
import {
  APPROVED_TDD_TEST_EXECUTION,
  ensureTDDTestExecutionApproved,
  formatTDDTestCommand,
  resolveSafeTDDTestCommand,
  runSafeTDDTestCommand,
  type TDDTestExecutor,
} from '../../../src/mcp-server/tdd-execution-policy.js';

describe('TDD MCP execution policy', () => {
  test('resolves approved test commands to executable plus argv without shell text', () => {
    expect(resolveSafeTDDTestCommand('npm test')).toEqual({
      executable: 'npm',
      args: ['test', '--silent'],
    });
    expect(formatTDDTestCommand(resolveSafeTDDTestCommand('pnpm test'))).toBe('pnpm test --silent');
  });

  test('schema rejects free-form shell command input before execution policy is reached', () => {
    expect(() => RedGreenCycleArgsSchema.parse({
      testCommand: 'npm test; touch artifacts/pwned',
      dryRun: false,
      testExecutionApproval: APPROVED_TDD_TEST_EXECUTION,
    })).toThrow();
  });

  test('dry-run and missing approval both prevent execution', () => {
    expect(ensureTDDTestExecutionApproved('none', true)).toEqual({
      approved: false,
      reason: 'dry-run mode is enabled',
    });
    expect(ensureTDDTestExecutionApproved('none', false)).toEqual({
      approved: false,
      reason: `test execution requires approval token '${APPROVED_TDD_TEST_EXECUTION}'`,
    });
    expect(ensureTDDTestExecutionApproved(APPROVED_TDD_TEST_EXECUTION, false)).toEqual({ approved: true });
  });

  test('runs approved commands through an executable and argv array with shell disabled', () => {
    const executor = vi.fn<TDDTestExecutor>().mockReturnValue('');

    runSafeTDDTestCommand('yarn test', { cwd: process.cwd(), executor });

    expect(executor).toHaveBeenCalledWith(
      'yarn',
      ['test', '--silent'],
      expect.objectContaining({
        cwd: process.cwd(),
        encoding: 'utf8',
        stdio: 'pipe',
        shell: false,
      })
    );
  });

  test('check_red_green_cycle is dry-run by default and reports the approved argv', async () => {
    const server = new TDDGuardServer();
    const result = await (server as any).checkRedGreenCycle({ testCommand: 'pnpm test' });

    expect(result.content[0].text).toContain('TDD test execution was not run');
    expect(result.content[0].text).toContain('Approved executable/argv: pnpm test --silent');
  });
});
