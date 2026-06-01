import { execFileSync } from 'child_process';

export type TDDTestCommand = 'npm test' | 'pnpm test' | 'yarn test';
export type TDDTestExecutionApproval = 'none' | 'approved-tdd-test-execution';

export interface ResolvedTDDTestCommand {
  executable: string;
  args: string[];
}

export type TDDTestExecutor = (
  executable: string,
  args: string[],
  options: { encoding: 'utf8'; stdio: 'pipe'; shell: false; cwd?: string }
) => string | Buffer;

export const APPROVED_TDD_TEST_EXECUTION = 'approved-tdd-test-execution' as const;

const ALLOWED_TDD_TEST_COMMANDS: Record<TDDTestCommand, ResolvedTDDTestCommand> = {
  'npm test': { executable: 'npm', args: ['test', '--silent'] },
  'pnpm test': { executable: 'pnpm', args: ['test', '--silent'] },
  'yarn test': { executable: 'yarn', args: ['test', '--silent'] },
};

export function resolveSafeTDDTestCommand(testCommand: TDDTestCommand): ResolvedTDDTestCommand {
  const resolved = ALLOWED_TDD_TEST_COMMANDS[testCommand];
  if (!resolved) {
    throw new Error('Unsupported TDD test command');
  }

  return {
    executable: resolved.executable,
    args: [...resolved.args],
  };
}

export function formatTDDTestCommand(command: ResolvedTDDTestCommand): string {
  return [command.executable, ...command.args].join(' ');
}

export function ensureTDDTestExecutionApproved(
  approval: TDDTestExecutionApproval,
  dryRun: boolean
): { approved: boolean; reason?: string } {
  if (dryRun) {
    return { approved: false, reason: 'dry-run mode is enabled' };
  }

  if (approval !== APPROVED_TDD_TEST_EXECUTION) {
    return {
      approved: false,
      reason: `test execution requires approval token '${APPROVED_TDD_TEST_EXECUTION}'`,
    };
  }

  return { approved: true };
}

export function runSafeTDDTestCommand(
  testCommand: TDDTestCommand,
  options: {
    cwd?: string;
    executor?: TDDTestExecutor;
  } = {}
): string | Buffer {
  const resolved = resolveSafeTDDTestCommand(testCommand);
  const executor = options.executor ?? execFileSync;
  const execOptions: { encoding: 'utf8'; stdio: 'pipe'; shell: false; cwd?: string } = {
    encoding: 'utf8',
    stdio: 'pipe',
    shell: false,
  };

  if (options.cwd) {
    execOptions.cwd = options.cwd;
  }

  return executor(resolved.executable, resolved.args, execOptions);
}
