import { execFileSync } from 'child_process';
import {
  createHighImpactChildEnv,
  evaluateHighImpactActionPolicy,
} from '../utils/high-impact-action-policy.js';

export type TDDTestCommand = 'npm test' | 'pnpm test' | 'yarn test';
export type TDDTestExecutionApproval = 'none' | 'approved-tdd-test-execution';

export interface ResolvedTDDTestCommand {
  executable: string;
  args: string[];
}

export type TDDTestExecutor = (
  executable: string,
  args: string[],
  options: { encoding: 'utf8'; stdio: 'pipe'; shell: false; cwd?: string; env?: NodeJS.ProcessEnv }
) => string | Buffer;

export const APPROVED_TDD_TEST_EXECUTION = 'approved-tdd-test-execution' as const;

const ALLOWED_TDD_TEST_COMMANDS: Record<TDDTestCommand, ResolvedTDDTestCommand> = {
  'npm test': { executable: 'npm', args: ['test', '--silent'] },
  'pnpm test': { executable: 'pnpm', args: ['test', '--silent'] },
  'yarn test': { executable: 'yarn', args: ['test', '--silent'] },
};

export function resolveSafeTDDTestCommand(
  testCommand: TDDTestCommand,
  platform: NodeJS.Platform = process.platform
): ResolvedTDDTestCommand {
  const resolved = ALLOWED_TDD_TEST_COMMANDS[testCommand];
  if (!resolved) {
    throw new Error('Unsupported TDD test command');
  }

  if (platform === 'win32') {
    return {
      executable: 'cmd.exe',
      args: ['/d', '/s', '/c', `${resolved.executable}.cmd`, ...resolved.args],
    };
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
  const decision = evaluateHighImpactActionPolicy({
    actionKind: 'package-manager',
    actionName: 'mcp-tdd-test-execution',
    apply: dryRun === false,
    dryRun,
    approvalScope: approval,
    requiredApprovalScope: APPROVED_TDD_TEST_EXECUTION,
    env: createHighImpactChildEnv(),
    agentContext: true,
  });

  if (decision.allowed) {
    return { approved: true };
  }
  if (decision.reason === 'explicit-dry-run') {
    return { approved: false, reason: 'dry-run mode is enabled' };
  }
  if (decision.approvalRequired) {
    return {
      approved: false,
      reason: `test execution requires approval token '${APPROVED_TDD_TEST_EXECUTION}'`,
    };
  }
  return { approved: false, reason: decision.reason };
}

export function runSafeTDDTestCommand(
  testCommand: TDDTestCommand,
  options: {
    cwd?: string;
    executor?: TDDTestExecutor;
    platform?: NodeJS.Platform;
  } = {}
): string | Buffer {
  const resolved = resolveSafeTDDTestCommand(testCommand, options.platform);
  const executor = options.executor ?? execFileSync;
  const execOptions: { encoding: 'utf8'; stdio: 'pipe'; shell: false; cwd?: string; env?: NodeJS.ProcessEnv } = {
    encoding: 'utf8',
    stdio: 'pipe',
    shell: false,
    env: createHighImpactChildEnv(),
  };

  if (options.cwd) {
    execOptions.cwd = options.cwd;
  }

  return executor(resolved.executable, resolved.args, execOptions);
}
