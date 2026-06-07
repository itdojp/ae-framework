import { chmod, mkdir, mkdtemp, readFile, rm, writeFile } from 'fs/promises';
import * as path from 'path';
import { afterEach, beforeEach, describe, expect, test, vi } from 'vitest';
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
  const testRoots: string[] = [];
  const originalEnv = { ...process.env };

  beforeEach(() => {
    process.env = {
      PATH: originalEnv.PATH,
      HOME: originalEnv.HOME,
    };
  });

  afterEach(async () => {
    process.env = { ...originalEnv };
    vi.restoreAllMocks();
    await Promise.all(testRoots.splice(0).map(root => rm(root, { recursive: true, force: true })));
  });

  test('resolves approved test commands to executable plus argv without shell text', () => {
    expect(resolveSafeTDDTestCommand('npm test')).toEqual({
      executable: 'npm',
      args: ['test', '--silent'],
    });
    expect(formatTDDTestCommand(resolveSafeTDDTestCommand('pnpm test'))).toBe('pnpm test --silent');
  });

  test('resolves Windows package-manager shims through fixed cmd.exe argv', () => {
    expect(resolveSafeTDDTestCommand('npm test', 'win32')).toEqual({
      executable: 'cmd.exe',
      args: ['/d', '/s', '/c', 'npm.cmd', 'test', '--silent'],
    });
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

  test('approved agent execution is blocked when the raw environment contains ambient secrets', () => {
    process.env['GITHUB_TOKEN'] = 'ghs-secret';

    expect(ensureTDDTestExecutionApproved(APPROVED_TDD_TEST_EXECUTION, false)).toEqual({
      approved: false,
      reason: 'ambient-secrets-present',
    });
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

  test('runs Windows-approved commands through fixed cmd.exe argv with shell disabled', () => {
    const executor = vi.fn<TDDTestExecutor>().mockReturnValue('');

    runSafeTDDTestCommand('pnpm test', { cwd: process.cwd(), executor, platform: 'win32' });

    expect(executor).toHaveBeenCalledWith(
      'cmd.exe',
      ['/d', '/s', '/c', 'pnpm.cmd', 'test', '--silent'],
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

  test('check_red_green_cycle runs approved tests in the approved workspace root', async () => {
    const workspaceRoot = await createTempWorkspace();
    const binDir = path.join(workspaceRoot, 'bin');
    const capturedCwd = path.join(workspaceRoot, 'captured-cwd.txt');
    await mkdir(binDir, { recursive: true });
    await writeFile(
      path.join(binDir, 'npm'),
      ['#!/bin/sh', 'printf "%s" "$PWD" > "$CWD_CAPTURE"', 'exit 0', ''].join('\n'),
      'utf8'
    );
    await chmod(path.join(binDir, 'npm'), 0o755);
    process.env['AE_MCP_WORKSPACE_ROOT'] = workspaceRoot;
    process.env['CWD_CAPTURE'] = capturedCwd;
    process.env['PATH'] = `${binDir}${path.delimiter}${originalEnv.PATH ?? ''}`;

    const server = new TDDGuardServer();
    const result = await (server as any).checkRedGreenCycle({
      testCommand: 'npm test',
      dryRun: false,
      testExecutionApproval: APPROVED_TDD_TEST_EXECUTION,
      expectRed: false,
    });

    expect(result.content[0].text).toContain('Tests are GREEN');
    expect(await readFile(capturedCwd, 'utf8')).toBe(workspaceRoot);
  });

  test('analyze_tdd_compliance is non-proceedable when 4-code test execution is skipped', async () => {
    const workspaceRoot = await createTempWorkspace();
    const projectRoot = path.join(workspaceRoot, 'project');
    await mkdir(path.join(projectRoot, 'src'), { recursive: true });
    await mkdir(path.join(projectRoot, 'tests'), { recursive: true });
    await writeFile(path.join(projectRoot, 'src', 'example.ts'), 'export const example = 1;\n', 'utf8');
    await writeFile(path.join(projectRoot, 'tests', 'example.test.ts'), 'import "../src/example.js";\n', 'utf8');
    process.env['AE_MCP_WORKSPACE_ROOT'] = workspaceRoot;

    const server = new TDDGuardServer();
    const result = await (server as any).analyzeTDDCompliance({
      path: 'project',
      phase: '4-code',
      testCommand: 'pnpm test',
    });

    expect(result.content[0].text).toContain('❌ Violations must be fixed');
    expect(result.content[0].text).toContain('test_execution_skipped');
    expect(result.content[0].text).toContain('cannot verify GREEN phase test results');
  });

  async function createTempWorkspace(): Promise<string> {
    const rootParent = path.join(process.cwd(), 'artifacts', 'tmp', 'tdd-execution-policy');
    await mkdir(rootParent, { recursive: true });
    const workspaceRoot = await mkdtemp(path.join(rootParent, 'workspace-'));
    testRoots.push(workspaceRoot);
    return workspaceRoot;
  }
});
