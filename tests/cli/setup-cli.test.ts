import { describe, it, expect, beforeAll, beforeEach, vi } from 'vitest';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';

const safeExitMock = vi.fn();
const getAvailableTemplatesMock = vi.fn();
const suggestTemplatesMock = vi.fn();
const getTemplateMock = vi.fn();
const installTemplateMock = vi.fn();
const detectPackageManagerMock = vi.fn();
const readlineQuestionMock = vi.fn();
const readlineCloseMock = vi.fn();
let lastRoot: string | undefined;

vi.mock('../../src/utils/safe-exit.js', () => ({
  safeExit: (...args: unknown[]) => safeExitMock(...args),
}));

vi.mock('node:readline/promises', () => ({
  createInterface: () => ({
    question: (...args: unknown[]) => readlineQuestionMock(...args),
    close: () => readlineCloseMock(),
  }),
}));

vi.mock('../../src/utils/installer-manager.js', () => ({
  InstallerManager: class {
    constructor(root: string) {
      lastRoot = root;
    }
    getAvailableTemplates() {
      return getAvailableTemplatesMock();
    }
    suggestTemplates() {
      return suggestTemplatesMock();
    }
    getTemplate(id: string) {
      return getTemplateMock(id);
    }
    installTemplate(id: string, context: unknown) {
      return installTemplateMock(id, context);
    }
    detectPackageManager() {
      return detectPackageManagerMock();
    }
  },
}));

let createSetupCommand: () => any;

beforeAll(async () => {
  ({ createSetupCommand } = await import('../../src/cli/setup-cli.js'));
});

beforeEach(() => {
  safeExitMock.mockReset();
  getAvailableTemplatesMock.mockReset();
  suggestTemplatesMock.mockReset();
  getTemplateMock.mockReset();
  installTemplateMock.mockReset();
  detectPackageManagerMock.mockReset();
  readlineQuestionMock.mockReset();
  readlineCloseMock.mockReset();
  lastRoot = undefined;
});

describe('setup CLI', () => {
  it('uses parent root when subcommand root is not provided', async () => {
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const parentRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'setup-parent-'));

    getAvailableTemplatesMock.mockReturnValue([]);

    const command = createSetupCommand();
    await command.parseAsync(['node', 'cli', '--root', parentRoot, 'list']);

    expect(lastRoot).toBe(parentRoot);
    consoleLogSpy.mockRestore();
  });

  it('uses subcommand root when provided', async () => {
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const parentRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'setup-parent-'));
    const childRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'setup-child-'));

    getAvailableTemplatesMock.mockReturnValue([]);

    const command = createSetupCommand();
    await command.parseAsync(['node', 'cli', '--root', parentRoot, 'list', '--root', childRoot]);

    expect(lastRoot).toBe(childRoot);
    consoleLogSpy.mockRestore();
  });

  it('suggest uses root to initialize installer manager', async () => {
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const root = fs.mkdtempSync(path.join(os.tmpdir(), 'setup-suggest-'));

    suggestTemplatesMock.mockResolvedValue({ suggestions: [], reasoning: [] });

    const command = createSetupCommand();
    await command.parseAsync(['node', 'cli', '--root', root, 'suggest']);

    expect(lastRoot).toBe(root);
    consoleLogSpy.mockRestore();
  });

  it('exits when template is missing', async () => {
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
    getTemplateMock.mockReturnValue(undefined);

    const command = createSetupCommand();
    await command.parseAsync(['node', 'cli', 'missing-template']);

    expect(installTemplateMock).not.toHaveBeenCalled();
    expect(safeExitMock).toHaveBeenCalledWith(2);
    consoleErrorSpy.mockRestore();
  });

  it('exits on invalid package manager', async () => {
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
    getTemplateMock.mockReturnValue({ id: 'typescript-node' });

    const command = createSetupCommand();
    await command.parseAsync(['node', 'cli', 'typescript-node', '--package-manager', 'invalid']);

    expect(installTemplateMock).not.toHaveBeenCalled();
    expect(safeExitMock).toHaveBeenCalledWith(2);
    consoleErrorSpy.mockRestore();
  });

  it('passes install context when provided', async () => {
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    getTemplateMock.mockReturnValue({ id: 'typescript-node' });
    installTemplateMock.mockResolvedValue({
      success: true,
      message: 'ok',
      installedDependencies: [],
      createdFiles: [],
      configuredFiles: [],
      executedSteps: [],
      warnings: [],
      errors: [],
      duration: 1,
    });

    const command = createSetupCommand();
    await command.parseAsync([
      'node',
      'cli',
      'typescript-node',
      '--name',
      'my-app',
      '--package-manager',
      'pnpm',
    ]);

    expect(installTemplateMock).toHaveBeenCalledWith('typescript-node', {
      projectName: 'my-app',
      packageManager: 'pnpm',
    });
    expect(safeExitMock).not.toHaveBeenCalled();
    consoleLogSpy.mockRestore();
  });

  it('exits when wizard runs without tty', async () => {
    const consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
    const originalStdinTTY = process.stdin.isTTY;
    const originalStdoutTTY = process.stdout.isTTY;

    Object.defineProperty(process.stdin, 'isTTY', { value: false, configurable: true });
    Object.defineProperty(process.stdout, 'isTTY', { value: false, configurable: true });

    const command = createSetupCommand();
    await command.parseAsync(['node', 'cli', 'wizard']);

    expect(safeExitMock).toHaveBeenCalledWith(2);

    Object.defineProperty(process.stdin, 'isTTY', { value: originalStdinTTY, configurable: true });
    Object.defineProperty(process.stdout, 'isTTY', { value: originalStdoutTTY, configurable: true });
    consoleErrorSpy.mockRestore();
  });

  it('runs wizard flow and installs template', async () => {
    const consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const originalStdinTTY = process.stdin.isTTY;
    const originalStdoutTTY = process.stdout.isTTY;

    Object.defineProperty(process.stdin, 'isTTY', { value: true, configurable: true });
    Object.defineProperty(process.stdout, 'isTTY', { value: true, configurable: true });

    getAvailableTemplatesMock.mockReturnValue([
      { id: 'typescript-node', name: 'TypeScript Node', description: '', category: 'api', language: 'typescript' },
    ]);
    getTemplateMock.mockReturnValue({ id: 'typescript-node' });
    detectPackageManagerMock.mockResolvedValue('pnpm');
    installTemplateMock.mockResolvedValue({
      success: true,
      message: 'ok',
      installedDependencies: [],
      createdFiles: [],
      configuredFiles: [],
      executedSteps: [],
      warnings: [],
      errors: [],
      duration: 1,
    });

    readlineQuestionMock
      .mockResolvedValueOnce('1')
      .mockResolvedValueOnce('my-app')
      .mockResolvedValueOnce('pnpm')
      .mockResolvedValueOnce('y');

    const command = createSetupCommand();
    await command.parseAsync(['node', 'cli', 'wizard']);

    expect(installTemplateMock).toHaveBeenCalledWith('typescript-node', {
      projectName: 'my-app',
      packageManager: 'pnpm',
    });

    Object.defineProperty(process.stdin, 'isTTY', { value: originalStdinTTY, configurable: true });
    Object.defineProperty(process.stdout, 'isTTY', { value: originalStdoutTTY, configurable: true });
    consoleLogSpy.mockRestore();
  });
});
