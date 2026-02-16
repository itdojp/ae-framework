import { spawnSync } from 'node:child_process';
import { chmodSync, mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { afterEach, describe, expect, it } from 'vitest';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const REPO_ROOT = path.resolve(__dirname, '..', '..');
const RUN_SCOPED_SOURCE = path.join(REPO_ROOT, 'scripts/mutation/run-scoped.sh');
const describePosixOnly = process.platform === 'win32' ? describe.skip : describe;

const tempDirs: string[] = [];

const createExecutable = (filePath: string, content: string): void => {
  writeFileSync(filePath, content, { encoding: 'utf-8' });
  chmodSync(filePath, 0o755);
};

const setupTempWorkspace = (): { workspace: string; binDir: string } => {
  const workspace = mkdtempSync(path.join(tmpdir(), 'ae-mutation-run-scoped-'));
  tempDirs.push(workspace);

  const scriptsDir = path.join(workspace, 'scripts/mutation');
  mkdirSync(scriptsDir, { recursive: true });
  writeFileSync(path.join(scriptsDir, 'run-scoped.sh'), readFileSync(RUN_SCOPED_SOURCE, 'utf-8'));
  chmodSync(path.join(scriptsDir, 'run-scoped.sh'), 0o755);

  const binDir = path.join(workspace, 'bin');
  mkdirSync(binDir, { recursive: true });

  return { workspace, binDir };
};

const runScoped = (
  workspace: string,
  binDir: string,
  envOverrides: Record<string, string> = {},
): ReturnType<typeof spawnSync> =>
  spawnSync('bash', ['scripts/mutation/run-scoped.sh', '--quick'], {
    cwd: workspace,
    encoding: 'utf-8',
    env: {
      ...process.env,
      PATH: `${binDir}:${process.env.PATH ?? ''}`,
      STRYKER_TIME_LIMIT: '0',
      ...envOverrides,
    },
  });

afterEach(() => {
  while (tempDirs.length > 0) {
    const dir = tempDirs.pop();
    if (dir) {
      rmSync(dir, { recursive: true, force: true });
    }
  }
});

describePosixOnly('scripts/mutation/run-scoped.sh', () => {
  it('fails when mutation report generation fails by default', () => {
    const { workspace, binDir } = setupTempWorkspace();
    createExecutable(path.join(binDir, 'npx'), '#!/usr/bin/env bash\nexit 0\n');
    createExecutable(
      path.join(binDir, 'node'),
      '#!/usr/bin/env bash\nif [[ "${1:-}" == "scripts/mutation/mutation-report.mjs" ]]; then\n  exit 1\nfi\nexit 0\n',
    );

    const result = runScoped(workspace, binDir);

    expect(result.status).toBe(1);
  });

  it('can ignore mutation report failure when strict mode is disabled', () => {
    const { workspace, binDir } = setupTempWorkspace();
    createExecutable(path.join(binDir, 'npx'), '#!/usr/bin/env bash\nexit 0\n');
    createExecutable(
      path.join(binDir, 'node'),
      '#!/usr/bin/env bash\nif [[ "${1:-}" == "scripts/mutation/mutation-report.mjs" ]]; then\n  exit 1\nfi\nexit 0\n',
    );

    const result = runScoped(workspace, binDir, { MUTATION_REPORT_STRICT: '0' });

    expect(result.status).toBe(0);
    expect(result.stderr).toContain('mutation-report failed but ignored');
  });

  it('preserves non-zero status from Stryker execution', () => {
    const { workspace, binDir } = setupTempWorkspace();
    createExecutable(path.join(binDir, 'npx'), '#!/usr/bin/env bash\nexit 7\n');
    createExecutable(path.join(binDir, 'node'), '#!/usr/bin/env bash\nexit 0\n');

    const result = runScoped(workspace, binDir);

    expect(result.status).toBe(7);
    expect(result.stderr).toContain('Stryker exited with status 7');
  });

  it('keeps timeout as non-blocking even when report generation fails', () => {
    const { workspace, binDir } = setupTempWorkspace();
    createExecutable(path.join(binDir, 'npx'), '#!/usr/bin/env bash\nexit 124\n');
    createExecutable(
      path.join(binDir, 'node'),
      '#!/usr/bin/env bash\nif [[ "${1:-}" == "scripts/mutation/mutation-report.mjs" ]]; then\n  exit 1\nfi\nexit 0\n',
    );

    const result = runScoped(workspace, binDir);

    expect(result.status).toBe(0);
    expect(result.stderr).toContain('treated as non-blocking');
    expect(result.stderr).toContain('keeping non-blocking timeout semantics');
  });
});
