import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';

const scriptPath = resolve('scripts/codex/generate-openapi-tests.ts');
const tsxBin = resolve('node_modules/.bin/tsx');
const fixturePath = 'artifacts/codex/generate-openapi-tests-security/openapi.json';
const defaultOutputDir = resolve('artifacts/codex/generated-tests');
const fixtureDir = resolve(dirname(fixturePath));
const outsideRepoDir = resolve('..', 'generate-openapi-tests-security-outside');

const writeSpec = () => {
  mkdirSync(fixtureDir, { recursive: true });
  writeFileSync(resolve(fixturePath), JSON.stringify({
    openapi: '3.0.0',
    paths: {
      '/orders\n../escape': {
        get: {
          operationId: "evil');\nimport fs from 'fs';/*",
          responses: {
            200: {
              content: {
                'application/json': {
                  schema: { type: 'object' },
                },
              },
            },
          },
        },
      },
    },
  }), 'utf8');
};

const runGenerator = (args: string[] = [], env: Record<string, string | undefined> = {}) => spawnSync(tsxBin, [scriptPath, ...args], {
  encoding: 'utf8',
  env: {
    ...process.env,
    CONTRACTS_OPENAPI_PATH: fixturePath,
    ...env,
  },
  timeout: 60_000,
});

describe('generate-openapi-tests security policy', () => {
  it('writes generated tests to review artifacts by default with sanitized filenames', () => {
    rmSync(fixtureDir, { recursive: true, force: true });
    rmSync(defaultOutputDir, { recursive: true, force: true });
    writeSpec();

    try {
      const result = runGenerator(['--use-operation-id']);

      expect(result.status).toBe(0);
      expect(result.stdout).toContain('artifacts/codex/generated-tests/');
      expect(existsSync(resolve('artifacts/codex/generated-tests/evil-import-fs-from-fs.spec.ts'))).toBe(true);
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(defaultOutputDir, { recursive: true, force: true });
    }
  });

  it('rejects writing generated tests under tests without explicit reviewed approval', () => {
    rmSync(fixtureDir, { recursive: true, force: true });
    writeSpec();

    try {
      const result = runGenerator(['--output-dir', 'tests/api/generated']);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('Writing generated tests under tests/ requires');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
    }
  });

  it('rejects writing generated tests directly to the tests directory without explicit reviewed approval', () => {
    rmSync(fixtureDir, { recursive: true, force: true });
    writeSpec();

    try {
      const result = runGenerator(['--output-dir', 'tests']);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('Writing generated tests under tests/ requires');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
    }
  });

  it('rejects output directories that resolve through symlinks outside the workspace', () => {
    rmSync(fixtureDir, { recursive: true, force: true });
    rmSync(outsideRepoDir, { recursive: true, force: true });
    writeSpec();
    mkdirSync(outsideRepoDir, { recursive: true });
    const symlinkPath = resolve('artifacts/codex/generate-openapi-tests-security/symlink-out');
    try {
      symlinkSync(outsideRepoDir, symlinkPath, 'dir');
    } catch {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outsideRepoDir, { recursive: true, force: true });
      return;
    }

    try {
      const result = runGenerator(['--output-dir', 'artifacts/codex/generate-openapi-tests-security/symlink-out']);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('resolves through a filesystem entry outside the approved workspace');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outsideRepoDir, { recursive: true, force: true });
    }
  });

  it('rejects absolute output directories outside the workspace', () => {
    rmSync(fixtureDir, { recursive: true, force: true });
    writeSpec();

    try {
      const result = runGenerator(['--output-dir', outsideRepoDir]);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('outside the approved workspace');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
    }
  });

  it('rejects absolute output directories that target the workspace root', () => {
    rmSync(fixtureDir, { recursive: true, force: true });
    writeSpec();

    try {
      const result = runGenerator(['--output-dir', resolve('.')]);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('must not target the workspace root');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
    }
  });

  it('allows writing under tests only with explicit reviewed approval', () => {
    rmSync(fixtureDir, { recursive: true, force: true });
    rmSync(resolve('tests/api/generated/evil-import-fs-from-fs.spec.ts'), { force: true });
    writeSpec();

    try {
      const result = runGenerator(
        ['--use-operation-id', '--output-dir', 'tests/api/generated', '--approve-generated-tests'],
        { CODEX_GENERATE_TESTS_APPROVAL: 'reviewed-generated-tests' },
      );

      expect(result.status).toBe(0);
      expect(result.stdout).toContain('tests/api/generated/');
      expect(existsSync(resolve('tests/api/generated/evil-import-fs-from-fs.spec.ts'))).toBe(true);
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(resolve('tests/api/generated/evil-import-fs-from-fs.spec.ts'), { force: true });
    }
  });
});
