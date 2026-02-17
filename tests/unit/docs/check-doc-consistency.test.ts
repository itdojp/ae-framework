import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { parseArgs, runDocConsistencyCheck } from '../../../scripts/docs/check-doc-consistency.mjs';

function withTempRepo(testFn: (rootDir: string) => void): void {
  const rootDir = mkdtempSync(path.join(tmpdir(), 'ae-doc-consistency-'));
  try {
    testFn(rootDir);
  } finally {
    rmSync(rootDir, { recursive: true, force: true });
  }
}

function writePackageJson(rootDir: string, scripts: Record<string, string>): void {
  writeFileSync(path.join(rootDir, 'package.json'), JSON.stringify({
    name: 'temp-doc-consistency',
    private: true,
    scripts,
  }, null, 2));
}

describe('check-doc-consistency', () => {
  it('parses docs and format arguments', () => {
    const result = parseArgs([
      'node',
      'check-doc-consistency.mjs',
      '--',
      '--docs',
      'README.md,docs/README.md',
      '--format',
      'json',
    ]);

    expect(result.docs).toEqual(['README.md', 'docs/README.md']);
    expect(result.format).toBe('json');
    expect(result.unknown).toEqual([]);
  });

  it('detects missing pnpm script references', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir, { build: 'echo build' });
      writeFileSync(path.join(rootDir, 'README.md'), [
        '# sample',
        '```bash',
        'pnpm run build',
        'pnpm run verify:lite',
        '```',
      ].join('\n'));

      const result = runDocConsistencyCheck([
        'node',
        'check-doc-consistency.mjs',
        `--root=${rootDir}`,
        '--docs=README.md',
        '--format=json',
      ]);

      expect(result.exitCode).toBe(1);
      expect(result.missingScripts).toHaveLength(1);
      expect(result.missingScripts[0]).toEqual(expect.objectContaining({
        markdownPath: 'README.md',
        scriptName: 'verify:lite',
      }));
    });
  });

  it('detects missing file path references in links and inline code', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir, { lint: 'echo lint' });
      mkdirSync(path.join(rootDir, 'docs'), { recursive: true });
      writeFileSync(path.join(rootDir, 'README.md'), '# root');
      writeFileSync(path.join(rootDir, 'docs/guide.md'), [
        '[Existing](../README.md)',
        '[Missing](../docs/missing.md)',
        'Reference: `docs/another-missing.md`',
      ].join('\n'));

      const result = runDocConsistencyCheck([
        'node',
        'check-doc-consistency.mjs',
        `--root=${rootDir}`,
        '--docs=docs/guide.md',
      ]);

      expect(result.exitCode).toBe(1);
      expect(result.missingPaths).toHaveLength(2);
      expect(result.missingPaths).toEqual(expect.arrayContaining([
        expect.objectContaining({ reference: '../docs/missing.md' }),
        expect.objectContaining({ reference: 'docs/another-missing.md' }),
      ]));
    });
  });

  it('returns success when scripts and references are consistent', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir, { lint: 'echo lint', 'verify:lite': 'echo verify' });
      mkdirSync(path.join(rootDir, 'docs/getting-started'), { recursive: true });
      writeFileSync(path.join(rootDir, 'README.md'), '# root');
      writeFileSync(path.join(rootDir, 'docs/getting-started/SETUP.md'), '# setup');
      writeFileSync(path.join(rootDir, 'docs/guide.md'), [
        'Run `pnpm run lint` and `pnpm run verify:lite`.',
        'See [Root](../README.md).',
        'Read `docs/getting-started/SETUP.md`.',
      ].join('\n'));

      const result = runDocConsistencyCheck([
        'node',
        'check-doc-consistency.mjs',
        `--root=${rootDir}`,
        '--docs=docs/guide.md',
      ]);

      expect(result.exitCode).toBe(0);
      expect(result.missingDocs).toHaveLength(0);
      expect(result.packageErrors).toHaveLength(0);
      expect(result.missingScripts).toHaveLength(0);
      expect(result.missingPaths).toHaveLength(0);
    });
  });

  it('resolves simple filename links strictly relative to source markdown', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir, { lint: 'echo lint' });
      mkdirSync(path.join(rootDir, 'docs'), { recursive: true });
      writeFileSync(path.join(rootDir, 'README.md'), '# root readme');
      writeFileSync(path.join(rootDir, 'docs/guide.md'), [
        '[Guide local readme](README.md)',
      ].join('\n'));

      const result = runDocConsistencyCheck([
        'node',
        'check-doc-consistency.mjs',
        `--root=${rootDir}`,
        '--docs=docs/guide.md',
      ]);

      expect(result.exitCode).toBe(1);
      expect(result.missingPaths).toEqual([
        expect.objectContaining({
          markdownPath: 'docs/guide.md',
          reference: 'README.md',
        }),
      ]);
    });
  });

  it('reports package.json read error without throwing', () => {
    withTempRepo((rootDir) => {
      mkdirSync(path.join(rootDir, 'docs'), { recursive: true });
      writeFileSync(path.join(rootDir, 'docs/guide.md'), 'Run `pnpm run lint`.');

      const result = runDocConsistencyCheck([
        'node',
        'check-doc-consistency.mjs',
        `--root=${rootDir}`,
        '--docs=docs/guide.md',
      ]);

      expect(result.exitCode).toBe(1);
      expect(result.packageErrors).toEqual([
        expect.objectContaining({ code: 'package_json_read_error' }),
      ]);
    });
  });
});
