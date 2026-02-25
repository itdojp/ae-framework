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
  it('uses expanded default docs when --docs is omitted', () => {
    const result = parseArgs(['node', 'check-doc-consistency.mjs']);
    expect(result.docs).toEqual(expect.arrayContaining([
      'README.md',
      'docs/getting-started/QUICK-START-GUIDE.md',
      'docs/getting-started/PHASE-6-GETTING-STARTED.md',
      'docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md',
    ]));
    expect(result.docsProvided).toBe(false);
  });

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
    expect(result.docsProvided).toBe(true);
    expect(result.unknown).toEqual([]);
  });

  it('expands default targets with docs/README CI/quality links', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir, { lint: 'echo lint' });
      mkdirSync(path.join(rootDir, 'docs/ci'), { recursive: true });
      mkdirSync(path.join(rootDir, 'docs/quality'), { recursive: true });
      mkdirSync(path.join(rootDir, 'docs/notes'), { recursive: true });
      mkdirSync(path.join(rootDir, 'docs/getting-started'), { recursive: true });
      mkdirSync(path.join(rootDir, 'docs/product'), { recursive: true });
      mkdirSync(path.join(rootDir, 'docs/integrations'), { recursive: true });
      writeFileSync(path.join(rootDir, 'README.md'), '# root');
      writeFileSync(path.join(rootDir, 'docs/README.md'), [
        '- [CI Guide](./ci/guide.md)',
        '- [Quality Guide](./quality/guide.md)',
        '- [Notes](./notes/guide.md)',
      ].join('\n'));
      writeFileSync(path.join(rootDir, 'docs/ci/guide.md'), 'Run `pnpm run lint`.');
      writeFileSync(path.join(rootDir, 'docs/quality/guide.md'), 'Run `pnpm run lint`.');
      writeFileSync(path.join(rootDir, 'docs/notes/guide.md'), 'Run `pnpm run lint`.');
      writeFileSync(path.join(rootDir, 'docs/getting-started/QUICK-START-GUIDE.md'), '# quick');
      writeFileSync(path.join(rootDir, 'docs/getting-started/PHASE-6-GETTING-STARTED.md'), '# phase6');
      writeFileSync(path.join(rootDir, 'docs/product/USER-MANUAL.md'), '# user manual');
      writeFileSync(path.join(rootDir, 'docs/integrations/QUICK-START-CODEX.md'), '# codex');
      writeFileSync(path.join(rootDir, 'docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md'), '# integration');

      const result = runDocConsistencyCheck([
        'node',
        'check-doc-consistency.mjs',
        `--root=${rootDir}`,
      ]);

      expect(result.docsScanned).toEqual(expect.arrayContaining([
        'docs/ci/guide.md',
        'docs/quality/guide.md',
      ]));
      expect(result.docsScanned).not.toContain('docs/notes/guide.md');
    });
  });

  it('does not auto-expand when --docs is explicitly provided', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir, { lint: 'echo lint' });
      mkdirSync(path.join(rootDir, 'docs/ci'), { recursive: true });
      writeFileSync(path.join(rootDir, 'README.md'), 'Run `pnpm run lint`.');
      writeFileSync(path.join(rootDir, 'docs/README.md'), '- [CI Guide](./ci/guide.md)');
      writeFileSync(path.join(rootDir, 'docs/ci/guide.md'), 'Run `pnpm run lint`.');

      const result = runDocConsistencyCheck([
        'node',
        'check-doc-consistency.mjs',
        `--root=${rootDir}`,
        '--docs=README.md',
      ]);

      expect(result.docsScanned).toEqual(['README.md']);
    });
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

  it('ignores generated report/artifact markdown references', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir, { lint: 'echo lint' });
      mkdirSync(path.join(rootDir, 'docs'), { recursive: true });
      writeFileSync(path.join(rootDir, 'docs/guide.md'), [
        'Generated outputs are optional:',
        '- `artifacts/context-pack/context-pack-phase5-report.md`',
        '- `reports/heavy-test-trends-history/summary.md`',
      ].join('\n'));

      const result = runDocConsistencyCheck([
        'node',
        'check-doc-consistency.mjs',
        `--root=${rootDir}`,
        '--docs=docs/guide.md',
      ]);

      expect(result.exitCode).toBe(0);
      expect(result.missingPaths).toHaveLength(0);
    });
  });

  it('does not treat extension-only inline tokens as paths', () => {
    withTempRepo((rootDir) => {
      writePackageJson(rootDir, { lint: 'echo lint' });
      mkdirSync(path.join(rootDir, 'docs'), { recursive: true });
      writeFileSync(path.join(rootDir, 'docs/guide.md'), 'Suffix notation: `.md`');

      const result = runDocConsistencyCheck([
        'node',
        'check-doc-consistency.mjs',
        `--root=${rootDir}`,
        '--docs=docs/guide.md',
      ]);

      expect(result.exitCode).toBe(0);
      expect(result.missingPaths).toHaveLength(0);
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
