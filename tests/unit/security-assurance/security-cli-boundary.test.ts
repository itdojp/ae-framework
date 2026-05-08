import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path, { join, resolve } from 'node:path';

const tsxBin = resolve('node_modules/.bin/tsx');
const inputSpec = 'fixtures/security-assurance/extract-claims/spec.md';
const scopePath = 'fixtures/security-assurance/sample.security-audit-scope.json';
const targetPath = 'fixtures/security-assurance/code-map-target';
const generatedAt = '2026-05-07T00:00:00.000Z';

const cliEnv = {
  ...process.env,
  VITEST: '',
  NODE_ENV: 'production',
  AE_TEST_NO_EXIT: '0',
  DISABLE_TELEMETRY: 'true',
};

function runSecurity(args: string[], options: { cwd?: string } = {}) {
  return spawnSync(tsxBin, ['src/cli/index.ts', 'security', ...args], {
    cwd: options.cwd,
    encoding: 'utf8',
    timeout: 60_000,
    env: cliEnv,
  });
}

describe('Security Assurance Lane CLI boundary', () => {
  it('prints repo-relative POSIX artifact paths for generated outputs', () => {
    mkdirSync('artifacts', { recursive: true });
    const outDir = mkdtempSync(join(resolve('artifacts'), 'security-cli-boundary-'));
    try {
      const result = runSecurity([
        'extract-claims',
        '--spec',
        inputSpec,
        '--out',
        outDir,
        '--generated-at',
        generatedAt,
      ]);

      expect(result.status, `${result.stdout}\n${result.stderr}`).toBe(0);
      const outputLine = result.stdout.split(/\r?\n/).find((line) => line.startsWith('Output: '));
      const summaryLine = result.stdout.split(/\r?\n/).find((line) => line.startsWith('Summary: '));
      expect(outputLine).toMatch(/^Output: artifacts\/security-cli-boundary-[^\\]+\/security-claims\.json$/);
      expect(summaryLine).toMatch(/^Summary: artifacts\/security-cli-boundary-[^\\]+\/security-claims\.md$/);
      expect(outputLine).not.toContain(process.cwd());
      expect(readFileSync(join(outDir, 'security-claims.json'), 'utf8')).toContain('security-claim/v1');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('rejects --out path traversal before writing artifacts', () => {
    const result = runSecurity([
      'extract-claims',
      '--spec',
      inputSpec,
      '--out',
      '../security-escape',
      '--generated-at',
      generatedAt,
    ]);

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('Unsafe --out path');
    expect(result.stderr).toContain('path traversal');
  });

  it('rejects unsafe absolute --out paths outside the working and temp roots', () => {
    const deniedPath = path.join(path.parse(process.cwd()).root, `ae-security-denied-output-${Date.now()}.json`);
    const result = runSecurity([
      'extract-claims',
      '--spec',
      inputSpec,
      '--out',
      deniedPath,
      '--generated-at',
      generatedAt,
    ]);

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('Unsafe --out path');
    expect(result.stderr).toContain('absolute output paths must stay under');
    expect(existsSync(deniedPath)).toBe(false);
  });

  it('reports malformed JSON input with a stable error prefix', () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-security-cli-malformed-'));
    const malformedClaims = join(fixtureDir, 'malformed-claims.json');
    try {
      writeFileSync(malformedClaims, '{not json', 'utf8');
      const result = runSecurity([
        'map-code',
        '--claims',
        malformedClaims,
        '--scope',
        scopePath,
        '--target',
        targetPath,
        '--out',
        join(fixtureDir, 'out'),
        '--generated-at',
        generatedAt,
      ]);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('Security code-map generation failed');
      expect(result.stderr).toContain('Malformed JSON input:');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
    }
  });

  it('reports schema mismatches at the CLI boundary', () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-security-cli-schema-'));
    const invalidClaims = join(fixtureDir, 'invalid-claims.json');
    try {
      writeFileSync(
        invalidClaims,
        `${JSON.stringify({ schemaVersion: 'security-claim/v1', generatedAt, claims: [{ id: 'SEC-CLAIM-BAD' }] }, null, 2)}\n`,
        'utf8',
      );
      const result = runSecurity([
        'map-code',
        '--claims',
        invalidClaims,
        '--scope',
        scopePath,
        '--target',
        targetPath,
        '--out',
        join(fixtureDir, 'out'),
        '--generated-at',
        generatedAt,
      ]);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('Input security claims failed schema validation');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
    }
  });

  it('reports missing input files with a stable error prefix', () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-security-cli-missing-'));
    try {
      const result = runSecurity([
        'map-code',
        '--claims',
        join(fixtureDir, 'missing-claims.json'),
        '--scope',
        scopePath,
        '--target',
        targetPath,
        '--out',
        join(fixtureDir, 'out'),
        '--generated-at',
        generatedAt,
      ]);

      expect(result.status).toBe(1);
      expect(result.stderr).toContain('Security code-map generation failed');
      expect(result.stderr).toContain('Input file not found:');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
    }
  });
});
