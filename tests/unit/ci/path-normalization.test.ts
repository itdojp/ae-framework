import { describe, expect, it } from 'vitest';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { normalizeArtifactPath as normalizeTs } from '../../../src/utils/path-normalization.js';

const loadNodeNormalizer = async () => {
  const moduleUrl = pathToFileURL(path.resolve('scripts/ci/lib/path-normalization.mjs')).toString();
  const mod = await import(moduleUrl);
  return mod.normalizeArtifactPath as (value: unknown, options?: { repoRoot?: string }) => string | null;
};

describe('normalizeArtifactPath contract', () => {
  it('normalizes relative paths to POSIX separators', async () => {
    const normalizeNode = await loadNodeNormalizer();
    const input = 'reports\\\\lint\\\\verify-lite-lint-summary.json';
    const expected = 'reports/lint/verify-lite-lint-summary.json';
    expect(normalizeTs(input)).toBe(expected);
    expect(normalizeNode(input)).toBe(expected);
  });

  it('converts in-repo absolute paths to repo-relative', async () => {
    const normalizeNode = await loadNodeNormalizer();
    const repoRoot = path.resolve('/tmp/fake-repo');
    const input = path.join(repoRoot, 'artifacts', 'report-envelope.json');
    const expected = 'artifacts/report-envelope.json';
    expect(normalizeTs(input, { repoRoot })).toBe(expected);
    expect(normalizeNode(input, { repoRoot })).toBe(expected);
  });

  it('returns \".\" for paths equal to repoRoot', async () => {
    const normalizeNode = await loadNodeNormalizer();
    const repoRoot = path.resolve('/tmp/fake-repo');
    expect(normalizeTs(repoRoot, { repoRoot })).toBe('.');
    expect(normalizeNode(repoRoot, { repoRoot })).toBe('.');
  });

  it('keeps external absolute paths absolute', async () => {
    const normalizeNode = await loadNodeNormalizer();
    const repoRoot = path.resolve('/tmp/fake-repo');
    const input = '/tmp/external.json';
    expect(normalizeTs(input, { repoRoot })).toBe('/tmp/external.json');
    expect(normalizeNode(input, { repoRoot })).toBe('/tmp/external.json');
  });

  it('resolves filesystem aliases before applying the repository boundary', async () => {
    const normalizeNode = await loadNodeNormalizer();
    const parent = mkdtempSync(path.join(tmpdir(), 'path-normalization-alias-'));
    const repoRoot = path.join(parent, 'repo');
    const aliasRoot = path.join(parent, 'repo-alias');
    const reportPath = path.join(repoRoot, 'artifacts', 'report.json');
    try {
      mkdirSync(path.dirname(reportPath), { recursive: true });
      writeFileSync(reportPath, '{}\n');
      symlinkSync(repoRoot, aliasRoot, 'junction');
      const aliasedReport = path.join(aliasRoot, 'artifacts', 'report.json');
      expect(normalizeTs(aliasedReport, { repoRoot })).toBe('artifacts/report.json');
      expect(normalizeNode(aliasedReport, { repoRoot })).toBe('artifacts/report.json');
    } finally {
      rmSync(parent, { recursive: true, force: true });
    }
  });

  it('resolves an aliased existing repository root for a missing descendant', async () => {
    const normalizeNode = await loadNodeNormalizer();
    const parent = mkdtempSync(path.join(tmpdir(), 'path-normalization-missing-alias-'));
    const repoRoot = path.join(parent, 'repo');
    const aliasRoot = path.join(parent, 'repo-alias');
    try {
      mkdirSync(repoRoot);
      symlinkSync(repoRoot, aliasRoot, 'junction');
      const missingReport = path.join(aliasRoot, 'artifacts', 'not-written.json');
      expect(normalizeTs(missingReport, { repoRoot: aliasRoot })).toBe('artifacts/not-written.json');
      expect(normalizeNode(missingReport, { repoRoot: aliasRoot })).toBe('artifacts/not-written.json');
    } finally {
      rmSync(parent, { recursive: true, force: true });
    }
  });

  it('keeps a missing descendant outside the repository when its existing ancestor is a symlink escape', async () => {
    const normalizeNode = await loadNodeNormalizer();
    const parent = mkdtempSync(path.join(tmpdir(), 'path-normalization-escape-'));
    const repoRoot = path.join(parent, 'repo');
    const externalRoot = path.join(parent, 'external');
    const escapeRoot = path.join(repoRoot, 'escape');
    try {
      mkdirSync(repoRoot);
      mkdirSync(externalRoot);
      symlinkSync(externalRoot, escapeRoot, 'junction');
      const escapedMissingPath = path.join(escapeRoot, 'not-written.json');
      const expected = path.posix.normalize(path.join(externalRoot, 'not-written.json').replace(/\\/g, '/'));
      expect(normalizeTs(escapedMissingPath, { repoRoot })).toBe(expected);
      expect(normalizeNode(escapedMissingPath, { repoRoot })).toBe(expected);
    } finally {
      rmSync(parent, { recursive: true, force: true });
    }
  });

  it('normalizes Windows drive-letter paths as external on POSIX hosts', async () => {
    const normalizeNode = await loadNodeNormalizer();
    const input = 'C:\\\\repo\\\\artifacts\\\\a.json';
    const expected = 'C:/repo/artifacts/a.json';
    expect(normalizeTs(input)).toBe(expected);
    expect(normalizeNode(input)).toBe(expected);
  });

  it('preserves UNC prefix as \"//\"', async () => {
    const normalizeNode = await loadNodeNormalizer();
    const input = '\\\\\\\\server\\\\share\\\\dir\\\\..\\\\file.json';
    const expected = '//server/share/file.json';
    expect(normalizeTs(input)).toBe(expected);
    expect(normalizeNode(input)).toBe(expected);
  });

  it('keeps already-POSIX UNC prefix as \"//\"', async () => {
    const normalizeNode = await loadNodeNormalizer();
    const input = '//server/share/dir/../file.json';
    const expected = '//server/share/file.json';
    expect(normalizeTs(input)).toBe(expected);
    expect(normalizeNode(input)).toBe(expected);
  });
});
