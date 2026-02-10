import { describe, expect, it } from 'vitest';
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

