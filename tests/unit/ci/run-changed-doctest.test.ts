import { describe, expect, it } from 'vitest';

import {
  batchFilesForDoctest,
  isExecutedAsMain,
  parseArgs,
  parseChangedMarkdownOutput,
  resolveBaseTarget,
} from '../../../scripts/ci/run-changed-doctest.mjs';

describe('run-changed-doctest', () => {
  it('parses base ref arguments', () => {
    const options = parseArgs(['node', 'run-changed-doctest.mjs', '--base-ref', 'origin/main']);
    expect(options.baseRef).toBe('origin/main');
    expect(options.baseSha).toBe('');
    expect(options.fetchMissing).toBe(false);
    expect(options.errors).toEqual([]);
    expect(options.unknown).toEqual([]);
  });

  it('prefers base sha when provided', () => {
    const options = parseArgs([
      'node',
      'run-changed-doctest.mjs',
      '--base-ref',
      'origin/main',
      '--base-sha',
      'abc1234',
      '--fetch-missing',
    ]);
    expect(resolveBaseTarget(options)).toBe('abc1234');
    expect(options.fetchMissing).toBe(true);
  });

  it('reports dedicated errors for missing base-ref values', () => {
    const options = parseArgs(['node', 'run-changed-doctest.mjs', '--base-ref']);
    expect(options.errors).toEqual(['--base-ref requires a value']);
    expect(options.unknown).toEqual([]);
  });

  it('rejects invalid base-sha values in inline form', () => {
    const options = parseArgs(['node', 'run-changed-doctest.mjs', '--base-sha=--cached']);
    expect(options.errors).toEqual(['--base-sha must be a hex commit SHA']);
  });

  it('filters git diff output to markdown files only', () => {
    const files = parseChangedMarkdownOutput('README.md\nsrc/index.ts\ndocs/README.md\n\n');
    expect(files).toEqual(['README.md', 'docs/README.md']);
  });

  it('batches doctest inputs to avoid oversized argv payloads', () => {
    const batches = batchFilesForDoctest([
      'docs/a.md',
      'docs/b.md',
      'docs/c.md',
    ], 20);
    expect(batches).toEqual([
      ['docs/a.md', 'docs/b.md'],
      ['docs/c.md'],
    ]);
  });

  it('matches main module path with URL-escaped argv path', () => {
    expect(
      isExecutedAsMain(
        'file:///tmp/with%20space/run-changed-doctest.mjs',
        '/tmp/with space/run-changed-doctest.mjs',
      ),
    ).toBe(true);
  });
});
