import { describe, expect, it } from 'vitest';

import {
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
    expect(options.unknown).toEqual([]);
  });

  it('prefers base sha when provided', () => {
    const options = parseArgs([
      'node',
      'run-changed-doctest.mjs',
      '--base-ref',
      'origin/main',
      '--base-sha',
      'abc123',
      '--fetch-missing',
    ]);
    expect(resolveBaseTarget(options)).toBe('abc123');
    expect(options.fetchMissing).toBe(true);
  });

  it('filters git diff output to markdown files only', () => {
    const files = parseChangedMarkdownOutput('README.md\nsrc/index.ts\ndocs/README.md\n\n');
    expect(files).toEqual(['README.md', 'docs/README.md']);
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
