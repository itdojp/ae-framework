import { describe, expect, it } from 'vitest';

import { filterArgsForCiIndex } from '../../../scripts/docs/check-doc-consistency-all.mjs';

describe('check-doc-consistency-all', () => {
  it('removes --docs arguments for ci-index checker', () => {
    const result = filterArgsForCiIndex([
      '--root',
      '/tmp/repo',
      '--docs',
      'README.md,docs/README.md',
      '--format',
      'json',
    ]);
    expect(result).toEqual([
      '--root',
      '/tmp/repo',
      '--format',
      'json',
    ]);
  });

  it('removes --docs=... form for ci-index checker', () => {
    const result = filterArgsForCiIndex([
      '--root=/tmp/repo',
      '--docs=README.md,docs/README.md',
      '--format=json',
    ]);
    expect(result).toEqual([
      '--root=/tmp/repo',
      '--format=json',
    ]);
  });
});
