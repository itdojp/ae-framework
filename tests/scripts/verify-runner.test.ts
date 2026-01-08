import { describe, it, expect } from 'vitest';
import { listProfiles, resolveProfile } from '../../scripts/verify/run.mjs';

describe('verify runner profiles', () => {
  it('lists supported profiles', () => {
    expect(listProfiles()).toEqual(['lite', 'conformance', 'formal']);
  });

  it('resolves profile commands', () => {
    expect(resolveProfile('conformance')).toEqual([['pnpm', 'run', 'verify:conformance']]);
  });

  it('returns null for unknown profiles', () => {
    expect(resolveProfile('unknown')).toBeNull();
  });
});
