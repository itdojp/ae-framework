import { describe, it, expect } from 'vitest';
import { listProfiles, resolveProfile } from '../../scripts/quality/run.mjs';

describe('quality runner profiles', () => {
  it('lists supported profiles', () => {
    expect(listProfiles()).toEqual(['all', 'gates', 'policy']);
  });

  it('resolves profile commands', () => {
    expect(resolveProfile('gates')).toEqual([['pnpm', 'run', 'quality:gates']]);
  });

  it('returns null for unknown profiles', () => {
    expect(resolveProfile('unknown')).toBeNull();
  });
});
