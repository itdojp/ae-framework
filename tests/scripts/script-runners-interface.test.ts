import { describe, it, expect } from 'vitest';

import { parseArgs as parseQualityArgs } from '../../scripts/quality/run.mjs';
import { parseArgs as parseVerifyArgs } from '../../scripts/verify/run.mjs';

describe('script runner interface', () => {
  it('quality runner accepts --profile=<name>', () => {
    const options = parseQualityArgs(['node', 'scripts/quality/run.mjs', '--profile=all']);
    expect(options.profile).toBe('all');
    expect(options.profileError).toBe(false);
    expect(options.unknown).toEqual([]);
  });

  it('quality runner accepts -p=<name>', () => {
    const options = parseQualityArgs(['node', 'scripts/quality/run.mjs', '-p=all']);
    expect(options.profile).toBe('all');
    expect(options.profileError).toBe(false);
    expect(options.unknown).toEqual([]);
  });

  it('verify runner accepts --profile=<name>', () => {
    const options = parseVerifyArgs(['node', 'scripts/verify/run.mjs', '--profile=lite']);
    expect(options.profile).toBe('lite');
    expect(options.profileError).toBe(false);
    expect(options.unknown).toEqual([]);
  });

  it('verify runner accepts -p=<name>', () => {
    const options = parseVerifyArgs(['node', 'scripts/verify/run.mjs', '-p=lite']);
    expect(options.profile).toBe('lite');
    expect(options.profileError).toBe(false);
    expect(options.unknown).toEqual([]);
  });

  it('runners treat empty --profile= as an error', () => {
    const quality = parseQualityArgs(['node', 'scripts/quality/run.mjs', '--profile=']);
    expect(quality.profileError).toBe(true);

    const verify = parseVerifyArgs(['node', 'scripts/verify/run.mjs', '-p=']);
    expect(verify.profileError).toBe(true);
  });
});

