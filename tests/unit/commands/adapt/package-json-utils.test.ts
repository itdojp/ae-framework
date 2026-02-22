import { describe, expect, it } from 'vitest';
import { normalizeScriptRecord, parsePackageJsonWithNormalizedScripts } from '../../../../src/commands/adapt/package-json-utils';

describe('package-json-utils', () => {
  it('normalizes scripts by keeping only string values', () => {
    const scripts = normalizeScriptRecord({
      test: 'vitest run',
      lint: 'eslint .',
      pretest: 1,
      nested: { invalid: true },
    });

    expect(scripts).toEqual({
      test: 'vitest run',
      lint: 'eslint .',
    });
  });

  it('returns undefined when scripts is not an object', () => {
    expect(normalizeScriptRecord('invalid')).toBeUndefined();
    expect(normalizeScriptRecord(['test'])).toBeUndefined();
    expect(normalizeScriptRecord(null)).toBeUndefined();
  });

  it('parses package.json and keeps valid script entries', () => {
    const parsed = parsePackageJsonWithNormalizedScripts<{
      name?: string;
      scripts?: Record<string, string>;
    }>(JSON.stringify({
      name: 'sample',
      scripts: {
        test: 'jest',
        lint: 'eslint .',
        build: 42,
      },
    }));

    expect(parsed.name).toBe('sample');
    expect(parsed.scripts).toEqual({
      test: 'jest',
      lint: 'eslint .',
    });
  });

  it('drops scripts when scripts is not object-like', () => {
    const parsed = parsePackageJsonWithNormalizedScripts<{ scripts?: Record<string, string> }>(
      JSON.stringify({ scripts: 'invalid' }),
    );

    expect(parsed.scripts).toBeUndefined();
  });

  it('returns empty object for non-object JSON roots', () => {
    const parsed = parsePackageJsonWithNormalizedScripts<Record<string, unknown>>('[]');
    expect(parsed).toEqual({});
  });
});
