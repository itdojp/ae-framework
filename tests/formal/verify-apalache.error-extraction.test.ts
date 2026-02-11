import { describe, it, expect } from 'vitest';
import { extractErrors, countErrors, extractErrorSnippet } from '../../scripts/formal/verify-apalache.mjs';

describe('verify-apalache error extraction', () => {
  it('matches full keywords and ignores partial stems', () => {
    const output = [
      'Info: ok',
      'violat',
      'violation detected',
      'unsatisfied constraint',
      'dead end reached',
      'counter-example found',
      'error: failure'
    ].join('\n');

    const errors = extractErrors(output);
    expect(errors).not.toContain('violat');
    expect(errors).toEqual(
      expect.arrayContaining([
        'violation detected',
        'unsatisfied constraint',
        'dead end reached',
        'counter-example found',
        'error: failure'
      ])
    );
    expect(countErrors(output)).toBe(5);
  });

  it('does not treat "no error" markers as errors', () => {
    const output = [
      'The outcome is: NoError',
      'Checker reports no error up to computation length 10',
      'EXITCODE: OK (0)',
      'No errors found',
      'No violations found',
      'Found 0 error(s)'
    ].join('\n');

    expect(extractErrors(output)).toEqual([]);
    expect(countErrors(output)).toBe(0);
    expect(extractErrorSnippet(output)).toBeNull();
  });

  it('returns a snippet around the first matched line', () => {
    const output = [
      'line 1',
      'line 2',
      'unsat result',
      'line 4',
      'line 5'
    ].join('\n');
    const snippet = extractErrorSnippet(output);
    expect(snippet).not.toBeNull();
    expect(snippet?.lines).toContain('unsat result');
  });
});
