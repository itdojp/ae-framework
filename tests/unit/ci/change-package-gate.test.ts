import { describe, expect, it } from 'vitest';
import {
  isTrustedSummaryAuthor,
  parseChangePackageValidationResult,
  resolveChangePackageValidationStatus,
} from '../../../scripts/ci/lib/change-package-gate.mjs';

describe('change-package gate helpers', () => {
  it('parses change-package validation result from PR summary comment body', () => {
    const body = `<!-- AE-PR-SUMMARY -->
## Quality Summary
### Change Package Validation
- result: WARN
- strict: false
`;
    expect(parseChangePackageValidationResult(body)).toBe('warn');
  });

  it('returns null when marker or section is missing', () => {
    expect(parseChangePackageValidationResult('no marker')).toBeNull();
    expect(parseChangePackageValidationResult('<!-- AE-PR-SUMMARY -->\n## Quality Summary')).toBeNull();
  });

  it('selects latest parsed result from comment list', () => {
    const comments = [
      {
        created_at: '2026-02-27T00:00:00Z',
        user: { login: 'github-actions' },
        body: '<!-- AE-PR-SUMMARY -->\n### Change Package Validation\n- result: PASS\n',
        html_url: 'https://example.test/1',
      },
      {
        created_at: '2026-02-27T00:02:00Z',
        user: { login: 'github-actions' },
        body: '<!-- AE-PR-SUMMARY -->\n### Change Package Validation\n- result: FAIL\n',
        html_url: 'https://example.test/2',
      },
    ];
    expect(resolveChangePackageValidationStatus(comments)).toEqual({
      status: 'fail',
      sourceUrl: 'https://example.test/2',
    });
  });

  it('returns missing when parseable summary does not exist', () => {
    expect(resolveChangePackageValidationStatus([])).toEqual({
      status: 'missing',
      sourceUrl: null,
    });
    expect(resolveChangePackageValidationStatus([{ body: 'n/a' }])).toEqual({
      status: 'missing',
      sourceUrl: null,
    });
  });

  it('ignores untrusted summary comments', () => {
    const comments = [
      {
        created_at: '2026-02-27T00:00:00Z',
        user: { login: 'contributor-user' },
        body: '<!-- AE-PR-SUMMARY -->\n### Change Package Validation\n- result: PASS\n',
      },
      {
        created_at: '2026-02-27T00:01:00Z',
        user: { login: 'github-actions' },
        body: '<!-- AE-PR-SUMMARY -->\n### Change Package Validation\n- result: WARN\n',
      },
    ];
    expect(resolveChangePackageValidationStatus(comments)).toEqual({
      status: 'warn',
      sourceUrl: null,
    });
  });

  it('detects trusted summary author', () => {
    expect(isTrustedSummaryAuthor({ user: { login: 'github-actions' } })).toBe(true);
    expect(isTrustedSummaryAuthor({ author: { login: 'github-actions[bot]' } })).toBe(true);
    expect(isTrustedSummaryAuthor({ user: { login: 'someone-else' } })).toBe(false);
  });
});
