import { describe, expect, it } from 'vitest';
import {
  isTrustedSummaryAuthor,
  parseChangePackageValidationResult,
  resolveChangePackageValidationStatus,
  resolveChangePackageValidationStatusFromChecks,
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


  it('resolves change-package validation from trusted PR-head check runs', () => {
    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
        completedAt: '2026-06-04T00:00:00Z',
        detailsUrl: 'https://example.test/checks/1',
      },
    ])).toEqual({
      status: 'pass',
      sourceUrl: 'https://example.test/checks/1',
    });

    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'CheckRun',
        name: 'cHaNgE pAcKaGe VaLiDaTiOn',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
        completedAt: '2026-06-04T00:00:00Z',
      },
    ])).toEqual({ status: 'pass', sourceUrl: null });

    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'COMPLETED',
        conclusion: 'NEUTRAL',
        completedAt: '2026-06-04T00:00:00Z',
      },
    ])).toEqual({ status: 'warn', sourceUrl: null });

    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'COMPLETED',
        conclusion: 'FAILURE',
        completedAt: '2026-06-04T00:00:00Z',
      },
    ])).toEqual({ status: 'fail', sourceUrl: null });

    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'COMPLETED',
        conclusion: 'SKIPPED',
        completedAt: '2026-06-04T00:00:00Z',
      },
    ])).toEqual({ status: 'fail', sourceUrl: null });

    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'COMPLETED',
        conclusion: 'STARTUP_FAILURE',
        completedAt: '2026-06-04T00:00:00Z',
      },
    ])).toEqual({ status: 'fail', sourceUrl: null });

    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'COMPLETED',
        conclusion: 'UNKNOWN_CONCLUSION',
        completedAt: '2026-06-04T00:00:00Z',
      },
    ])).toEqual({ status: 'fail', sourceUrl: null });
  });

  it('fails closed for missing, pending, and ambiguous check-run evidence', () => {
    expect(resolveChangePackageValidationStatusFromChecks([])).toEqual({
      status: 'missing',
      sourceUrl: null,
    });
    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'IN_PROGRESS',
        conclusion: '',
        startedAt: '2026-06-04T00:00:00Z',
      },
    ])).toEqual({ status: 'pending', sourceUrl: null });
    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
        completedAt: '2026-06-04T00:00:00Z',
      },
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'COMPLETED',
        conclusion: 'FAILURE',
        completedAt: '2026-06-04T00:00:00Z',
      },
    ])).toEqual({ status: 'ambiguous', sourceUrl: null });
  });

  it('treats a timestamp-less queued rerun as pending over older completed evidence', () => {
    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
        completedAt: '2026-06-04T00:01:00Z',
      },
      {
        __typename: 'CheckRun',
        name: 'Change Package Validation',
        status: 'QUEUED',
        conclusion: null,
      },
    ])).toEqual({ status: 'pending', sourceUrl: null });
  });

  it('ignores similarly named non-CheckRun status rollup entries', () => {
    expect(resolveChangePackageValidationStatusFromChecks([
      {
        __typename: 'StatusContext',
        name: 'Change Package Validation',
        context: 'Change Package Validation',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
        completedAt: '2026-06-04T00:00:00Z',
      },
    ])).toEqual({ status: 'missing', sourceUrl: null });
  });

});
