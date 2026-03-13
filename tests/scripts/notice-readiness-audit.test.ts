import { describe, expect, it } from 'vitest';
import {
  buildNoticeReadinessAudit,
  renderMarkdownReport,
} from '../../scripts/legal/build-notice-readiness.mjs';

describe('notice readiness audit', () => {
  const baseScopeAudit = {
    gitHeadSha: '1111111111111111111111111111111111111111',
    repositoryLicense: 'MIT License',
    packageLicenseField: 'MIT',
    nestedNoticeFiles: [],
  };

  const baseConditionalAudit = {
    gitHeadSha: '1111111111111111111111111111111111111111',
    summary: {
      byOriginClass: {
        'committed-contract-artifact': 2,
        'tracked-reference-snapshot': 1,
        'test-fixture': 1,
      },
    },
    items: [
      {
        path: 'fixtures/legal/sample.notice-readiness-audit.json',
        originClass: 'test-fixture',
      },
    ],
  };

  it('marks draft-ready when no blockers are present', () => {
    const audit = buildNoticeReadinessAudit({
      scopeAudit: baseScopeAudit,
      conditionalAudit: baseConditionalAudit,
      scopeAuditPath: 'artifacts/reference/legal/license-scope-audit.json',
      conditionalAuditPath: 'artifacts/reference/legal/conditional-asset-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('draft-ready');
    expect(audit.gitHeadSha).toBe('1111111111111111111111111111111111111111');
    expect(audit.readiness.blockers).toHaveLength(0);
    expect(audit.proposedRootNotice.lines[0]).toBe('ae-framework');
  });

  it('rejects mismatched input gitHeadSha values', () => {
    expect(() =>
      buildNoticeReadinessAudit({
        scopeAudit: baseScopeAudit,
        conditionalAudit: {
          ...baseConditionalAudit,
          gitHeadSha: '2222222222222222222222222222222222222222',
        },
        scopeAuditPath: 'artifacts/reference/legal/license-scope-audit.json',
        conditionalAuditPath: 'artifacts/reference/legal/conditional-asset-audit.json',
        generatedAt: '2026-03-13T00:00:00.000Z',
      }),
    ).toThrow('scope and conditional audits must share the same gitHeadSha');
  });

  it('rejects missing input gitHeadSha values', () => {
    expect(() =>
      buildNoticeReadinessAudit({
        scopeAudit: { ...baseScopeAudit, gitHeadSha: null },
        conditionalAudit: baseConditionalAudit,
        scopeAuditPath: 'artifacts/reference/legal/license-scope-audit.json',
        conditionalAuditPath: 'artifacts/reference/legal/conditional-asset-audit.json',
        generatedAt: '2026-03-13T00:00:00.000Z',
      }),
    ).toThrow('scope audit gitHeadSha is required');
  });

  it('adds blockers for nested notices and unclassified conditional assets', () => {
    const audit = buildNoticeReadinessAudit({
      scopeAudit: {
        ...baseScopeAudit,
        nestedNoticeFiles: ['vendor/NOTICE.txt'],
      },
      conditionalAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        summary: {
          byOriginClass: {
            'runtime-output-or-unclassified': 1,
          },
        },
        items: [
          {
            path: 'artifacts/tmp/unclassified.json',
            originClass: 'runtime-output-or-unclassified',
          },
        ],
      },
      scopeAuditPath: 'artifacts/reference/legal/license-scope-audit.json',
      conditionalAuditPath: 'artifacts/reference/legal/conditional-asset-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('needs-review');
    expect(audit.evidence.nestedNoticeFiles).toEqual(['vendor/NOTICE.txt']);
    expect(audit.evidence.unclassifiedConditionalFiles).toEqual([
      'artifacts/tmp/unclassified.json',
    ]);
    expect(audit.readiness.blockers.map((entry) => entry.code)).toEqual([
      'nested-notice-review-required',
      'conditional-origin-unclassified',
    ]);
  });

  it('renders markdown with draft NOTICE and evidence tables', () => {
    const markdown = renderMarkdownReport({
      schemaVersion: 'notice-readiness-audit/v1',
      generatedAt: '2026-03-13T00:00:00.000Z',
      gitHeadSha: '1111111111111111111111111111111111111111',
      inputs: {
        scopeAuditPath: 'artifacts/reference/legal/license-scope-audit.json',
        conditionalAuditPath: 'artifacts/reference/legal/conditional-asset-audit.json',
        repositoryLicense: 'MIT License',
        packageLicenseField: 'MIT',
        nestedNoticeFilesCount: 1,
        conditionalOriginClassCounts: {
          'runtime-output-or-unclassified': 1,
        },
      },
      evidence: {
        nestedNoticeFiles: ['vendor/NOTICE.txt'],
        unclassifiedConditionalFiles: ['artifacts/tmp/a|b.json'],
      },
      readiness: {
        status: 'needs-review',
        recommendedAction: 'review-and-draft',
        blockers: [
          {
            code: 'nested-notice-review-required',
            reason: '1 tracked nested notice files require review before final NOTICE text is approved.',
          },
        ],
        cutoverPrerequisites: ['Update root LICENSE and package.json license field together on cutover.'],
      },
      proposedRootNotice: {
        status: 'draft-only',
        reviewRequired: true,
        title: 'ae-framework',
        lines: [
          'ae-framework',
          'Copyright (c) ae-framework contributors.',
          'This product includes software developed by the ae-framework contributors.',
        ],
      },
    });

    expect(markdown).toContain('# Notice Readiness Audit');
    expect(markdown).toContain('- gitHeadSha: 1111111111111111111111111111111111111111');
    expect(markdown).toContain('| Nested notice file |');
    expect(markdown).toContain('`artifacts/tmp/a\\|b.json`');
    expect(markdown).toContain('## Proposed root NOTICE draft');
    expect(markdown).toContain('This product includes software developed by the ae-framework contributors.');
  });
});
