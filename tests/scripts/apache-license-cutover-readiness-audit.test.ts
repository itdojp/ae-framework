import { describe, expect, it } from 'vitest';
import {
  buildApacheLicenseCutoverReadinessAudit,
  renderMarkdownReport,
} from '../../scripts/legal/build-apache-license-cutover-readiness.mjs';

const sampleScopeAudit = {
  gitHeadSha: '1111111111111111111111111111111111111111',
  repositoryLicense: 'MIT License',
  packageLicenseField: 'MIT',
  nestedNoticeFiles: [],
};

const sampleConditionalAudit = {
  gitHeadSha: '1111111111111111111111111111111111111111',
  items: [],
};

const sampleNoticeAudit = {
  gitHeadSha: '1111111111111111111111111111111111111111',
  inputs: {
    nestedNoticeFilesCount: 0,
  },
  readiness: {
    status: 'draft-ready',
  },
  evidence: {
    nestedNoticeFiles: [],
    unclassifiedConditionalFiles: [],
  },
};

const sampleContributorAudit = {
  gitHeadSha: '1111111111111111111111111111111111111111',
  summary: {
    humanLikeCount: 2,
    botLikeCount: 1,
    noreplyCount: 1,
  },
  readiness: {
    legalDecisionRequired: true,
    notes: ['Repo facts do not establish relicensing authority.'],
  },
};

describe('buildApacheLicenseCutoverReadinessAudit', () => {

  it('derives unclassified blockers from conditional audit even if notice evidence is stale', () => {
    const audit = buildApacheLicenseCutoverReadinessAudit({
      scopeAudit: sampleScopeAudit,
      conditionalAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        items: [
          { path: 'artifacts/raw.bin', originClass: 'runtime-output-or-unclassified' },
        ],
      },
      noticeReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        readiness: { status: 'draft-ready' },
        evidence: { unclassifiedConditionalFiles: [] },
      },
      contributorReadinessAudit: sampleContributorAudit,
      scopeAuditPath: 'scope.json',
      conditionalAuditPath: 'conditional.json',
      noticeReadinessAuditPath: 'notice.json',
      contributorReadinessAuditPath: 'contributors.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('blocked');
    expect(audit.gitHeadSha).toBe('1111111111111111111111111111111111111111');
    expect(audit.summary.unclassifiedConditionalFilesCount).toBe(1);
    expect(audit.readiness.blockers.some((blocker) => blocker.code === 'conditional-origin-unclassified')).toBe(true);
  });

  it('omits human review reasons when the audit is ready', () => {
    const audit = buildApacheLicenseCutoverReadinessAudit({
      scopeAudit: sampleScopeAudit,
      conditionalAudit: sampleConditionalAudit,
      noticeReadinessAudit: sampleNoticeAudit,
      contributorReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        summary: sampleContributorAudit.summary,
        readiness: {
          legalDecisionRequired: false,
          notes: [],
        },
      },
      scopeAuditPath: 'scope.json',
      conditionalAuditPath: 'conditional.json',
      noticeReadinessAuditPath: 'notice.json',
      contributorReadinessAuditPath: 'contributors.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('ready');
    expect(audit.readiness.humanReviewReasons).toEqual([]);
  });

  it('returns human-review-required when blockers are cleared but legal review remains', () => {
    const audit = buildApacheLicenseCutoverReadinessAudit({
      scopeAudit: sampleScopeAudit,
      conditionalAudit: sampleConditionalAudit,
      noticeReadinessAudit: sampleNoticeAudit,
      contributorReadinessAudit: sampleContributorAudit,
      scopeAuditPath: 'artifacts/reference/legal/license-scope-audit.json',
      conditionalAuditPath: 'artifacts/reference/legal/conditional-asset-audit.json',
      noticeReadinessAuditPath: 'artifacts/reference/legal/notice-readiness-audit.json',
      contributorReadinessAuditPath: 'artifacts/reference/legal/contributor-license-readiness-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('human-review-required');
    expect(audit.readiness.recommendedAction).toBe('legal-review');
    expect(audit.summary.blockerCount).toBe(0);
    expect(audit.summary.contributorHumanLikeCount).toBe(2);
  });

  it('returns blocked when notice readiness or MIT baseline is incomplete', () => {
    const audit = buildApacheLicenseCutoverReadinessAudit({
      scopeAudit: {
        ...sampleScopeAudit,
        packageLicenseField: null,
        nestedNoticeFiles: ['docs/third-party/NOTICE'],
      },
      conditionalAudit: sampleConditionalAudit,
      noticeReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        inputs: {
          nestedNoticeFilesCount: 1,
        },
        readiness: { status: 'needs-review' },
        evidence: {
          nestedNoticeFiles: ['vendor/NOTICE'],
          unclassifiedConditionalFiles: ['artifacts/foo.bin'],
        },
      },
      contributorReadinessAudit: sampleContributorAudit,
      scopeAuditPath: 'scope.json',
      conditionalAuditPath: 'conditional.json',
      noticeReadinessAuditPath: 'notice.json',
      contributorReadinessAuditPath: 'contributors.json',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('blocked');
    expect(audit.readiness.recommendedAction).toBe('resolve-blockers');
    expect(audit.summary.blockerCount).toBeGreaterThanOrEqual(3);
    expect(audit.readiness.blockers.some((blocker) => blocker.code === 'package-license-field-not-mit')).toBe(true);
  });

  it('uses notice readiness filtered nested notice count instead of raw scope audit file names', () => {
    const audit = buildApacheLicenseCutoverReadinessAudit({
      scopeAudit: {
        ...sampleScopeAudit,
        nestedNoticeFiles: [
          'docs/project/NOTICE-READINESS-AUDIT.md',
          'tests/contracts/notice-readiness-audit-contract.test.ts',
        ],
      },
      conditionalAudit: sampleConditionalAudit,
      noticeReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        inputs: {
          nestedNoticeFilesCount: 0,
        },
        readiness: { status: 'draft-ready' },
        evidence: {
          nestedNoticeFiles: [],
          unclassifiedConditionalFiles: [],
        },
      },
      contributorReadinessAudit: sampleContributorAudit,
      scopeAuditPath: 'scope.json',
      conditionalAuditPath: 'conditional.json',
      noticeReadinessAuditPath: 'notice.json',
      contributorReadinessAuditPath: 'contributors.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.summary.nestedNoticeFilesCount).toBe(0);
    expect(audit.readiness.blockers.some((blocker) => blocker.code === 'nested-notice-review-required')).toBe(false);
    expect(audit.readiness.status).toBe('human-review-required');
  });

  it('renders a markdown report', () => {
    const audit = buildApacheLicenseCutoverReadinessAudit({
      scopeAudit: sampleScopeAudit,
      conditionalAudit: sampleConditionalAudit,
      noticeReadinessAudit: sampleNoticeAudit,
      contributorReadinessAudit: sampleContributorAudit,
      scopeAuditPath: 'scope.json',
      conditionalAuditPath: 'conditional.json',
      noticeReadinessAuditPath: 'notice.json',
      contributorReadinessAuditPath: 'contributors.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    const markdown = renderMarkdownReport(audit);
    expect(markdown).toContain('# Apache License Cutover Readiness Audit');
    expect(markdown).toContain('- gitHeadSha: 1111111111111111111111111111111111111111');
    expect(markdown).toContain('- status: human-review-required');
    expect(markdown).toContain('- contributor noreply: 1');
  });

  it('rejects mismatched input gitHeadSha values', () => {
    expect(() =>
      buildApacheLicenseCutoverReadinessAudit({
        scopeAudit: sampleScopeAudit,
        conditionalAudit: { ...sampleConditionalAudit, gitHeadSha: '2222222222222222222222222222222222222222' },
        noticeReadinessAudit: sampleNoticeAudit,
        contributorReadinessAudit: sampleContributorAudit,
        scopeAuditPath: 'scope.json',
        conditionalAuditPath: 'conditional.json',
        noticeReadinessAuditPath: 'notice.json',
        contributorReadinessAuditPath: 'contributors.json',
        generatedAt: '2026-03-13T00:00:00.000Z',
      }),
    ).toThrow('input audits must share the same gitHeadSha');
  });

  it('rejects missing input gitHeadSha values', () => {
    expect(() =>
      buildApacheLicenseCutoverReadinessAudit({
        scopeAudit: { ...sampleScopeAudit, gitHeadSha: null },
        conditionalAudit: sampleConditionalAudit,
        noticeReadinessAudit: sampleNoticeAudit,
        contributorReadinessAudit: sampleContributorAudit,
        scopeAuditPath: 'scope.json',
        conditionalAuditPath: 'conditional.json',
        noticeReadinessAuditPath: 'notice.json',
        contributorReadinessAuditPath: 'contributors.json',
        generatedAt: '2026-03-13T00:00:00.000Z',
      }),
    ).toThrow('scope audit gitHeadSha is required');
  });
});
