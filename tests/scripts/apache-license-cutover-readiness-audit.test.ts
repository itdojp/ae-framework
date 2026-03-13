import { describe, expect, it } from 'vitest';
import {
  buildApacheLicenseCutoverReadinessAudit,
  renderMarkdownReport,
} from '../../scripts/legal/build-apache-license-cutover-readiness.mjs';

const sampleScopeAudit = {
  repositoryLicense: 'MIT License',
  packageLicenseField: 'MIT',
  nestedNoticeFiles: [],
};

const sampleConditionalAudit = {
  items: [],
};

const sampleNoticeAudit = {
  readiness: {
    status: 'draft-ready',
  },
  evidence: {
    unclassifiedConditionalFiles: [],
  },
};

const sampleContributorAudit = {
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
        readiness: { status: 'needs-review' },
        evidence: { unclassifiedConditionalFiles: ['artifacts/foo.bin'] },
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
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    const markdown = renderMarkdownReport(audit);
    expect(markdown).toContain('# Apache License Cutover Readiness Audit');
    expect(markdown).toContain('- status: human-review-required');
    expect(markdown).toContain('- contributor noreply: 1');
  });
});
