import { describe, expect, it } from 'vitest';
import {
  buildContributorLicenseReadinessAudit,
  renderMarkdownReport,
} from '../../scripts/legal/build-contributor-license-readiness.mjs';

describe('contributor license readiness audit', () => {
  it('classifies contributors and summarizes noreply/bot counts', () => {
    const audit = buildContributorLicenseReadinessAudit({
      scopeAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        repositoryLicense: 'MIT License',
        packageLicenseField: 'MIT',
        contributorInventory: [
          { author: 'Alice <alice@example.com>', commits: 10 },
          { author: 'alice <12345+alice@users.noreply.github.com>', commits: 3 },
          { author: 'ae-framework-bot <bot@example.com>', commits: 2 },
        ],
      },
      scopeAuditPath: 'artifacts/reference/legal/license-scope-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.gitHeadSha).toBe('1111111111111111111111111111111111111111');
    expect(audit.inputs.contributorCount).toBe(3);
    expect(audit.summary.humanLikeCount).toBe(2);
    expect(audit.summary.botLikeCount).toBe(1);
    expect(audit.summary.noreplyCount).toBe(1);
    expect(audit.summary.topContributorCommits).toBe(10);
    expect(audit.readiness.status).toBe('repo-facts-ready');
  });


  it('does not classify arbitrary agent substrings as bot-like and still detects noreply without angle brackets', () => {
    const audit = buildContributorLicenseReadinessAudit({
      scopeAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        repositoryLicense: 'MIT License',
        packageLicenseField: 'MIT',
        contributorInventory: [
          { author: 'Jane Management <jane@magenta.dev>', commits: 5 },
          { author: 'jane 12345+alice@users.noreply.github.com', commits: 1 },
          { author: 'release-agent <bot@example.com>', commits: 2 },
        ],
      },
      scopeAuditPath: 'artifacts/reference/legal/license-scope-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.summary.humanLikeCount).toBe(2);
    expect(audit.summary.botLikeCount).toBe(1);
    expect(audit.summary.noreplyCount).toBe(1);
  });

  it('renders markdown with escaped author cells', () => {
    const markdown = renderMarkdownReport({
      schemaVersion: 'contributor-license-readiness-audit/v1',
      generatedAt: '2026-03-13T00:00:00.000Z',
      gitHeadSha: '1111111111111111111111111111111111111111',
      inputs: {
        scopeAuditPath: 'artifacts/reference/legal/license-scope-audit.json',
        repositoryLicense: 'MIT License',
        packageLicenseField: 'MIT',
        contributorCount: 1,
      },
      summary: {
        humanLikeCount: 1,
        botLikeCount: 0,
        noreplyCount: 0,
        topContributorCommits: 1,
      },
      contributors: [
        {
          author: 'A|lice <a`b@example.com>',
          commits: 1,
          kind: 'human-like',
          usesNoreply: false,
        },
      ],
      readiness: {
        status: 'repo-facts-ready',
        recommendedAction: 'human-legal-review',
        legalDecisionRequired: true,
        notes: ['Repo facts do not establish relicensing authority.'],
      },
    });

    expect(markdown).toContain('`A\\|lice <a\\`b@example.com>`');
    expect(markdown).toContain('- gitHeadSha: 1111111111111111111111111111111111111111');
    expect(markdown).toContain('## Readiness notes');
  });
});
