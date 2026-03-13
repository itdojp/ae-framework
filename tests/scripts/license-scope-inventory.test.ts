import { describe, expect, it } from 'vitest';
import {
  buildLicenseScopeAudit,
  buildMarkdownReport,
  classifyTrackedPath,
  parseShortlog,
  resolveGeneratedAt,
  resolveGitHeadSha,
} from '../../scripts/legal/inventory-license-scope.mjs';

describe('license scope inventory helpers', () => {
  it('classifies tracked paths into declared buckets', () => {
    expect(classifyTrackedPath('docs/project/RELEASE.md')).toBe('first-party');
    expect(classifyTrackedPath('README.md')).toBe('first-party-root');
    expect(classifyTrackedPath('LICENSE')).toBe('legal-root');
    expect(classifyTrackedPath('artifacts/reference/types/public-types.current.d.ts')).toBe('conditional');
    expect(classifyTrackedPath('unknown.txt')).toBe('other');
  });

  it('parses git shortlog output', () => {
    expect(
      parseShortlog('  10 Alice <alice@example.com>\n  2 Bob <bob@example.com>\n'),
    ).toEqual([
      { commits: 10, author: 'Alice <alice@example.com>' },
      { commits: 2, author: 'Bob <bob@example.com>' },
    ]);
  });

  it('builds audit summary with conditional breakdown and nested notices', () => {
    const audit = buildLicenseScopeAudit({
      trackedFiles: [
        'README.md',
        'docs/project/RELEASE.md',
        'artifacts/reference/types/public-types.current.d.ts',
        'fixtures/agents/sample.ae-handoff.json',
        'test-cassettes/Custom_directory_test.json',
        'LICENSE',
        'vendor/NOTICE.txt',
        'vendor/LICENSE-MIT',
      ],
      shortlogText: '  10 Alice <alice@example.com>\n  2 Bob <bob@example.com>\n',
      packageJson: { license: 'MIT' },
      rootLicenseText: 'MIT License\n\nCopyright (c) 2024 itdojp\n',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.generatedAt).toBe('2026-03-13T00:00:00.000Z');
    expect(audit.gitHeadSha).toBe('1111111111111111111111111111111111111111');
    expect(audit.repositoryLicense).toBe('MIT License');
    expect(audit.packageLicenseField).toBe('MIT');
    expect(audit.trackedFilesSummary.total).toBe(8);
    expect(audit.trackedFilesSummary.firstPartyRoot).toBe(1);
    expect(audit.trackedFilesSummary.firstParty).toBe(1);
    expect(audit.trackedFilesSummary.legalRoot).toBe(1);
    expect(audit.trackedFilesSummary.conditional).toBe(3);
    expect(audit.trackedFilesSummary.other).toBe(2);
    expect(audit.conditionalBreakdown).toEqual({
      artifacts: 1,
      fixtures: 1,
      'test-cassettes': 1,
    });
    expect(audit.nestedNoticeFiles).toEqual(['vendor/NOTICE.txt', 'vendor/LICENSE-MIT']);
    expect(audit.contributorInventory[0]).toEqual({
      commits: 10,
      author: 'Alice <alice@example.com>',
    });
  });

  it('rejects missing gitHeadSha', () => {
    expect(() =>
      buildLicenseScopeAudit({
        trackedFiles: [],
        shortlogText: '',
        packageJson: { license: 'MIT' },
        rootLicenseText: 'MIT License',
      }),
    ).toThrow('gitHeadSha is required');
  });

  it('renders markdown report', () => {
    const markdown = buildMarkdownReport({
      generatedAt: '2026-03-13T00:00:00.000Z',
      gitHeadSha: '1111111111111111111111111111111111111111',
      repositoryLicense: 'MIT License',
      packageLicenseField: 'MIT',
      trackedFilesSummary: {
        total: 7,
        firstParty: 1,
        firstPartyRoot: 1,
        legalRoot: 1,
        conditional: 3,
        other: 1,
      },
      conditionalBreakdown: {
        artifacts: 1,
        fixtures: 1,
        'test-cassettes': 1,
      },
      nestedNoticeFiles: ['LICENSE'],
      contributorInventory: [{ commits: 10, author: 'Alice <alice@example.com>' }],
      otherTrackedFiles: ['vendor/NOTICE.txt'],
    });

    expect(markdown).toContain('# License Migration Audit');
    expect(markdown).toContain('- gitHeadSha: 1111111111111111111111111111111111111111');
    expect(markdown).toContain('- Repository license: MIT License');
    expect(markdown).toContain('- legal root files: 1');
    expect(markdown).toContain('- artifacts: 1');
    expect(markdown).toContain('- 10 Alice <alice@example.com>');
    expect(markdown).toContain('- vendor/NOTICE.txt');
  });

  it('resolves generatedAt from SOURCE_DATE_EPOCH seconds', () => {
    expect(resolveGeneratedAt('0')).toBe('1970-01-01T00:00:00.000Z');
  });

  it('rejects invalid SOURCE_DATE_EPOCH values', () => {
    expect(() => resolveGeneratedAt('2026-03-13')).toThrow(
      'SOURCE_DATE_EPOCH must be an integer number of seconds',
    );
  });

  it('resolves git head sha from the repository', () => {
    expect(resolveGitHeadSha(process.cwd())).toMatch(/^[0-9a-f]{40}$/);
  });
});
