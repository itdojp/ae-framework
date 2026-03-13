import { describe, expect, it } from 'vitest';
import {
  buildThirdPartyNoticeCandidateAudit,
  collectVendoredPathCandidates,
  isNestedNoticeCandidate,
  listSubmodules,
  renderMarkdownReport,
} from '../../scripts/legal/build-third-party-notice-candidate-audit.mjs';
import { mkdtempSync, rmSync, writeFileSync, mkdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';

describe('third-party notice candidate audit', () => {
  it('detects nested legal files outside docs and conditional directories', () => {
    expect(isNestedNoticeCandidate('src/vendor/LICENSE-MIT')).toBe(true);
    expect(isNestedNoticeCandidate('docs/project/LICENSE-MIGRATION-AUDIT.md')).toBe(false);
    expect(isNestedNoticeCandidate('artifacts/reference/legal/LICENSE-THIRD-PARTY.txt')).toBe(false);
    expect(isNestedNoticeCandidate('test-cassettes/provider/LICENSE.txt')).toBe(false);
  });

  it('collects vendored path candidates by exact segment', () => {
    expect(
      collectVendoredPathCandidates([
        'src/vendor/example.ts',
        'src/vendor/README.md',
        'packages/app/external/lib.js',
      ]),
    ).toEqual([
      { path: 'packages/app/external', segment: 'external', sampleFile: 'packages/app/external/lib.js' },
      { path: 'src/vendor', segment: 'vendor', sampleFile: 'src/vendor/example.ts' },
    ]);
  });

  it('builds review-required summary when candidates exist', () => {
    const audit = buildThirdPartyNoticeCandidateAudit({
      trackedFiles: ['src/vendor/example.ts', 'src/vendor/LICENSE-MIT'],
      submodules: [{ path: 'vendor/submodule', url: 'https://example.com/submodule.git' }],
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.gitHeadSha).toBe('1111111111111111111111111111111111111111');
    expect(audit.summary.status).toBe('review-required');
    expect(audit.summary.nestedNoticeFileCount).toBe(1);
    expect(audit.summary.vendoredPathCount).toBe(1);
    expect(audit.summary.submoduleCount).toBe(1);
    expect(audit.review.reasons).toEqual([
      'nested-legal-files-present',
      'vendored-path-candidates-present',
      'submodules-present',
    ]);
  });

  it('renders markdown with escaped table cells', () => {
    const markdown = renderMarkdownReport({
      schemaVersion: 'third-party-notice-candidate-audit/v1',
      generatedAt: '2026-03-13T00:00:00.000Z',
      gitHeadSha: '1111111111111111111111111111111111111111',
      inputs: {
        trackedFilesScanned: 2,
        vendorLikeSegments: ['vendor'],
        nestedNoticePattern: 'pattern',
      },
      summary: {
        nestedNoticeFileCount: 0,
        vendoredPathCount: 1,
        submoduleCount: 0,
        status: 'review-required',
      },
      evidence: {
        nestedNoticeFiles: [],
        vendoredPathCandidates: [
          { path: 'src/vendor', segment: 'vendor', sampleFile: 'src/vendor/a|b.ts' },
        ],
        submodules: [],
      },
      review: {
        requiresIndividualNoticeReview: true,
        reasons: ['vendored-path-candidates-present'],
      },
    });

    expect(markdown).toContain('<code>src/vendor/a|b.ts</code>');
    expect(markdown).toContain('- gitHeadSha: 1111111111111111111111111111111111111111');
    expect(markdown).toContain('<code>src/vendor</code>');
  });

  it('renders backslashes safely inside code cells', () => {
    const markdown = renderMarkdownReport({
      schemaVersion: 'third-party-notice-candidate-audit/v1',
      generatedAt: '2026-03-13T00:00:00.000Z',
      gitHeadSha: '1111111111111111111111111111111111111111',
      inputs: {
        trackedFilesScanned: 1,
        vendorLikeSegments: ['vendor'],
        nestedNoticePattern: 'pattern',
      },
      summary: {
        nestedNoticeFileCount: 1,
        vendoredPathCount: 0,
        submoduleCount: 0,
        status: 'review-required',
      },
      evidence: {
        nestedNoticeFiles: ['vendor\\\\LICENSE'],
        vendoredPathCandidates: [],
        submodules: [],
      },
      review: {
        requiresIndividualNoticeReview: true,
        reasons: ['nested-legal-files-present'],
      },
    });

    expect(markdown).toContain('<code>vendor&#92;&#92;LICENSE</code>');
  });

  it('lists submodules from .gitmodules', () => {
    const root = mkdtempSync(path.join(tmpdir(), 'ae-third-party-submodule-'));
    try {
      execFileSync('git', ['init'], { cwd: root, stdio: 'ignore' });
      writeFileSync(
        path.join(root, '.gitmodules'),
        ['[submodule "vendor/example"]', '\tpath = vendor/example', '\turl = https://example.com/repo.git', ''].join('\n'),
      );
      mkdirSync(path.join(root, 'vendor'), { recursive: true });
      expect(listSubmodules(root)).toEqual([
        { path: 'vendor/example', url: 'https://example.com/repo.git' },
      ]);
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });

  it('fails when .gitmodules exists but cannot be parsed', () => {
    const root = mkdtempSync(path.join(tmpdir(), 'ae-third-party-submodule-invalid-'));
    try {
      execFileSync('git', ['init'], { cwd: root, stdio: 'ignore' });
      writeFileSync(path.join(root, '.gitmodules'), '[submodule "vendor/example"\n\tpath = vendor/example\n');
      expect(() => listSubmodules(root)).toThrow();
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });
});
