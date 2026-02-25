import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';

import {
  parseArgs,
  runCiDocIndexConsistencyCheck,
} from '../../../scripts/docs/check-ci-doc-index-consistency.mjs';

function withTempRepo(testFn: (rootDir: string) => void): void {
  const rootDir = mkdtempSync(path.join(tmpdir(), 'ae-ci-doc-index-'));
  try {
    testFn(rootDir);
  } finally {
    rmSync(rootDir, { recursive: true, force: true });
  }
}

function writeFile(rootDir: string, relativePath: string, content: string): void {
  const fullPath = path.join(rootDir, relativePath);
  mkdirSync(path.dirname(fullPath), { recursive: true });
  writeFileSync(fullPath, content);
}

function writeBaselineDocs(rootDir: string): void {
  writeFile(rootDir, 'docs/README.md', [
    '# Docs Index',
    '- CI policy: `ci-policy.md`',
    '- Docs Doctest policy: `ci/docs-doctest-policy.md`',
    '- CI operations handbook: `ci/ci-operations-handbook.md`',
    '- CI troubleshooting guide: `ci/ci-troubleshooting-guide.md`',
    '- PR automation: `ci/pr-automation.md`',
    '- Workflow role matrix: `ci/workflow-role-matrix.md`',
    '- Opt-in controls: `ci/OPT-IN-CONTROLS.md`',
    '- CI docs boundary matrix: `ci/ci-doc-boundary-matrix.md`',
  ].join('\n'));

  writeFile(rootDir, 'docs/ci-policy.md', [
    '# CI Policy',
    '### 参考ドキュメント',
    '- docs/ci/docs-doctest-policy.md',
    '- docs/ci/ci-operations-handbook.md',
    '- docs/ci/ci-troubleshooting-guide.md',
    '- docs/ci/pr-automation.md',
    '- docs/ci/workflow-role-matrix.md',
    '- docs/ci/OPT-IN-CONTROLS.md',
    '- docs/ci/ci-doc-boundary-matrix.md',
    '',
    '## 6. 参照',
    '- docs/ci/docs-doctest-policy.md',
    '- docs/ci/ci-operations-handbook.md',
    '- docs/ci/ci-troubleshooting-guide.md',
    '- docs/ci/pr-automation.md',
    '- docs/ci/workflow-role-matrix.md',
    '- docs/ci/OPT-IN-CONTROLS.md',
    '- docs/ci/ci-doc-boundary-matrix.md',
  ].join('\n'));

  const requiredTargets = [
    'docs/ci/docs-doctest-policy.md',
    'docs/ci/ci-operations-handbook.md',
    'docs/ci/ci-troubleshooting-guide.md',
    'docs/ci/pr-automation.md',
    'docs/ci/workflow-role-matrix.md',
    'docs/ci/OPT-IN-CONTROLS.md',
    'docs/ci/ci-doc-boundary-matrix.md',
  ];
  for (const target of requiredTargets) {
    writeFile(rootDir, target, `# ${target}\n`);
  }
}

describe('check-ci-doc-index-consistency', () => {
  it('uses default files when --files is omitted', () => {
    const result = parseArgs(['node', 'check-ci-doc-index-consistency.mjs']);
    expect(result.files).toEqual(['docs/README.md', 'docs/ci-policy.md']);
  });

  it('passes when required links and targets are consistent', () => {
    withTempRepo((rootDir) => {
      writeBaselineDocs(rootDir);

      const result = runCiDocIndexConsistencyCheck([
        'node',
        'check-ci-doc-index-consistency.mjs',
        `--root=${rootDir}`,
      ]);

      expect(result.exitCode).toBe(0);
      expect(result.findings).toHaveLength(0);
    });
  });

  it('reports missing required links', () => {
    withTempRepo((rootDir) => {
      writeBaselineDocs(rootDir);
      writeFile(rootDir, 'docs/README.md', '# Docs Index\n- CI policy: `ci-policy.md`\n');

      const result = runCiDocIndexConsistencyCheck([
        'node',
        'check-ci-doc-index-consistency.mjs',
        `--root=${rootDir}`,
      ]);

      expect(result.exitCode).toBe(1);
      expect(result.findings.some((finding) => finding.code === 'missing_required_link')).toBe(true);
      expect(result.findings.some((finding) => finding.message.includes('ci/pr-automation.md'))).toBe(true);
    });
  });

  it('reports missing target files', () => {
    withTempRepo((rootDir) => {
      writeBaselineDocs(rootDir);
      rmSync(path.join(rootDir, 'docs/ci/pr-automation.md'));

      const result = runCiDocIndexConsistencyCheck([
        'node',
        'check-ci-doc-index-consistency.mjs',
        `--root=${rootDir}`,
      ]);

      expect(result.exitCode).toBe(1);
      expect(result.findings.some((finding) => finding.code === 'missing_required_target')).toBe(true);
      expect(result.findings.some((finding) => finding.message.includes('docs/ci/pr-automation.md'))).toBe(true);
    });
  });

  it('reports duplicate references inside a canonical section', () => {
    withTempRepo((rootDir) => {
      writeBaselineDocs(rootDir);
      writeFile(rootDir, 'docs/ci-policy.md', [
        '# CI Policy',
        '### 参考ドキュメント',
        '- docs/ci/docs-doctest-policy.md',
        '- docs/ci/docs-doctest-policy.md',
        '- docs/ci/ci-operations-handbook.md',
        '- docs/ci/ci-troubleshooting-guide.md',
        '- docs/ci/pr-automation.md',
        '',
        '## 6. 参照',
        '- docs/ci/docs-doctest-policy.md',
        '- docs/ci/ci-operations-handbook.md',
        '- docs/ci/ci-troubleshooting-guide.md',
        '- docs/ci/pr-automation.md',
      ].join('\n'));

      const result = runCiDocIndexConsistencyCheck([
        'node',
        'check-ci-doc-index-consistency.mjs',
        `--root=${rootDir}`,
      ]);

      expect(result.exitCode).toBe(1);
      expect(result.findings.some((finding) => finding.code === 'duplicate_reference')).toBe(true);
    });
  });

  it('reports unknown options', () => {
    withTempRepo((rootDir) => {
      writeBaselineDocs(rootDir);
      const result = runCiDocIndexConsistencyCheck([
        'node',
        'check-ci-doc-index-consistency.mjs',
        `--root=${rootDir}`,
        '--unknown-flag',
      ]);
      expect(result.exitCode).toBe(1);
      expect(result.findings).toEqual([expect.objectContaining({ code: 'unknown_option' })]);
    });
  });
});
