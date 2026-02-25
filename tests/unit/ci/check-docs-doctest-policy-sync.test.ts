import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';

import {
  isExecutedAsMain,
  main,
  runDocsDoctestPolicySyncCheck,
} from '../../../scripts/ci/check-docs-doctest-policy-sync.mjs';

function withTempDir(fn: (dir: string) => void): void {
  const dir = mkdtempSync(path.join(tmpdir(), 'ae-docs-doctest-sync-'));
  try {
    fn(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function writeFixtureFiles(dir: string, packageRaw = '{"scripts":{}}') {
  const workflowPath = path.join(dir, 'docs-doctest.yml');
  const packagePath = path.join(dir, 'package.json');
  const policyPath = path.join(dir, 'docs-doctest-policy.md');

  const workflow = [
    'jobs:',
    '  doctest-index:',
    "    if: ${{ github.event_name != 'schedule' }}",
    '    steps:',
    '      - name: Detect changed markdown files (PR only)',
    '        run: |',
    '          git fetch --no-tags --depth=1 origin "${BASE_SHA}"',
    "          git diff --name-only \"${BASE_SHA}\" HEAD -- '*.md' '**/*.md'",
    "    if: ${{ github.event_name == 'pull_request' && steps.changed-docs.outputs.files != '' }}",
    "      - 'scripts/ci/check-docs-doctest-policy-sync.mjs'",
    "      - 'scripts/ci/check-docs-doctest-policy-sync.mjs'",
  ].join('\n');

  const policy = [
    '# Docs Doctest Policy',
    '',
    '差分 Markdown を pull_request で検証する。',
    'workflow_dispatch(full=true) で full 実行できる。',
  ].join('\n');

  writeFileSync(workflowPath, workflow);
  writeFileSync(packagePath, packageRaw);
  writeFileSync(policyPath, policy);

  return { workflowPath, packagePath, policyPath };
}

describe('check-docs-doctest-policy-sync', () => {
  it('passes when workflow/package/policy are aligned', () => {
    withTempDir((dir) => {
      const packageRaw = JSON.stringify({
        scripts: {
          'test:doctest:index': "tsx scripts/doctest.ts '{README.md,docs/README.md}'",
          'test:doctest:full': "tsx scripts/doctest.ts 'docs/**/*.md'",
        },
      });
      const paths = writeFixtureFiles(dir, packageRaw);

      const result = runDocsDoctestPolicySyncCheck(paths);
      expect(result.exitCode).toBe(0);
      expect(result.errors).toHaveLength(0);
    });
  });

  it('reports missing required snippets as validation errors', () => {
    withTempDir((dir) => {
      const packageRaw = JSON.stringify({
        scripts: {
          'test:doctest:index': 'tsx scripts/doctest.ts README.md',
        },
      });
      const paths = writeFixtureFiles(dir, packageRaw);

      const result = runDocsDoctestPolicySyncCheck(paths);
      expect(result.exitCode).toBe(1);
      expect(result.errors.some((error) => error.includes('test:doctest:index must include'))).toBe(true);
      expect(result.errors.some((error) => error.includes('scripts.test:doctest:full is missing'))).toBe(true);
    });
  });

  it('returns clear read error when a required file is missing', () => {
    withTempDir((dir) => {
      const paths = writeFixtureFiles(dir);
      rmSync(paths.policyPath, { force: true });

      const result = main(paths);
      expect(result.exitCode).toBe(1);
      expect(result.errors[0]).toContain('failed to read');
      expect(result.errors[0]).toContain('docs-doctest-policy.md');
    });
  });

  it('returns clear parse error when package json is invalid', () => {
    withTempDir((dir) => {
      const paths = writeFixtureFiles(dir, '{invalid-json');

      const result = main(paths);
      expect(result.exitCode).toBe(1);
      expect(result.errors[0]).toContain('invalid JSON in');
      expect(result.errors[0]).toContain('package.json');
    });
  });

  it('treats URL-escaped module path and argv path as the same file', () => {
    const metaUrl = 'file:///tmp/with%20space/check-docs-doctest-policy-sync.mjs';
    const argvPath = '/tmp/with space/check-docs-doctest-policy-sync.mjs';
    expect(isExecutedAsMain(metaUrl, argvPath)).toBe(true);
  });
});
