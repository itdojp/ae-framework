import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';

import {
  REQUIRED_WORKFLOW_PATHS,
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

type WorkflowFixtureOptions = {
  paths?: string[];
  indexIf?: string;
  fullIf?: string;
  includeIndexSyncStep?: boolean;
  includeFullSyncStep?: boolean;
  includeChangedDocsStep?: boolean;
  includeChangedDocsRunStep?: boolean;
  changedDocsStepId?: string;
};

function createWorkflowYaml(options: WorkflowFixtureOptions = {}): string {
  const {
    paths = REQUIRED_WORKFLOW_PATHS,
    indexIf = "${{ github.event_name != 'schedule' }}",
    fullIf = "${{ github.event_name == 'schedule' || (github.event_name == 'workflow_dispatch' && inputs.full) }}",
    includeIndexSyncStep = true,
    includeFullSyncStep = true,
    includeChangedDocsStep = true,
    includeChangedDocsRunStep = true,
    changedDocsStepId = 'changed-docs',
  } = options;
  const pathLines = paths.map((entry) => `      - '${entry}'`);
  const indexSteps: string[] = [];
  const fullSteps: string[] = [];

  indexSteps.push('      - name: Install dependencies');
  indexSteps.push('        run: pnpm install --frozen-lockfile || pnpm install --no-frozen-lockfile');
  if (includeIndexSyncStep) {
    indexSteps.push('      - name: Validate docs-doctest policy sync');
    indexSteps.push('        run: node scripts/ci/check-docs-doctest-policy-sync.mjs');
  }
  if (includeChangedDocsStep) {
    indexSteps.push('      - name: Detect changed markdown files (PR only)');
    indexSteps.push(`        id: ${changedDocsStepId}`);
    indexSteps.push('        if: "${{ github.event_name == \'pull_request\' }}"');
    indexSteps.push('        run: |');
    indexSteps.push('          git fetch --no-tags --depth=1 origin "${BASE_SHA}"');
    indexSteps.push("          git diff --name-only \"${BASE_SHA}\" HEAD -- '*.md' '**/*.md'");
  }
  if (includeChangedDocsRunStep) {
    indexSteps.push('      - name: Run doctest (changed markdown in PR)');
    indexSteps.push(
      "        if: \"${{ github.event_name == 'pull_request' && steps.changed-docs.outputs.files != '' }}\""
    );
    indexSteps.push('        run: xargs -0 pnpm -s tsx scripts/doctest.ts');
  }

  fullSteps.push('      - name: Install dependencies');
  fullSteps.push('        run: pnpm install --frozen-lockfile || pnpm install --no-frozen-lockfile');
  if (includeFullSyncStep) {
    fullSteps.push('      - name: Validate docs-doctest policy sync');
    fullSteps.push('        run: node scripts/ci/check-docs-doctest-policy-sync.mjs');
  }

  return [
    'name: Docs Doctest',
    'on:',
    '  pull_request:',
    '    paths:',
    ...pathLines,
    '  push:',
    '    paths:',
    ...pathLines,
    '  workflow_dispatch:',
    '    inputs:',
    '      full:',
    '        required: false',
    '        type: boolean',
    'jobs:',
    '  doctest-index:',
    `    if: "${indexIf}"`,
    '    steps:',
    ...indexSteps,
    '  doctest-full:',
    `    if: "${fullIf}"`,
    '    steps:',
    ...fullSteps,
  ].join('\n');
}

function writeFixtureFiles(dir: string, packageRaw = '{"scripts":{}}', workflowRaw = createWorkflowYaml()) {
  const workflowPath = path.join(dir, 'docs-doctest.yml');
  const packagePath = path.join(dir, 'package.json');
  const policyPath = path.join(dir, 'docs-doctest-policy.md');

  const policy = [
    '# Docs Doctest Policy',
    '',
    '差分 Markdown を pull_request で検証する。',
    'workflow_dispatch(full=true) で full 実行できる。',
    '',
    '## 失敗時の対応手順（runbook）',
    '',
    '`node scripts/ci/check-docs-doctest-policy-sync.mjs` を実行して同期状態を確認する。',
  ].join('\n');

  writeFileSync(workflowPath, workflowRaw);
  writeFileSync(packagePath, packageRaw);
  writeFileSync(policyPath, policy);

  return { workflowPath, packagePath, policyPath };
}

function defaultPackageRaw() {
  return JSON.stringify({
    scripts: {
      'test:doctest:index': "tsx scripts/doctest.ts '{README.md,docs/README.md}'",
      'test:doctest:full': "tsx scripts/doctest.ts 'docs/**/*.md'",
    },
  });
}

describe('check-docs-doctest-policy-sync', () => {
  it('passes when workflow/package/policy are aligned', () => {
    withTempDir((dir) => {
      const paths = writeFixtureFiles(dir, defaultPackageRaw());

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
      expect(result.errors.some((error) => error.includes('docs/README.md target'))).toBe(true);
      expect(result.errors.some((error) => error.includes('scripts.test:doctest:full is missing'))).toBe(true);
    });
  });

  it('does not treat docs/README.md only as root README.md target', () => {
    withTempDir((dir) => {
      const packageRaw = JSON.stringify({
        scripts: {
          'test:doctest:index': "tsx scripts/doctest.ts 'docs/README.md'",
          'test:doctest:full': "tsx scripts/doctest.ts 'docs/**/*.md'",
        },
      });
      const paths = writeFixtureFiles(dir, packageRaw);

      const result = runDocsDoctestPolicySyncCheck(paths);
      expect(result.exitCode).toBe(1);
      expect(result.errors.some((error) => error.includes('README.md target'))).toBe(true);
    });
  });

  it('reports missing workflow path entries as validation errors', () => {
    withTempDir((dir) => {
      const paths = writeFixtureFiles(
        dir,
        defaultPackageRaw(),
        createWorkflowYaml({
          paths: REQUIRED_WORKFLOW_PATHS.filter((entry) => entry !== 'pnpm-lock.yaml'),
        })
      );

      const result = runDocsDoctestPolicySyncCheck(paths);
      expect(result.exitCode).toBe(1);
      expect(result.errors.some((error) => error.includes('on.pull_request.paths'))).toBe(true);
      expect(result.errors.some((error) => error.includes('pnpm-lock.yaml'))).toBe(true);
    });
  });

  it('reports job condition mismatches as validation errors', () => {
    withTempDir((dir) => {
      const paths = writeFixtureFiles(
        dir,
        defaultPackageRaw(),
        createWorkflowYaml({
          indexIf: "${{ github.event_name == 'schedule' }}",
        })
      );

      const result = runDocsDoctestPolicySyncCheck(paths);
      expect(result.exitCode).toBe(1);
      expect(result.errors.some((error) => error.includes('jobs.doctest-index.if mismatch'))).toBe(true);
    });
  });

  it('reports missing changed-docs step as validation errors', () => {
    withTempDir((dir) => {
      const paths = writeFixtureFiles(
        dir,
        defaultPackageRaw(),
        createWorkflowYaml({
          includeChangedDocsStep: false,
        })
      );

      const result = runDocsDoctestPolicySyncCheck(paths);
      expect(result.exitCode).toBe(1);
      expect(
        result.errors.some((error) =>
          error.includes('doctest-index must include "Detect changed markdown files (PR only)" step')
        )
      ).toBe(true);
    });
  });

  it('reports changed-docs id mismatch as validation errors', () => {
    withTempDir((dir) => {
      const paths = writeFixtureFiles(
        dir,
        defaultPackageRaw(),
        createWorkflowYaml({
          changedDocsStepId: 'changed-markdown',
        })
      );

      const result = runDocsDoctestPolicySyncCheck(paths);
      expect(result.exitCode).toBe(1);
      expect(result.errors.some((error) => error.includes('changed-docs step id mismatch'))).toBe(true);
    });
  });

  it('reports invalid YAML clearly when workflow file is malformed', () => {
    withTempDir((dir) => {
      const paths = writeFixtureFiles(
        dir,
        defaultPackageRaw(),
        'on:\n  pull_request:\n    paths:\n      - "README.md"\n  :'
      );

      const result = main(paths);
      expect(result.exitCode).toBe(1);
      expect(result.errors[0]).toContain('invalid YAML in');
      expect(result.errors[0]).toContain('docs-doctest.yml');
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

  it('returns clear read error when package json is missing', () => {
    withTempDir((dir) => {
      const paths = writeFixtureFiles(dir, defaultPackageRaw());
      rmSync(paths.packagePath, { force: true });

      const result = main(paths);
      expect(result.exitCode).toBe(1);
      expect(result.errors[0]).toContain('failed to read');
      expect(result.errors[0]).toContain('package.json');
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
