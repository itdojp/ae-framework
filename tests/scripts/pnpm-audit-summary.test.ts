import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  parseArgs,
  parseDependencyPath,
  stripPackageVersion,
  summarizePnpmAudit,
} from '../../scripts/security/summarize-pnpm-audit.mjs';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/security/summarize-pnpm-audit.mjs');
const outputDir = resolve(repoRoot, '.codex-local/tmp/pnpm-audit-summary-test');
const fixtureRepoRoot = join(outputDir, 'repo');

function writeJson(filePath: string, payload: unknown) {
  mkdirSync(dirname(filePath), { recursive: true });
  writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`);
}

function resetFixtureRepo() {
  rmSync(outputDir, { recursive: true, force: true });
  mkdirSync(fixtureRepoRoot, { recursive: true });
  writeJson(join(fixtureRepoRoot, 'package.json'), {
    name: 'pnpm-audit-summary-fixture',
    packageManager: 'pnpm@10.0.0',
    dependencies: {
      'fast-xml-parser': '5.2.2',
    },
    devDependencies: {
      vitest: '3.2.4',
    },
  });
  writeJson(join(fixtureRepoRoot, 'apps/storybook/package.json'), {
    name: '@fixture/storybook',
    devDependencies: {
      '@storybook/nextjs': '8.6.14',
    },
  });
}

function sampleAudit() {
  return {
    actions: [
      {
        action: 'update',
        module: 'fast-xml-parser',
        target: '5.2.3',
        depth: 1,
        resolves: [
          {
            id: 100,
            path: '.>fast-xml-parser',
            dev: false,
            optional: false,
            bundled: false,
          },
        ],
      },
      {
        action: 'review',
        module: 'webpack',
        target: null,
        depth: 3,
        resolves: [
          {
            id: 200,
            path: 'apps__storybook>@storybook/nextjs>webpack',
            dev: true,
            optional: false,
            bundled: false,
          },
        ],
      },
    ],
    advisories: {
      100: {
        module_name: 'fast-xml-parser',
        severity: 'critical',
        title: 'critical parser issue',
        vulnerable_versions: '<5.2.3',
        patched_versions: '>=5.2.3',
        recommendation: 'upgrade fast-xml-parser',
        url: 'https://example.com/advisories/100',
        cves: ['CVE-2099-0001'],
        cvss: { score: 9.8 },
        findings: [
          {
            version: '5.2.2',
            paths: ['. > fast-xml-parser@5.2.2'],
          },
        ],
      },
      200: {
        module_name: 'webpack',
        severity: 'high',
        title: 'transitive bundler issue',
        vulnerable_versions: '<5.99.0',
        patched_versions: '>=5.99.0',
        recommendation: 'review storybook chain',
        url: 'https://example.com/advisories/200',
        cves: [],
        cvss: { score: 7.5 },
        findings: [
          {
            version: '5.97.1',
            paths: ['apps/storybook > @storybook/nextjs@8.6.14 > webpack@5.97.1'],
          },
        ],
      },
      300: {
        module_name: 'vitest',
        severity: 'moderate',
        title: 'test runner issue',
        vulnerable_versions: '<3.2.5',
        patched_versions: '>=3.2.5',
        recommendation: 'upgrade vitest',
        url: 'https://example.com/advisories/300',
        cves: [],
        cvss: { score: 5.1 },
        findings: [
          {
            version: '3.2.4',
            paths: ['. > vitest@3.2.4'],
          },
        ],
      },
    },
    metadata: {
      vulnerabilities: {
        critical: 1,
        high: 1,
        moderate: 1,
        low: 0,
      },
      dependencies: 3,
      devDependencies: 2,
      totalDependencies: 5,
    },
  };
}

describe('summarize-pnpm-audit', () => {
  it('parses package names and pnpm path roots without losing scoped names', () => {
    expect(stripPackageVersion('@aws-sdk/client-s3@3.966.0')).toBe('@aws-sdk/client-s3');
    expect(stripPackageVersion('fast-xml-parser@5.2.2')).toBe('fast-xml-parser');
    expect(parseDependencyPath('apps__storybook>@storybook/nextjs>webpack')).toEqual({
      raw: 'apps__storybook>@storybook/nextjs>webpack',
      workspaceRoots: ['apps/storybook'],
      packages: ['@storybook/nextjs', 'webpack'],
    });
  });

  it('classifies audit advisories by directness, exposure, and pnpm action', () => {
    resetFixtureRepo();
    const auditPath = join(fixtureRepoRoot, 'audit.json');
    writeJson(auditPath, sampleAudit());

    const report = summarizePnpmAudit(parseArgs([
      '--repo-root', fixtureRepoRoot,
      '--input', auditPath,
    ]));

    expect(report.schemaVersion).toBe('pnpm-audit-classification/v1');
    expect(report.contractId).toBe('pnpm-audit-classification.v1');
    expect(report.enforcement.mode).toBe('report-only');
    expect(report.enforcement.gateWeakening).toBe(false);
    expect(report.summary.bySeverity).toMatchObject({ critical: 1, high: 1, moderate: 1, low: 0 });
    expect(report.summary.criticalHighUniqueModules).toEqual(['fast-xml-parser', 'webpack']);

    const parser = report.advisories.find((advisory) => advisory.moduleName === 'fast-xml-parser');
    expect(parser).toMatchObject({
      directness: 'direct',
      exposure: 'production',
      remediationStatus: 'update-available',
    });
    expect(parser?.rootDependencies).toEqual([
      {
        name: 'fast-xml-parser',
        manifestRoot: '.',
        section: 'dependencies',
        exposure: 'production',
      },
    ]);

    const webpack = report.advisories.find((advisory) => advisory.moduleName === 'webpack');
    expect(webpack).toMatchObject({
      directness: 'transitive',
      exposure: 'development',
      remediationStatus: 'manual-review',
      workspaceRoots: ['apps/storybook'],
    });
    expect(webpack?.rootDependencies).toEqual([
      {
        name: '@storybook/nextjs',
        manifestRoot: 'apps/storybook',
        section: 'devDependencies',
        exposure: 'development',
      },
    ]);

    const vitest = report.advisories.find((advisory) => advisory.moduleName === 'vitest');
    expect(vitest).toMatchObject({
      directness: 'direct',
      exposure: 'test',
    });
  });

  it('writes JSON and Markdown artifacts without changing gate enforcement', () => {
    resetFixtureRepo();
    const auditPath = join(fixtureRepoRoot, 'audit.json');
    const jsonPath = join(outputDir, 'classification.json');
    const markdownPath = join(outputDir, 'classification.md');
    writeJson(auditPath, sampleAudit());

    const result = spawnSync('node', [
      scriptPath,
      '--repo-root', fixtureRepoRoot,
      '--input', auditPath,
      '--output-json', jsonPath,
      '--output-md', markdownPath,
    ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(existsSync(jsonPath)).toBe(true);
    expect(existsSync(markdownPath)).toBe(true);

    const report = JSON.parse(readFileSync(jsonPath, 'utf8'));
    expect(report.enforcement).toMatchObject({
      mode: 'report-only',
      gateWeakening: false,
    });
    const markdown = readFileSync(markdownPath, 'utf8');
    expect(markdown).toContain('Mode: **report-only**');
    expect(markdown).toContain('Gate weakening: **no**');
    expect(markdown).toContain('| critical | fast-xml-parser | production | direct | .:fast-xml-parser (dependencies) | 1 | >=5.2.3 | update fast-xml-parser -> 5.2.3 |');
  });

  it('rejects pnpm audit error payloads instead of emitting clean-looking evidence', () => {
    resetFixtureRepo();
    const auditPath = join(fixtureRepoRoot, 'audit-error.json');
    writeJson(auditPath, {
      error: {
        code: 'ERR_PNPM_AUDIT_BAD_RESPONSE',
        message: 'registry returned an invalid advisory response',
      },
    });

    expect(() => summarizePnpmAudit(parseArgs([
      '--repo-root', fixtureRepoRoot,
      '--input', auditPath,
    ]))).toThrow(/error payload/);

    const result = spawnSync('node', [
      scriptPath,
      '--repo-root', fixtureRepoRoot,
      '--input', auditPath,
      '--output-json', join(outputDir, 'should-not-exist.json'),
      '--output-md', join(outputDir, 'should-not-exist.md'),
    ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('pnpm audit input is an error payload');
  });
});
