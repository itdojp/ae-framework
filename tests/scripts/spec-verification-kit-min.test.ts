import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { describe, expect, it } from 'vitest';

import {
  buildActivationSummary,
  discoverProfile,
  parseArgs,
} from '../../scripts/spec-verification/run-min-profile.mjs';

const generatedAt = '2026-07-01T00:00:00.000Z';
const exampleRoot = 'examples/spec-verification-kit-min';

describe('Spec & Verification Kit minimum activation profile', () => {
  it('discovers traceable BDD, property, and requirement fragments in the runnable example', () => {
    const profile = discoverProfile(exampleRoot);

    expect(profile.requirements).toEqual([
      {
        id: 'REQ-SVK-001',
        title: 'Activation profile preserves a positive reservation quantity',
        path: 'requirements/minimum-profile.requirements.json',
      },
    ]);
    expect(profile.featureFiles).toEqual(['spec/bdd/features/minimum-profile.feature']);
    expect(profile.stepFiles).toEqual(['spec/bdd/steps/minimum-profile.steps.js']);
    expect(profile.propertyFiles).toEqual(['tests/property/minimum-profile.property.test.ts']);
    expect(profile.traceLinks).toEqual(expect.arrayContaining([
      { traceRef: 'REQ-SVK-001', path: 'requirements/minimum-profile.requirements.json' },
      { traceRef: 'REQ-SVK-001', path: 'spec/bdd/features/minimum-profile.feature' },
      { traceRef: 'REQ-SVK-001', path: 'tests/property/minimum-profile.property.test.ts' },
    ]));
  });

  it('reports custom suite discovery separately from the built-in property smoke in dry-run mode', () => {
    const summary = buildActivationSummary(parseArgs([
      'node',
      'scripts/spec-verification/run-min-profile.mjs',
      '--profile-root',
      exampleRoot,
      '--dry-run',
      '--generated-at',
      generatedAt,
    ]));

    expect(summary.result).toBe('warning');
    expect(summary.generatedAt).toBe(generatedAt);
    expect(summary.checks.find((check) => check.id === 'property-smoke')).toMatchObject({
      status: 'skipped',
      kind: 'built-in-harness',
      traceRefs: ['REQ-SVK-001'],
    });
    expect(summary.checks.find((check) => check.id === 'bdd-custom')).toMatchObject({
      status: 'warning',
      message: expect.stringContaining('Custom suite discovered but not executed'),
    });
    expect(summary.checks.find((check) => check.id === 'property-custom')).toMatchObject({
      status: 'warning',
      files: ['tests/property/minimum-profile.property.test.ts'],
      command: expect.stringContaining(resolve(exampleRoot, 'tests/property/minimum-profile.property.test.ts')),
    });
    expect(summary.distinctions.customPropertySuites).toContain('property-custom');
  });

  it('does not traverse symlinked profile directories or register TypeScript Cucumber steps without a loader', () => {
    const root = resolve('.codex-local/tmp');
    mkdirSync(root, { recursive: true });
    const sandbox = mkdtempSync(join(root, 'spec-kit-min-symlink-'));
    const workRoot = join(sandbox, 'work');
    const outsideRoot = join(sandbox, 'outside');
    mkdirSync(join(workRoot, 'tests'), { recursive: true });
    mkdirSync(join(outsideRoot, 'property'), { recursive: true });
    writeFileSync(join(outsideRoot, 'property', 'outside.property.test.ts'), '// @trace:OUTSIDE\n', 'utf8');
    try {
      symlinkSync(join(outsideRoot, 'property'), join(workRoot, 'tests', 'property'), 'dir');
    } catch {
      rmSync(sandbox, { recursive: true, force: true });
      return;
    }

    try {
      expect(discoverProfile(workRoot).propertyFiles).toEqual([]);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }

    const repoProfile = discoverProfile('.');
    expect(repoProfile.stepFiles.some((filePath) => filePath.endsWith('.ts'))).toBe(false);
  });

  it('rejects activation profile and output paths outside the current workspace', () => {
    expect(() => parseArgs([
      'node',
      'scripts/spec-verification/run-min-profile.mjs',
      '--profile-root',
      '../outside-profile',
      '--dry-run',
    ])).toThrow(/--profile-root must stay within the current workspace/);

    expect(() => parseArgs([
      'node',
      'scripts/spec-verification/run-min-profile.mjs',
      '--output-json',
      '../activation-summary.json',
      '--dry-run',
    ])).toThrow(/--output-json must stay within the current workspace/);

    expect(() => parseArgs([
      'node',
      'scripts/spec-verification/run-min-profile.mjs',
      '--property-output',
      '../property-summary.json',
      '--dry-run',
    ])).toThrow(/--property-output must stay within the current workspace/);
  });

  it('runs the example BDD and property suites and writes activation artifacts', () => {
    const outputRoot = resolve('.codex-local/tmp/spec-kit-min-test');
    const outputJson = `${outputRoot}/activation-summary.json`;
    const outputMd = `${outputRoot}/activation-summary.md`;
    rmSync(outputRoot, { recursive: true, force: true });

    const result = spawnSync('node', [
      'scripts/spec-verification/run-min-profile.mjs',
      '--profile-root',
      exampleRoot,
      '--run-custom-suites',
      '--skip',
      'lint',
      '--skip',
      'types',
      '--skip',
      'fast',
      '--skip',
      'property-smoke',
      '--output-json',
      outputJson,
      '--output-md',
      outputMd,
      '--generated-at',
      generatedAt,
    ], { cwd: resolve('.'), encoding: 'utf8', timeout: 120_000 });

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(existsSync(outputJson)).toBe(true);
    expect(existsSync(outputMd)).toBe(true);
    const summary = JSON.parse(readFileSync(outputJson, 'utf8'));
    expect(summary).toMatchObject({
      schemaVersion: 'spec-verification-kit-min-run/v1',
      generatedAt,
      result: 'pass',
    });
    expect(summary.checks.find((check: { id: string }) => check.id === 'bdd-custom')).toMatchObject({ status: 'pass' });
    expect(summary.checks.find((check: { id: string }) => check.id === 'property-custom')).toMatchObject({ status: 'pass' });
    expect(readFileSync(outputMd, 'utf8')).toContain('REQ-SVK-001');

    rmSync(outputRoot, { recursive: true, force: true });
  });
});
