import { execFileSync } from 'node:child_process';
import { readFileSync, rmSync } from 'node:fs';
import path from 'node:path';
import { beforeAll, describe, expect, it } from 'vitest';

const repoRoot = process.cwd();
const reportPath = path.join(repoRoot, '.codex-local', 'tmp', 'profile-dogfood-test-report.json');
const reportMdPath = path.join(repoRoot, '.codex-local', 'tmp', 'profile-dogfood-test-report.md');
let buildDogfoodReport: typeof import('../../scripts/profiles/dogfood-ci-profiles.mjs').buildDogfoodReport;
let renderMarkdown: typeof import('../../scripts/profiles/dogfood-ci-profiles.mjs').renderMarkdown;
let parseCli: typeof import('../../scripts/profiles/dogfood-ci-profiles.mjs').parseCli;

beforeAll(async () => {
  execFileSync('pnpm', ['--filter', '@ae-framework/core', 'run', 'build'], {
    cwd: repoRoot,
    stdio: 'pipe',
  });
  ({ buildDogfoodReport, renderMarkdown, parseCli } = await import('../../scripts/profiles/dogfood-ci-profiles.mjs'));
});

describe('deploy-time profile dogfood replay', () => {
  it('compares all deploy-time profiles against the 20-case fixture without drift', async () => {
    const report = await buildDogfoodReport({ generatedAt: '2026-07-04T00:00:00.000Z' });

    expect(report.status).toBe('pass');
    expect(report.fixture.caseCount).toBeGreaterThanOrEqual(20);
    expect(report.fixture.mode).toBe('documented-fixture-equivalent');
    expect(report.summary).toMatchObject({ profileCount: 3, replayCoverageCount: 20, driftCount: 0 });
    expect(report.ciProfileMapping).toEqual({
      verifyLite: 'minimal',
      currentPrVerification: 'standard',
      nightlyAndLabelGatedHeavyLanes: 'full',
    });

    const minimal = report.profiles.find((profile) => profile.profileId === 'minimal');
    const standard = report.profiles.find((profile) => profile.profileId === 'standard');
    const full = report.profiles.find((profile) => profile.profileId === 'full');
    expect(minimal?.requiredChecks).toEqual(['gate', 'policy-gate', 'verify-lite']);
    expect(standard?.activeLanes).toContain('context-pack-validation');
    expect(full?.activeLanes).toContain('formal-tla');
    expect(full?.summary).toMatchObject({ caseCount: 20, driftCount: 0 });
  });

  it('keeps pnpm-style argument separators from becoming positionals', () => {
    expect(parseCli(['--', '--profile', 'minimal', '--no-write']).profile).toBe('minimal');
  });

  it('renders a human-readable drift-free report', async () => {
    const report = await buildDogfoodReport({ profile: 'full', generatedAt: '2026-07-04T00:00:00.000Z' });
    const markdown = renderMarkdown(report);
    expect(markdown).toContain('Deploy-time profile dogfood report');
    expect(markdown).toContain('| full | High-assurance critical core |');
    expect(markdown).toContain('No drift detected in replay fixture.');
  });

  it('exposes the replay through the package script', () => {
    rmSync(reportPath, { force: true });
    rmSync(reportMdPath, { force: true });
    const output = execFileSync('pnpm', [
      '-s',
      'run',
      'profiles:dogfood',
      '--',
      '--profile',
      'minimal',
      '--out',
      reportPath,
      '--out-md',
      reportMdPath,
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });
    expect(output).toContain('profile dogfood: pass');
    const report = JSON.parse(readFileSync(reportPath, 'utf8'));
    expect(report.summary).toMatchObject({ profileCount: 1, replayCoverageCount: 20, driftCount: 0 });
  });

  it('wires the local verify-lite path to the minimal deploy-time profile dogfood run', () => {
    const runner = readFileSync(path.join(repoRoot, 'scripts/ci/run-verify-lite-local.sh'), 'utf8');
    expect(runner).toContain('pnpm -s run profiles:dogfood');
    expect(runner).toContain('    -- \\');
    expect(runner).toContain('${VERIFY_LITE_PROFILE_DOGFOOD_PROFILE:-minimal}');

    const packageJson = JSON.parse(readFileSync(path.join(repoRoot, 'package.json'), 'utf8'));
    expect(packageJson.scripts['profiles:dogfood']).toContain('pnpm --filter @ae-framework/core -s run build');
  });
});
