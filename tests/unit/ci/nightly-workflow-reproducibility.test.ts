import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, expect, it } from 'vitest';
import YAML from 'yaml';

const repoRoot = process.cwd();

const readText = (relativePath: string) => readFileSync(resolve(repoRoot, relativePath), 'utf8');

describe('Nightly Matrix dependency reproducibility', () => {
  it('pins one pnpm version and makes the repository lockfile config authoritative', () => {
    const packageJson = JSON.parse(readText('package.json'));
    const npmrc = readText('.npmrc');
    const setupAction = YAML.parse(readText('.github/actions/setup-node-pnpm/action.yml'));
    const workflow = YAML.parse(readText('.github/workflows/nightly.yml'));

    expect(packageJson.packageManager).toBe('pnpm@10.0.0');
    expect(setupAction.inputs['pnpm-version'].default).toBe('10.0.0');
    expect(npmrc).toContain('lockfile=true');
    expect(npmrc).not.toContain('use-lockfile=');
    expect(workflow.env.NPM_CONFIG_USERCONFIG).toBe('${{ github.workspace }}/.npmrc');
  });

  it('keeps every nightly install frozen and exposes the effective lockfile setting', () => {
    const workflowText = readText('.github/workflows/nightly.yml');
    const workflow = YAML.parse(workflowText);

    expect(workflowText).not.toContain('--no-frozen-lockfile');
    expect(workflow.jobs['matrix-test'].strategy['fail-fast']).toBe(false);

    for (const jobName of ['matrix-test', 'perf', 'monitor']) {
      const steps = workflow.jobs[jobName].steps as Array<Record<string, unknown>>;
      const authority = steps.find((step) => step.name === 'Confirm lockfile authority');
      const install = steps.find((step) => step.name === 'Install (frozen lockfile)' || step.name === 'Install');
      expect(authority?.run).toContain('pnpm config get lockfile');
      expect(authority?.run).toContain('test "$(pnpm config get lockfile)" = "true"');
      expect(install?.run).toBe('pnpm install --frozen-lockfile');
    }
  });

  it('uses the legacy compatibility CLI that owns qa:flake', () => {
    const workflow = YAML.parse(readText('.github/workflows/nightly.yml'));
    const monitorSteps = workflow.jobs.monitor.steps as Array<Record<string, unknown>>;
    const flake = monitorSteps.find((step) => step.name === 'Flake (30x)');

    expect(flake?.run).toContain('node dist/src/cli.js qa:flake');
    expect(flake?.run).toContain('--pattern "tests/unit/**/*.test.ts"');
    expect(flake?.run).not.toContain('dist/src/cli/index.js qa:flake');
    expect(flake?.run).not.toContain('--pattern "tests/**"');
  });
});
