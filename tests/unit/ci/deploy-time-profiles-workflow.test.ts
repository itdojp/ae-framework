import fs from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import yaml from 'js-yaml';

const repoRoot = process.cwd();
const workflowPath = path.join(repoRoot, '.github/workflows/deploy-time-profiles.yml');
const branchProtectionPresetPaths = [
  '.github/branch-protection.main.require-verify-lite-gate.json',
  '.github/branch-protection.main.verify-lite-noreview.json',
  '.github/branch-protection.main.verify-lite-trace-noreview.json',
].map((presetPath) => path.join(repoRoot, presetPath));

describe('deploy-time profiles required check workflow', () => {
  it('emits a stable required check while path-filtering all-profile replay inside the job', () => {
    const raw = fs.readFileSync(workflowPath, 'utf8');
    const workflow = yaml.load(raw) as any;
    const job = workflow.jobs?.['deploy-time-profiles'];

    expect(job?.name).toBe('deploy-time-profiles');
    expect(raw).toContain('should_run=false');
    expect(raw).toContain('matches_profile_trigger_path()');
    expect(raw).toContain('local profile_prefixes=(');
    expect(raw).toContain('"packages/core/"');
    expect(raw).toContain('"profiles/"');
    expect(raw).toContain('"fixtures/profiles/dogfood/"');
    expect(raw).toContain('".github/actions/assurance-gate/"');
    expect(raw).toContain('"scripts/profiles/"');
    expect(raw).toContain('[[ "$changed_file" == "$profile_prefix"* ]]');
    expect(raw).toContain('action.yml|schema/assurance-profile.schema.json');
    expect(raw).toContain('scripts/actions/assurance-gate.mjs');
    expect(raw).toContain('.github/workflows/deploy-time-profiles.yml');
    expect(raw).toContain('.github/branch-protection.main.verify-lite-trace-noreview.json)');
    expect(raw).not.toContain('packages/core/*) return 0');
    expect(raw).toContain('git merge-base "$base_sha" "$head_sha"');
    expect(raw).toContain('git diff --name-only -z "$diff_base_sha" "$head_sha"');
    expect(raw).toContain('pnpm -s run profiles:dogfood -- \\');
    expect(raw).toContain('--profile all');
    expect(raw).toContain('report.summary?.profileCount !== 3');

    // The workflow must not use top-level pull_request.paths because branch protection
    // requires the check context to be emitted for every PR, even when the expensive
    // all-profile replay is skipped inside the job.
    expect(workflow.on?.pull_request?.paths).toBeUndefined();
    expect(raw).not.toContain('      - packages/core/**');
  });

  it('names the deploy-time profile check in branch-protection presets that keep gate required', () => {
    for (const presetPath of branchProtectionPresetPaths) {
      const protection = JSON.parse(fs.readFileSync(presetPath, 'utf8'));
      expect(protection.required_status_checks.contexts).toContain('deploy-time-profiles');
    }
  });
});
