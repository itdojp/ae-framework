import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';

const scriptPath = path.resolve(process.cwd(), 'scripts/admin/validate-branch-protection-inputs.mjs');
const tmpRoot = path.resolve(process.cwd(), '.codex-local/tmp');
const tmpRoots: string[] = [];

const makeGithubOutputPath = () => {
  const root = tmpRoot;
  fs.mkdirSync(root, { recursive: true });
  const dir = fs.mkdtempSync(path.join(root, 'branch-protection-'));
  tmpRoots.push(dir);
  return path.join(dir, 'github-output.txt');
};

const runValidator = (env: Record<string, string>) => {
  const githubOutput = makeGithubOutputPath();
  const result = spawnSync(process.execPath, [scriptPath], {
    cwd: process.cwd(),
    env: {
      ...process.env,
      GITHUB_OUTPUT: githubOutput,
      GITHUB_REPOSITORY: 'itdojp/ae-framework',
      BRANCH_PROTECTION_BRANCH: 'main',
      BRANCH_PROTECTION_PRESET: 'branch-protection.main.require-verify-lite-gate.json',
      BRANCH_PROTECTION_EMERGENCY_APPROVAL: 'normal-change',
      ...env,
    },
    encoding: 'utf8',
  });
  const output = fs.existsSync(githubOutput) ? fs.readFileSync(githubOutput, 'utf8') : '';
  return { ...result, githubOutput: output };
};

afterEach(() => {
  for (const root of tmpRoots.splice(0)) {
    fs.rmSync(root, { recursive: true, force: true });
  }
  fs.rmSync(path.resolve(process.cwd(), '.codex-local'), { recursive: true, force: true });
});

describe('validate-branch-protection-inputs', () => {
  it('accepts the safe default main preset and emits sanitized workflow outputs', () => {
    const result = runValidator({});

    expect(result.status).toBe(0);
    expect(result.stdout).toContain('Validated branch-protection preset: branch-protection.main.require-verify-lite-gate.json');
    expect(result.githubOutput).toContain('branch=main\n');
    expect(result.githubOutput).toContain('preset=branch-protection.main.require-verify-lite-gate.json\n');
    expect(result.githubOutput).toContain('preset_path=.github/branch-protection.main.require-verify-lite-gate.json\n');
    expect(result.githubOutput).toContain('api_path=repos/itdojp/ae-framework/branches/main/protection\n');
    expect(result.githubOutput).toContain('emergency=false\n');
  });

  it('rejects non-allowlisted branches and preset traversal before producing admin API paths', () => {
    const badBranch = runValidator({ BRANCH_PROTECTION_BRANCH: 'release' });
    expect(badBranch.status).not.toBe(0);
    expect(badBranch.stderr).toContain('Branch is not allowlisted');
    expect(badBranch.githubOutput).toBe('');

    const traversal = runValidator({ BRANCH_PROTECTION_PRESET: '../branch-protection.main.relax2.json' });
    expect(traversal.status).not.toBe(0);
    expect(traversal.stderr).toContain('Preset is not allowlisted');
    expect(traversal.githubOutput).toBe('');
  });

  it('allows restore without break-glass because it tightens branch protection', () => {
    const result = runValidator({ BRANCH_PROTECTION_PRESET: 'branch-protection.main.restore.json' });

    expect(result.status).toBe(0);
    expect(result.githubOutput).toContain('preset=branch-protection.main.restore.json\n');
    expect(result.githubOutput).toContain('emergency=false\n');
  });

  it('requires explicit break-glass approval for presets that relax review or check gates', () => {
    const withoutApproval = runValidator({
      BRANCH_PROTECTION_PRESET: 'branch-protection.main.relax2.json',
      BRANCH_PROTECTION_EMERGENCY_APPROVAL: 'normal-change',
    });
    expect(withoutApproval.status).not.toBe(0);
    expect(withoutApproval.stderr).toContain('requires BRANCH_PROTECTION_EMERGENCY_APPROVAL=approved-break-glass');
    expect(withoutApproval.githubOutput).toBe('');

    const withApproval = runValidator({
      BRANCH_PROTECTION_PRESET: 'branch-protection.main.relax2.json',
      BRANCH_PROTECTION_EMERGENCY_APPROVAL: 'approved-break-glass',
    });
    expect(withApproval.status).toBe(0);
    expect(withApproval.githubOutput).toContain('preset=branch-protection.main.relax2.json\n');
    expect(withApproval.githubOutput).toContain('emergency=true\n');
  });
});
