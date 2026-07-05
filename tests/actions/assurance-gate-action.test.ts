import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { beforeAll, describe, expect, it } from 'vitest';

const repoRoot = process.cwd();
const tmpRoot = path.join(repoRoot, '.codex-local', 'tmp', 'assurance-gate-action-tests');

function resetWorkspace(name: string): string {
  const workspace = path.join(tmpRoot, name);
  rmSync(workspace, { recursive: true, force: true });
  mkdirSync(path.join(workspace, 'artifacts'), { recursive: true });
  return workspace;
}

beforeAll(() => {
  mkdirSync(tmpRoot, { recursive: true });
  execFileSync('pnpm', ['--filter', '@ae-framework/core', 'run', 'build'], {
    cwd: repoRoot,
    stdio: 'pipe',
  });
});

describe('assurance-gate action runner', () => {
  it('resolves the action repository from a root action path', () => {
    const workspace = resetWorkspace('root-action-path');
    writeFileSync(path.join(workspace, 'artifacts', 'evidence.json'), `${JSON.stringify({
      evidence: [
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'spec',
          kind: 'schema',
          sourceKind: 'spec-derived',
          origin: 'fixture-schema',
        },
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'behavior',
          kind: 'integration',
          sourceKind: 'runtime-derived',
          origin: 'fixture-integration',
        },
      ],
      policyEvidence: ['postDeployVerify', 'qualityGates'],
    }, null, 2)}\n`);

    const result = spawnSync('node', [
      'scripts/actions/assurance-gate.mjs',
      '--workspace', workspace,
      '--profile', 'minimal',
      '--artifacts-dir', 'artifacts',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 30_000,
      env: { ...process.env, GITHUB_ACTION_PATH: repoRoot },
    });

    expect(result.stderr).toBe('');
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('ae-framework assurance gate: pass');
  });

  it('resolves the action repository from the compatibility subdirectory action path', () => {
    const workspace = resetWorkspace('subdirectory-action-path');
    writeFileSync(path.join(workspace, 'artifacts', 'evidence.json'), `${JSON.stringify({
      evidence: [
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'spec',
          kind: 'schema',
          sourceKind: 'spec-derived',
          origin: 'fixture-schema',
        },
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'behavior',
          kind: 'integration',
          sourceKind: 'runtime-derived',
          origin: 'fixture-integration',
        },
      ],
      policyEvidence: ['postDeployVerify', 'qualityGates'],
    }, null, 2)}\n`);

    const result = spawnSync('node', [
      'scripts/actions/assurance-gate.mjs',
      '--workspace', workspace,
      '--profile', 'minimal',
      '--artifacts-dir', 'artifacts',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 30_000,
      env: { ...process.env, GITHUB_ACTION_PATH: path.join(repoRoot, '.github/actions/assurance-gate') },
    });

    expect(result.stderr).toBe('');
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('ae-framework assurance gate: pass');
  });

  it('runs the minimal profile against a bare non-workspace fixture', () => {
    const workspace = resetWorkspace('minimal-pass');
    writeFileSync(path.join(workspace, 'artifacts', 'evidence.json'), `${JSON.stringify({
      evidence: [
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'spec',
          kind: 'schema',
          sourceKind: 'spec-derived',
          origin: 'fixture-schema',
          generatorLineage: 'fixture',
        },
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'behavior',
          kind: 'integration',
          sourceKind: 'runtime-derived',
          origin: 'fixture-integration',
          generatorLineage: 'fixture-runtime',
        },
      ],
      policyEvidence: ['postDeployVerify', 'qualityGates'],
    }, null, 2)}\n`);

    const githubOutput = path.join(workspace, 'github-output.txt');
    const command = [
      'scripts/actions/assurance-gate.mjs',
      '--workspace', workspace,
      '--action-repo', repoRoot,
      '--profile', 'minimal',
      '--artifacts-dir', 'artifacts',
      '--output-dir', 'artifacts/assurance-gate',
    ];
    const result = spawnSync('node', command, {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 30_000,
      env: { ...process.env, GITHUB_OUTPUT: githubOutput },
    });

    expect(result.stderr).toBe('');
    expect(result.status).toBe(0);
    expect(result.stdout).toContain('ae-framework assurance gate: pass');
    expect(readFileSync(githubOutput, 'utf8')).toContain('review-surface-path=artifacts/assurance-gate/review-surface.md');

    const gateResult = JSON.parse(readFileSync(path.join(workspace, 'artifacts', 'assurance-gate', 'gate-result.json'), 'utf8'));
    expect(gateResult).toMatchObject({
      schemaVersion: 'assurance-gate-result/v1',
      profile: 'minimal',
      policyResult: 'pass',
      reviewSurfacePath: 'artifacts/assurance-gate/review-surface.md',
    });
    const summary = JSON.parse(readFileSync(path.join(workspace, 'artifacts', 'assurance-gate', 'assurance-summary.json'), 'utf8'));
    expect(summary.summary).toMatchObject({ claimCount: 1, satisfiedClaims: 1, warningCount: 0 });
    const reviewSurface = readFileSync(path.join(workspace, 'artifacts', 'assurance-gate', 'review-surface.md'), 'utf8');
    expect(reviewSurface).toContain('Policy decision: pass');

    const rerun = spawnSync('node', command, {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 30_000,
    });
    expect(rerun.status).toBe(0);
    const rerunGateResult = JSON.parse(readFileSync(path.join(workspace, 'artifacts', 'assurance-gate', 'gate-result.json'), 'utf8'));
    expect(rerunGateResult.artifactValidation.warningCount).toBe(1);
  });

  it('records a blocking minimal gate decision for missing policy evidence', () => {
    const workspace = resetWorkspace('minimal-block');
    writeFileSync(path.join(workspace, 'artifacts', 'evidence.json'), `${JSON.stringify({
      evidence: [
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'spec',
          kind: 'schema',
          sourceKind: 'spec-derived',
          origin: 'fixture-schema',
        },
      ],
      policyEvidence: ['postDeployVerify'],
    }, null, 2)}\n`);

    const baseCommand = [
      'scripts/actions/assurance-gate.mjs',
      '--workspace', workspace,
      '--action-repo', repoRoot,
      '--profile', 'minimal',
      '--artifacts-dir', 'artifacts',
      '--output-dir', 'artifacts/assurance-gate',
    ];
    const reportOnlyResult = spawnSync('node', [...baseCommand, '--fail-on-block', 'false'], {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 30_000,
    });

    expect(reportOnlyResult.stderr).toBe('');
    expect(reportOnlyResult.status).toBe(0);
    expect(reportOnlyResult.stdout).toContain('ae-framework assurance gate: block');

    const gateResult = JSON.parse(readFileSync(path.join(workspace, 'artifacts', 'assurance-gate', 'gate-result.json'), 'utf8'));
    expect(gateResult).toMatchObject({
      profile: 'minimal',
      policyResult: 'block',
      policyEvidence: ['postDeployVerify'],
    });
    const policyDecision = JSON.parse(readFileSync(path.join(workspace, 'artifacts', 'assurance-gate', 'policy-decision.json'), 'utf8'));
    expect(policyDecision.missingEvidence).toEqual(['qualityGates']);
    const reviewSurface = readFileSync(path.join(workspace, 'artifacts', 'assurance-gate', 'review-surface.md'), 'utf8');
    expect(reviewSurface).toContain('Policy decision: block');

    const enforcedResult = spawnSync('node', [...baseCommand, '--fail-on-block', 'true'], {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 30_000,
    });
    expect(enforcedResult.status).toBe(1);
    expect(enforcedResult.stderr).toContain('policy blocked: missing evidence qualityGates');
  });

  it('rejects malformed custom release policies before evaluation', () => {
    const workspace = resetWorkspace('invalid-policy');
    mkdirSync(path.join(workspace, '.ae'), { recursive: true });
    writeFileSync(path.join(workspace, '.ae', 'policy.yml'), 'schemaVersion: ae-release-policy/v1\nrequiredEvidence: not-an-array\n');
    writeFileSync(path.join(workspace, 'artifacts', 'evidence.json'), `${JSON.stringify({
      policyEvidence: ['postDeployVerify', 'qualityGates'],
    }, null, 2)}\n`);

    const result = spawnSync('node', [
      'scripts/actions/assurance-gate.mjs',
      '--workspace', workspace,
      '--action-repo', repoRoot,
      '--profile', 'minimal',
      '--artifacts-dir', 'artifacts',
      '--policy', '.ae/policy.yml',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 30_000,
    });

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('Policy validation failed');
  });


  it('rejects custom profile policy paths that escape the workspace', () => {
    const workspace = resetWorkspace('escaping-custom-policy');
    mkdirSync(path.join(workspace, '.ae'), { recursive: true });
    const customProfile = readFileSync(path.join(repoRoot, 'profiles', 'minimal.yaml'), 'utf8')
      .replace('profileId: minimal', 'profileId: escaping-policy')
      .replace('source: policy/release-policy.yml', 'source: ../../../../etc/passwd');
    writeFileSync(path.join(workspace, '.ae', 'custom-profile.yaml'), customProfile);

    const result = spawnSync('node', [
      'scripts/actions/assurance-gate.mjs',
      '--workspace', workspace,
      '--action-repo', repoRoot,
      '--profile', '.ae/custom-profile.yaml',
      '--artifacts-dir', 'artifacts',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 30_000,
    });

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('custom profile policy must be inside');
  });


  it('validates semver contract artifacts instead of treating them as unknown', () => {
    const workspace = resetWorkspace('malformed-semver-artifact');
    writeFileSync(path.join(workspace, 'artifacts', 'evidence.json'), `${JSON.stringify({
      policyEvidence: ['postDeployVerify', 'qualityGates'],
    }, null, 2)}\n`);
    writeFileSync(path.join(workspace, 'artifacts', 'policy-decision.json'), `${JSON.stringify({
      schemaVersion: '1.0.0',
      contractId: 'policy-decision.v1',
    }, null, 2)}\n`);

    const result = spawnSync('node', [
      'scripts/actions/assurance-gate.mjs',
      '--workspace', workspace,
      '--action-repo', repoRoot,
      '--profile', 'minimal',
      '--artifacts-dir', 'artifacts',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 30_000,
    });

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('policy-decision-v1');
  });
});
