import { afterEach, describe, expect, it } from 'vitest';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const validateScript = resolve(repoRoot, 'scripts/plan-artifact/validate.mjs');
const schemaPath = resolve(repoRoot, 'schema/plan-artifact.schema.json');
const policyPath = resolve(repoRoot, 'policy/risk-policy.yml');
const fixturePath = resolve(repoRoot, 'fixtures/plan/sample.plan-artifact.json');
const workdirs: string[] = [];

async function createWorkdir(prefix: string) {
  const workdir = await mkdtemp(join(tmpdir(), prefix));
  workdirs.push(workdir);
  return workdir;
}

afterEach(async () => {
  await Promise.all(workdirs.splice(0).map((workdir) => rm(workdir, { recursive: true, force: true })));
});

describe('plan-artifact validate', () => {
  it('passes for the sample fixture', async () => {
    const workdir = await createWorkdir('plan-artifact-validate-pass-');
    const inputPath = join(workdir, 'plan-artifact.json');
    const outputJsonPath = join(workdir, 'plan-artifact-validation.json');
    const outputMarkdownPath = join(workdir, 'plan-artifact-validation.md');
    await writeFile(inputPath, await readFile(fixturePath, 'utf8'));

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', schemaPath,
      '--policy', policyPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);
    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as { result: string };
    expect(report.result).toBe('pass');
  });

  it('fails when required fields are missing', async () => {
    const workdir = await createWorkdir('plan-artifact-validate-fail-');
    const inputPath = join(workdir, 'plan-artifact.json');
    const outputJsonPath = join(workdir, 'plan-artifact-validation.json');
    const outputMarkdownPath = join(workdir, 'plan-artifact-validation.md');
    const payload = JSON.parse(await readFile(fixturePath, 'utf8')) as Record<string, unknown>;
    delete payload.rollbackPlan;
    await writeFile(inputPath, `${JSON.stringify(payload, null, 2)}\n`);

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', schemaPath,
      '--policy', policyPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(1);
    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as { result: string; errors: string[] };
    expect(report.result).toBe('fail');
    expect(report.errors.some((item) => item.includes('rollbackPlan'))).toBe(true);
  });

  it('passes when risk labels are customized in policy', async () => {
    const workdir = await createWorkdir('plan-artifact-validate-custom-risk-');
    const inputPath = join(workdir, 'plan-artifact.json');
    const outputJsonPath = join(workdir, 'plan-artifact-validation.json');
    const outputMarkdownPath = join(workdir, 'plan-artifact-validation.md');
    const customPolicyPath = join(workdir, 'risk-policy.yml');
    const payload = JSON.parse(await readFile(fixturePath, 'utf8')) as Record<string, unknown>;
    payload.risk = {
      selected: 'priority:critical',
      requiresHumanApproval: true,
      minHumanApprovals: 1,
    };
    await writeFile(inputPath, `${JSON.stringify(payload, null, 2)}\n`);
    await writeFile(customPolicyPath, [
      'labels:',
      '  risk:',
      '    low: priority:normal',
      '    high: priority:critical',
      'high_risk:',
      '  min_human_approvals: 1',
      '  require_plan_artifact: true',
    ].join('\n'));

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', schemaPath,
      '--policy', customPolicyPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);
    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as { result: string; errors: string[] };
    expect(report.result).toBe('pass');
    expect(report.errors).toHaveLength(0);
  });
});
