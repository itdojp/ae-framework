import { afterEach, describe, expect, it } from 'vitest';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const scriptPath = resolve(repoRoot, 'scripts/plan-artifact/generate.mjs');
const policyPath = resolve(repoRoot, 'policy/risk-policy.yml');
const workdirs: string[] = [];

async function createWorkdir(prefix: string) {
  const workdir = await mkdtemp(join(tmpdir(), prefix));
  workdirs.push(workdir);
  return workdir;
}

afterEach(async () => {
  await Promise.all(workdirs.splice(0).map((workdir) => rm(workdir, { recursive: true, force: true })));
});

describe('plan-artifact generate', () => {
  it('renders plan artifact json and markdown from input payload', async () => {
    const workdir = await createWorkdir('plan-artifact-generate-');
    const inputPath = join(workdir, 'plan-artifact.input.json');
    const eventPath = join(workdir, 'event.json');
    const outputJsonPath = join(workdir, 'artifacts', 'plan', 'plan-artifact.json');
    const outputMarkdownPath = join(workdir, 'artifacts', 'plan', 'plan-artifact.md');

    await mkdir(join(workdir, 'artifacts', 'plan'), { recursive: true });
    await writeFile(inputPath, `${JSON.stringify({
      goal: 'Introduce plan-artifact/v1',
      scope: 'Add schema, scripts, and policy-gate wiring.',
      risk: { selected: 'risk:high' },
      assumptions: ['Artifacts can be committed to the PR branch.'],
      filesExpectedToChange: ['schema/plan-artifact.schema.json', 'scripts/ci/policy-gate.mjs'],
      verificationPlan: [
        {
          name: 'Run contract tests',
          command: 'pnpm exec vitest run tests/contracts/plan-artifact-contract.test.ts',
          expectedEvidence: ['fixtures/plan/sample.plan-artifact.json']
        }
      ],
      rollbackPlan: 'Revert schema, scripts, and docs.',
      requiredHumanInput: ['approval=plan-review']
    }, null, 2)}\n`);
    await writeFile(eventPath, `${JSON.stringify({
      repository: { full_name: 'itdojp/ae-framework' },
      pull_request: {
        number: 2535,
        base: { ref: 'main' },
        head: { ref: 'feat/2535-plan-artifact' }
      }
    }, null, 2)}\n`);

    const result = spawnSync(process.execPath, [
      scriptPath,
      '--policy', policyPath,
      '--input', inputPath,
      '--event-path', eventPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      env: { ...process.env, GITHUB_EVENT_PATH: '' },
    });

    expect(result.status).toBe(0);

    const json = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      schemaVersion: string;
      source: { repository: string; prNumber: number };
      risk: { selected: string; minHumanApprovals: number };
      assumptions: Array<{ id: string; text: string }>;
    };
    expect(json.schemaVersion).toBe('plan-artifact/v1');
    expect(json.source.repository).toBe('itdojp/ae-framework');
    expect(json.source.prNumber).toBe(2535);
    expect(json.risk.selected).toBe('risk:high');
    expect(json.risk.minHumanApprovals).toBe(1);
    expect(json.assumptions[0].id).toBe('A1');

    const markdown = await readFile(outputMarkdownPath, 'utf8');
    expect(markdown).toContain('## Plan Artifact');
    expect(markdown).toContain('### Verification plan');
  });

  it('fails fast when goal is empty', async () => {
    const workdir = await createWorkdir('plan-artifact-generate-empty-goal-');
    const inputPath = join(workdir, 'plan-artifact.input.json');
    const eventPath = join(workdir, 'event.json');
    const outputJsonPath = join(workdir, 'artifacts', 'plan', 'plan-artifact.json');
    const outputMarkdownPath = join(workdir, 'artifacts', 'plan', 'plan-artifact.md');

    await mkdir(join(workdir, 'artifacts', 'plan'), { recursive: true });
    await writeFile(inputPath, `${JSON.stringify({
      goal: '   ',
      scope: 'Add schema, scripts, and policy-gate wiring.',
      risk: { selected: 'risk:high' },
      assumptions: ['Artifacts can be committed to the PR branch.'],
      filesExpectedToChange: ['schema/plan-artifact.schema.json'],
      verificationPlan: [
        {
          name: 'Run contract tests',
          command: 'pnpm exec vitest run tests/contracts/plan-artifact-contract.test.ts',
        }
      ],
      rollbackPlan: 'Revert schema, scripts, and docs.',
      requiredHumanInput: ['approval=plan-review']
    }, null, 2)}\n`);
    await writeFile(eventPath, `${JSON.stringify({
      repository: { full_name: 'itdojp/ae-framework' },
      pull_request: {
        number: 2535,
        base: { ref: 'main' },
        head: { ref: 'feat/2535-plan-artifact' }
      }
    }, null, 2)}\n`);

    const result = spawnSync(process.execPath, [
      scriptPath,
      '--policy', policyPath,
      '--input', inputPath,
      '--event-path', eventPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
      env: { ...process.env, GITHUB_EVENT_PATH: '' },
    });

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('goal is required and must be non-empty');
  });
});
