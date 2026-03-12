import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { cp, mkdtemp, mkdir, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { renderMarkdown } from '../../../scripts/agents/create-handoff.mjs';

const scriptPath = resolve(process.cwd(), 'scripts/agents/create-handoff.mjs');
const schemaPath = resolve(process.cwd(), 'schema/ae-handoff.schema.json');
const hookFeedbackFixturePath = resolve(process.cwd(), 'fixtures/agents/sample.hook-feedback.json');
const partialHookFeedbackFixturePath = resolve(process.cwd(), 'fixtures/agents/sample.hook-feedback-partial.json');
const verifyLiteFixturePath = resolve(process.cwd(), 'packages/envelope/__fixtures__/verify-lite-summary.json');
const harnessHealthFixturePath = resolve(process.cwd(), 'fixtures/ci/sample.harness-health.json');
const changePackageFixturePath = resolve(process.cwd(), 'fixtures/change-package/sample.change-package.json');
const assuranceSummaryFixturePath = resolve(process.cwd(), 'fixtures/assurance/sample.assurance-summary.json');
const uiE2ESummaryFixturePath = resolve(process.cwd(), 'fixtures/e2e/sample.ui-e2e-summary.json');
const policyGateFixturePath = resolve(process.cwd(), 'fixtures/policy-gate/sample.policy-gate-summary-v1.json');

const schema = JSON.parse(await readFile(schemaPath, 'utf8')) as Record<string, unknown>;
const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);
const validate = ajv.compile(schema);

describe('create-handoff CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'ae-handoff-create-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  async function writeFixture(relativePath: string, sourcePath: string) {
    const fullPath = join(workdir, relativePath);
    await mkdir(dirname(fullPath), { recursive: true });
    await cp(sourcePath, fullPath);
    return fullPath;
  }

  function runCreate(extraArgs: string[] = []) {
    const outputJsonPath = join(workdir, 'artifacts', 'handoff', 'ae-handoff.json');
    const outputMdPath = join(workdir, 'artifacts', 'handoff', 'ae-handoff.md');
    const result = spawnSync(process.execPath, [
      scriptPath,
      '--goal',
      'prepare deterministic handoff package',
      '--target',
      'A',
      '--generated-at',
      '2026-03-12T13:00:00.000Z',
      '--schema',
      schemaPath,
      '--output-json',
      outputJsonPath,
      '--output-md',
      outputMdPath,
      ...extraArgs,
    ], {
      cwd: workdir,
    });
    return { result, outputJsonPath, outputMdPath };
  }

  it('builds valid AE-HANDOFF from an existing hook-feedback artifact', async () => {
    await writeFixture('artifacts/agents/hook-feedback.json', hookFeedbackFixturePath);
    await writeFixture('artifacts/ci/policy-gate-summary.json', policyGateFixturePath);

    const { result, outputJsonPath, outputMdPath } = runCreate([
      '--command-run',
      'gh pr checks 2646 --required',
      '--risks-rollback-note',
      'revert the workflow change if gate behavior regresses',
    ]);

    expect(result.status).toBe(0);

    const handoff = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      schemaVersion: string;
      handoffTarget: string | null;
      changePackageRef: string | null;
      artifacts: Array<{ path: string }>;
      blockers: Array<{ summary: string; kind: string }>;
    };
    const markdown = await readFile(outputMdPath, 'utf8');

    expect(validate(handoff), JSON.stringify(validate.errors)).toBe(true);
    expect(handoff.schemaVersion).toBe('ae-handoff/v1');
    expect(handoff.handoffTarget).toBe('A');
    expect(handoff.changePackageRef).toBe('artifacts/change-package/change-package.json');
    expect(handoff.artifacts.some((entry) => entry.path === 'artifacts/agents/hook-feedback.json')).toBe(true);
    expect(handoff.artifacts.some((entry) => entry.path === 'artifacts/assurance/assurance-summary.json')).toBe(true);
    expect(handoff.blockers.some((entry) => entry.summary.includes('Missing required labels'))).toBe(true);
    expect((handoff as { nextActions: Array<{ command: string | null }> }).nextActions[1]?.command)
      .toBe('pnpm run context-pack:verify-functor');
    expect(markdown).toContain('## AE-HANDOFF');
    expect(markdown).toContain('prepare deterministic handoff package');
  });

  it('does not emit missing evidence paths from partial hook-feedback', async () => {
    await writeFixture('artifacts/agents/hook-feedback.json', partialHookFeedbackFixturePath);

    const { result, outputJsonPath } = runCreate();
    expect(result.status).toBe(0);

    const handoff = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      artifacts: Array<{ path: string }>;
      blockers: Array<{ summary: string }>;
    };

    expect(validate(handoff), JSON.stringify(validate.errors)).toBe(true);
    expect(handoff.artifacts.some((entry) => entry.path === 'artifacts/ci/harness-health.json')).toBe(false);
    expect(handoff.artifacts.some((entry) => entry.path === 'artifacts/change-package/change-package.json')).toBe(false);
    expect(handoff.blockers.some((entry) => entry.summary.includes('Missing artifact: harness-health'))).toBe(true);
  });

  it('derives handoff content from verify-lite and companion artifacts when hook-feedback is missing', async () => {
    await writeFixture('artifacts/verify-lite/verify-lite-run-summary.json', verifyLiteFixturePath);
    await writeFixture('artifacts/ci/harness-health.json', harnessHealthFixturePath);
    await writeFixture('artifacts/change-package/change-package.json', changePackageFixturePath);
    await writeFixture('artifacts/assurance/assurance-summary.json', assuranceSummaryFixturePath);
    await writeFixture('artifacts/e2e/ui-e2e-summary.json', uiE2ESummaryFixturePath);
    await writeFixture('artifacts/ci/policy-gate-summary.json', policyGateFixturePath);

    const { result, outputJsonPath } = runCreate([
      '--hook-feedback',
      'artifacts/agents/missing-hook-feedback.json',
      '--command-run',
      'pnpm -s run verify:lite',
    ]);

    expect(result.status).toBe(0);

    const handoff = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      currentStatus: string;
      commandsRun: string[];
      artifacts: Array<{ path: string }>;
      blockers: Array<{ summary: string }>;
    };

    expect(validate(handoff), JSON.stringify(validate.errors)).toBe(true);
    expect(handoff.commandsRun).toContain('pnpm -s run verify:lite');
    expect(handoff.artifacts.some((entry) => entry.path === 'artifacts/verify-lite/verify-lite-run-summary.json')).toBe(true);
    expect(handoff.artifacts.some((entry) => entry.path === 'artifacts/ci/policy-gate-summary.json')).toBe(true);
    expect(handoff.blockers.some((entry) => entry.summary.startsWith('policy-gate:'))).toBe(true);
    expect(handoff.currentStatus).not.toBe('');
  });

  it('fails when neither hook-feedback nor verify-lite summary exists', async () => {
    const { result } = runCreate([
      '--hook-feedback',
      'artifacts/agents/missing-hook-feedback.json',
      '--verify-lite-summary',
      'artifacts/verify-lite/missing-summary.json',
    ]);

    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('hook-feedback not found');
  });

  it('normalizes whitespace-only target and current-status overrides', async () => {
    await writeFixture('artifacts/agents/hook-feedback.json', hookFeedbackFixturePath);

    const { result, outputJsonPath } = runCreate([
      '--target',
      '   ',
      '--current-status',
      '   ',
    ]);

    expect(result.status).toBe(0);

    const handoff = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      handoffTarget: string | null;
      currentStatus: string;
    };

    expect(handoff.handoffTarget).toBeNull();
    expect(handoff.currentStatus).not.toBe('');
  });

  it('renders markdown with safe fences when payload contains backticks', () => {
    const markdown = renderMarkdown({
      schemaVersion: 'ae-handoff/v1',
      generatedAt: '2026-03-12T13:00:00.000Z',
      handoffTarget: 'A',
      goal: 'stabilize ```json fenced payload',
      currentStatus: 'rerun `pnpm -s run verify:lite` after updating `docs/example.md`',
      nextActions: [
        {
          order: 1,
          summary: 'rerun `pnpm -s run verify:lite`',
          command: 'pnpm -s run verify:lite',
        },
      ],
      commandsRun: ['node -e \"console.log(`ok`)\"'],
      artifacts: [{ path: 'artifacts/example`trace`.json', description: 'example with backticks' }],
      risksRollbackNote: null,
      blockers: [],
      changePackageRef: null,
    });

    expect(markdown).toContain('````json');
    expect(markdown).toContain('``artifacts/example`trace`.json``');
    expect(markdown).toContain('``node -e \"console.log(`ok`)\"``');
  });
});
