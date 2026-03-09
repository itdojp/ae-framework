import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const scriptPath = resolve(process.cwd(), 'scripts/agents/build-hook-feedback.mjs');
const schemaPath = resolve(process.cwd(), 'schema/hook-feedback.schema.json');

const schema = JSON.parse(await readFile(schemaPath, 'utf8')) as Record<string, unknown>;
const ajv = new Ajv2020({ allErrors: true, strict: false });
addFormats(ajv);
const validate = ajv.compile(schema);

describe('build-hook-feedback CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'hook-feedback-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  async function writeJson(relativePath: string, payload: unknown) {
    const fullPath = join(workdir, relativePath);
    await mkdir(dirname(fullPath), { recursive: true });
    await writeFile(fullPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
    return fullPath;
  }

  function runBuild(extraArgs: string[] = []) {
    const outputJsonPath = join(workdir, 'artifacts', 'agents', 'hook-feedback.json');
    const outputMdPath = join(workdir, 'artifacts', 'agents', 'hook-feedback.md');
    const result = spawnSync(process.execPath, [
      scriptPath,
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

  it('builds blocked feedback with actionable next actions and repro commands', async () => {
    await writeJson('artifacts/verify-lite/verify-lite-run-summary.json', {
      schemaVersion: '1.0.0',
      timestamp: '2026-03-09T00:00:00.000Z',
      metadata: { generatedAt: '2026-03-09T00:00:00.000Z', generator: 'test', toolVersions: {} },
      flags: { install: '', noFrozen: false, keepLintLog: false, enforceLint: false, runMutation: false },
      steps: {
        lint: { status: 'failure' },
        build: { status: 'success' },
      },
      traceability: {
        status: 'failure',
        missingCount: 2,
        matrixPath: 'artifacts/traceability/matrix.json',
        notes: '2 links missing',
      },
      artifacts: {
        lintSummary: null,
        lintLog: null,
        mutationSummary: null,
        mutationSurvivors: null,
        conformanceSummary: null,
        conformanceSummaryMarkdown: null,
      },
    });
    await writeJson('artifacts/ci/harness-health.json', {
      schemaVersion: 'harness-health/v1',
      generatedAt: '2026-03-09T00:00:00.000Z',
      severity: 'critical',
      reasons: ['Testing harness: 1 failing reproducibility records.'],
      recommendedLabels: ['run-ci-extended'],
      recommendedContextChanges: [
        {
          file: 'spec/context-pack/functor-map.json',
          changeType: 'add',
          targetId: 'ReserveInventory',
          suggestedCommand: 'pnpm run context-pack:verify-functor',
        },
      ],
      reproducibleHints: [
        { gate: 'testingHarness', command: 'pnpm run test:ci:extended' },
      ],
      gates: {},
    });
    await writeJson('artifacts/change-package/change-package.json', {
      schemaVersion: 'change-package/v1',
      risk: {
        selected: 'risk:high',
        missingRequiredLabels: ['run-ci-extended'],
      },
      evidence: {
        items: [
          {
            id: 'verifyLiteSummary',
            path: 'artifacts/verify-lite/verify-lite-run-summary.json',
            description: 'verify-lite run summary',
            present: true,
          },
        ],
      },
      reproducibility: {
        commands: ['pnpm run verify:lite', 'pnpm run test:ci:extended'],
      },
      exceptions: [
        { code: 'missing-required-labels', message: 'Missing required labels: run-ci-extended' },
      ],
    });
    await writeJson('artifacts/context-pack/context-pack-suggestions.json', {
      schemaVersion: 'context-pack-suggestions/v1',
      generatedAt: '2026-03-09T00:00:00.000Z',
      status: 'fail',
      recommendedContextChanges: [
        {
          file: 'spec/context-pack/functor-map.json',
          changeType: 'add',
          targetId: 'ReserveInventory',
          suggestedCommand: 'pnpm run context-pack:verify-functor',
        },
      ],
    });

    const { result, outputJsonPath, outputMdPath } = runBuild();
    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      status: string;
      nextActions: string[];
      reproCommands: string[];
      evidence: Array<{ id: string }>;
      blockingReasons: string[];
    };
    expect(validate(report), JSON.stringify(validate.errors)).toBe(true);
    expect(report.status).toBe('blocked');
    expect(report.blockingReasons.some((entry) => entry.includes('Missing required labels'))).toBe(true);
    expect(report.nextActions.some((entry) => entry.includes('fix failing verify-lite steps'))).toBe(true);
    expect(report.nextActions.some((entry) => entry.includes('run-ci-extended'))).toBe(true);
    expect(report.reproCommands).toContain('pnpm run verify:lite');
    expect(report.reproCommands).toContain('pnpm run test:ci:extended');
    expect(report.reproCommands).toContain('pnpm run context-pack:verify-functor');
    expect(report.evidence.some((entry) => entry.id === 'harnessHealth')).toBe(true);

    const markdown = await readFile(outputMdPath, 'utf8');
    expect(markdown).toContain('# Hook Feedback');
    expect(markdown).toContain('## Repro commands');
  });

  it('builds warn feedback and falls back to verify-lite command when no repro command is present', async () => {
    await writeJson('artifacts/verify-lite/verify-lite-run-summary.json', {
      schemaVersion: '1.0.0',
      timestamp: '2026-03-09T00:00:00.000Z',
      metadata: { generatedAt: '2026-03-09T00:00:00.000Z', generator: 'test', toolVersions: {} },
      flags: { install: '', noFrozen: false, keepLintLog: false, enforceLint: false, runMutation: false },
      steps: {
        lint: { status: 'pending' },
        build: { status: 'success' },
      },
      artifacts: {
        lintSummary: null,
        lintLog: null,
        mutationSummary: null,
        mutationSurvivors: null,
        conformanceSummary: null,
        conformanceSummaryMarkdown: null,
      },
    });
    await writeJson('artifacts/ci/harness-health.json', {
      schemaVersion: 'harness-health/v1',
      generatedAt: '2026-03-09T00:00:00.000Z',
      severity: 'warn',
      reasons: ['Testing harness: pending checks.'],
      recommendedLabels: [],
      recommendedContextChanges: [],
      reproducibleHints: [],
      gates: {},
    });
    await writeJson('artifacts/change-package/change-package.json', {
      schemaVersion: 'change-package/v1',
      evidence: { items: [] },
      reproducibility: { commands: [] },
      exceptions: [],
      risk: { selected: 'risk:low', missingRequiredLabels: [] },
    });

    const { result, outputJsonPath } = runBuild();
    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      status: string;
      reproCommands: string[];
      nextActions: string[];
      source: { contextPackSuggestionsPath: string | null };
    };
    expect(validate(report), JSON.stringify(validate.errors)).toBe(true);
    expect(report.status).toBe('warn');
    expect(report.reproCommands).toEqual(['pnpm run verify:lite']);
    expect(report.nextActions[0]).toContain('incomplete verify-lite steps');
    expect(report.source.contextPackSuggestionsPath).toBeNull();
  });
});
