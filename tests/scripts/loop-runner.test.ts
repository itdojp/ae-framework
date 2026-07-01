import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { describe, expect, it } from 'vitest';

import {
  buildLoopRun,
  parseArgs,
  renderMarkdown,
  run,
} from '../../scripts/loop/run-report-only.mjs';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/loop/run-report-only.mjs');
const generatedAt = '2026-07-01T00:00:00.000Z';
const schema = JSON.parse(readFileSync(resolve('schema/loop-run-summary.schema.json'), 'utf8'));
const strictPolicy = readJson('fixtures/loop/strict-safety.loop-policy.json');

function readJson(filePath: string) {
  return JSON.parse(readFileSync(resolve(filePath), 'utf8'));
}

function validateWithSchema(payload: unknown) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  expect(validate(payload), JSON.stringify(validate.errors, null, 2)).toBe(true);
}

function tempDir(prefix: string) {
  const root = resolve('.codex-local/tmp');
  mkdirSync(root, { recursive: true });
  return mkdtempSync(join(root, prefix));
}

function buildWithTempPolicy(input: Record<string, any>, policy: Record<string, any>) {
  const outputDir = tempDir('loop-runner-policy-');
  const inputPath = join(outputDir, 'loop-input.json');
  const policyPath = join(outputDir, 'loop-policy.json');
  writeFileSync(inputPath, `${JSON.stringify(input, null, 2)}\n`);
  writeFileSync(policyPath, `${JSON.stringify(policy, null, 2)}\n`);
  try {
    return buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      inputPath,
      '--policy',
      policyPath,
      '--generated-at',
      generatedAt,
      '--no-write',
    ]));
  } finally {
    rmSync(outputDir, { recursive: true, force: true });
  }
}

describe('report-only loop runner', () => {
  it('builds the deterministic success summary fixture', () => {
    const summary = buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      'examples/loop-engineering/success/loop-input.json',
      '--generated-at',
      generatedAt,
      '--no-write',
    ]));

    expect(summary).toEqual(readJson('fixtures/loop/success.loop-run-summary.json'));
    expect(renderMarkdown(summary)).toBe(readFileSync(resolve('fixtures/loop/success.loop-run-summary.md'), 'utf8'));
    validateWithSchema(summary);
    expect(summary.reportOnly).toBe(true);
    expect(summary.stopReason).toBe('success');
    expect(summary.iterations[0].observedEvidence[0].status).toBe('pass');
    expect(summary.commands).toEqual([
      'pnpm -s run verify:lite -- --fixture examples/loop-engineering/success/verify-lite-summary.json',
    ]);
    expect(summary.policy.policyId).toBe('loop-report-only-default');
    expect(summary.observability.approvalAuthority).toContain('report-only');
  });

  it('keeps loop-run-summary/v1 schema compatible with pre-policy summaries', () => {
    const legacySummary = readJson('fixtures/loop/success.loop-run-summary.json');
    delete legacySummary.policy;
    delete legacySummary.observability;
    delete legacySummary.replay;

    validateWithSchema(legacySummary);
  });

  it('includes generatedAt in the replay idempotency key', () => {
    const baseArgs = [
      'node',
      scriptPath,
      '--input',
      'examples/loop-engineering/success/loop-input.json',
      '--no-write',
    ];
    const first = buildLoopRun(parseArgs([...baseArgs, '--generated-at', generatedAt]));
    const second = buildLoopRun(parseArgs([...baseArgs, '--generated-at', '2026-07-01T01:00:00.000Z']));

    expect(first.replay.idempotencyKey).not.toBe(second.replay.idempotencyKey);
    expect(first.replay.note).toContain('generatedAt');
  });

  it('builds the deterministic blocked summary fixture without failing the report-only CLI', () => {
    const summary = buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      'examples/loop-engineering/blocked/loop-input.json',
      '--generated-at',
      generatedAt,
      '--no-write',
    ]));

    expect(summary).toEqual(readJson('fixtures/loop/blocked.loop-run-summary.json'));
    validateWithSchema(summary);
    expect(summary.stopReason).toBe('blocked');
    expect(summary.iterations[0].validation.actualStatus).toBe('fail');
    expect(summary.nextRecommendedAction).toContain('update the ExecPlan');

    const outputDir = tempDir('loop-runner-blocked-');
    const jsonPath = join(outputDir, 'blocked-summary.json');
    const mdPath = join(outputDir, 'blocked-summary.md');
    const result = spawnSync('node', [
      scriptPath,
      '--input',
      'examples/loop-engineering/blocked/loop-input.json',
      '--generated-at',
      generatedAt,
      '--output-json',
      jsonPath,
      '--output-md',
      mdPath,
    ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(readJson(jsonPath)).toMatchObject({ result: 'blocked', reportOnly: true });
    expect(readFileSync(mdPath, 'utf8')).toContain('Stop reason: `blocked`');
    rmSync(outputDir, { recursive: true, force: true });
  });

  it('returns a failing process status for unsafe actions while still producing review evidence', () => {
    const outputDir = tempDir('loop-runner-unsafe-');
    const inputPath = join(outputDir, 'unsafe-input.json');
    const jsonPath = join(outputDir, 'unsafe-summary.json');
    const mdPath = join(outputDir, 'unsafe-summary.md');
    const input = readJson('examples/loop-engineering/success/loop-input.json');
    input.runId = 'loop-unsafe-demo';
    input.iterations[0].actionHook.kind = 'merge-pr';
    writeFileSync(inputPath, `${JSON.stringify(input, null, 2)}\n`);

    const result = spawnSync('node', [
      scriptPath,
      '--input',
      inputPath,
      '--generated-at',
      generatedAt,
      '--output-json',
      jsonPath,
      '--output-md',
      mdPath,
    ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });

    expect(result.status).toBe(1);
    const summary = JSON.parse(readFileSync(jsonPath, 'utf8'));
    expect(summary).toMatchObject({ result: 'unsafe-action', stopReason: 'unsafe-action' });
    expect(summary.safety.forbiddenActionsDetected).toEqual(['merge-pr']);
    expect(summary.observability.unsafeActionStops).toBe(1);
    validateWithSchema(summary);
    rmSync(outputDir, { recursive: true, force: true });
  });

  it('rejects review approval hooks even when they are marked non-mutating', () => {
    const input = readJson('examples/loop-engineering/success/loop-input.json');
    input.iterations[0].actionHook.kind = 'approve-review';
    input.iterations[0].actionHook.mutatesRepository = false;

    const outputDir = tempDir('loop-runner-approval-hook-');
    const inputPath = join(outputDir, 'approval-hook-input.json');
    writeFileSync(inputPath, `${JSON.stringify(input, null, 2)}\n`);

    const summary = buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      inputPath,
      '--generated-at',
      generatedAt,
      '--no-write',
    ]));

    expect(summary).toMatchObject({ result: 'unsafe-action', stopReason: 'unsafe-action' });
    expect(summary.safety.forbiddenActionsDetected).toEqual(['approve-review']);
    rmSync(outputDir, { recursive: true, force: true });
  });

  it('does not allow failed validation evidence to end as success', () => {
    const input = readJson('examples/loop-engineering/success/loop-input.json');
    input.runId = 'loop-validation-mismatch-demo';
    input.iterations[0].validation.actualStatus = 'fail';
    input.iterations[0].decision = 'success';

    const outputDir = tempDir('loop-runner-validation-mismatch-');
    const inputPath = join(outputDir, 'validation-mismatch-input.json');
    writeFileSync(inputPath, `${JSON.stringify(input, null, 2)}\n`);

    const summary = buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      inputPath,
      '--generated-at',
      generatedAt,
      '--no-write',
    ]));

    expect(summary).toMatchObject({ result: 'validation-failed', stopReason: 'validation-failed' });
    expect(summary.findings).toEqual(expect.arrayContaining([
      expect.objectContaining({ code: 'validation-status-mismatch', severity: 'error' }),
    ]));
    rmSync(outputDir, { recursive: true, force: true });
  });

  it('reports fixture exhaustion as blocked instead of max-iterations', () => {
    const input = readJson('examples/loop-engineering/success/loop-input.json');
    input.runId = 'loop-fixture-exhausted-demo';
    input.maxIterations = 3;
    input.iterations[0].decision = 'continue';

    const outputDir = tempDir('loop-runner-fixture-exhausted-');
    const inputPath = join(outputDir, 'fixture-exhausted-input.json');
    writeFileSync(inputPath, `${JSON.stringify(input, null, 2)}\n`);

    const summary = buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      inputPath,
      '--generated-at',
      generatedAt,
      '--no-write',
    ]));

    expect(summary).toMatchObject({ result: 'blocked', stopReason: 'blocked' });
    expect(summary.findings).toEqual(expect.arrayContaining([
      expect.objectContaining({ code: 'fixture-exhausted', severity: 'warning' }),
    ]));
    rmSync(outputDir, { recursive: true, force: true });
  });

  it('builds the deterministic safety-budget summary fixture with repeated-failure observability', () => {
    const summary = buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      'examples/loop-engineering/safety/loop-input.json',
      '--generated-at',
      generatedAt,
      '--no-write',
    ]));

    expect(summary).toEqual(readJson('fixtures/loop/safety-budget.loop-run-summary.json'));
    expect(renderMarkdown(summary)).toBe(readFileSync(resolve('fixtures/loop/safety-budget.loop-run-summary.md'), 'utf8'));
    validateWithSchema(summary);
    expect(summary).toMatchObject({ result: 'blocked', stopReason: 'blocked' });
    expect(summary.observability.repeatedFailureSignatures).toEqual([
      expect.objectContaining({ signature: 'loop.verify-lite.same-error', count: 2 }),
    ]);
    expect(summary.reviewSurface.body).toContain('Authority: report-only evidence');
  });

  it('applies report-only loop policy stops for budgets, commands, paths, evidence, and risk', () => {
    const baseInput = readJson('examples/loop-engineering/success/loop-input.json');

    const maxIterationsInput = JSON.parse(JSON.stringify(baseInput));
    maxIterationsInput.runId = 'loop-policy-max-iterations-demo';
    maxIterationsInput.maxIterations = 3;
    maxIterationsInput.iterations[0].decision = 'continue';
    const maxIterationsPolicy = JSON.parse(JSON.stringify(strictPolicy));
    maxIterationsPolicy.budgets.maxIterations = 1;
    expect(buildWithTempPolicy(maxIterationsInput, maxIterationsPolicy)).toMatchObject({
      result: 'max-iterations',
      stopReason: 'max-iterations',
    });

    const deniedCommandPolicy = JSON.parse(JSON.stringify(strictPolicy));
    deniedCommandPolicy.commandPolicy.denyList.push('pnpm -s run verify:lite');
    const deniedCommandSummary = buildWithTempPolicy(baseInput, deniedCommandPolicy);
    expect(deniedCommandSummary).toMatchObject({ result: 'unsafe-action', stopReason: 'unsafe-action' });
    expect(deniedCommandSummary.findings).toEqual(expect.arrayContaining([
      expect.objectContaining({ code: 'loop-policy-denied-command' }),
    ]));

    const deniedPathPolicy = JSON.parse(JSON.stringify(strictPolicy));
    deniedPathPolicy.pathPolicy.deniedPrefixes.push('examples/loop-engineering/success');
    const deniedPathSummary = buildWithTempPolicy(baseInput, deniedPathPolicy);
    expect(deniedPathSummary).toMatchObject({ result: 'unsafe-action', stopReason: 'unsafe-action' });
    expect(deniedPathSummary.findings).toEqual(expect.arrayContaining([
      expect.objectContaining({ code: 'loop-policy-denied-path' }),
    ]));

    const modifiedFileInput = JSON.parse(JSON.stringify(baseInput));
    modifiedFileInput.iterations[0].actionHook.modifiedFiles = ['docs/README.md'];
    const modifiedFileSummary = buildWithTempPolicy(modifiedFileInput, strictPolicy);
    expect(modifiedFileSummary).toMatchObject({ result: 'unsafe-action', stopReason: 'unsafe-action' });
    expect(modifiedFileSummary.findings).toEqual(expect.arrayContaining([
      expect.objectContaining({ code: 'loop-policy-modified-file-limit' }),
    ]));

    const missingEvidencePolicy = JSON.parse(JSON.stringify(strictPolicy));
    missingEvidencePolicy.evidenceRequirements.requiredEvidenceIds = ['ev.release-approval'];
    const missingEvidenceSummary = buildWithTempPolicy(baseInput, missingEvidencePolicy);
    expect(missingEvidenceSummary).toMatchObject({ result: 'blocked', stopReason: 'blocked' });
    expect(missingEvidenceSummary.observability.missingEvidenceIds).toEqual(['ev.release-approval']);

    const evidenceRequirementOnlyPolicy = JSON.parse(JSON.stringify(strictPolicy));
    evidenceRequirementOnlyPolicy.evidenceRequirements.requiredEvidenceIds = ['ev.release-approval'];
    evidenceRequirementOnlyPolicy.evidenceRequirements.missingEvidenceStops = true;
    evidenceRequirementOnlyPolicy.stopRules.stopOnMissingEvidence = false;
    const evidenceRequirementOnlySummary = buildWithTempPolicy(baseInput, evidenceRequirementOnlyPolicy);
    expect(evidenceRequirementOnlySummary).toMatchObject({ result: 'blocked', stopReason: 'blocked' });
    expect(evidenceRequirementOnlySummary.findings).toEqual(expect.arrayContaining([
      expect.objectContaining({ code: 'loop-policy-missing-evidence' }),
    ]));

    const highRiskInput = JSON.parse(JSON.stringify(baseInput));
    highRiskInput.goal.riskLevel = 'critical';
    const highRiskSummary = buildWithTempPolicy(highRiskInput, strictPolicy);
    expect(highRiskSummary).toMatchObject({ result: 'human-required', stopReason: 'human-required' });
    expect(highRiskSummary.findings).toEqual(expect.arrayContaining([
      expect.objectContaining({ code: 'loop-policy-human-approval-required' }),
    ]));
  });

  it('rejects input and output paths outside the working directory', () => {
    expect(() => buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      '../outside-loop-input.json',
      '--no-write',
    ]))).toThrow(/loop input must stay within the working directory/);

    const result = spawnSync('node', [
      scriptPath,
      '--input',
      'examples/loop-engineering/success/loop-input.json',
      '--output-json',
      '../outside-loop-summary.json',
    ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('output JSON must stay within the working directory');
  });

  it('rejects schema-invalid loop input before producing a summary', () => {
    const outputDir = tempDir('loop-runner-invalid-input-');
    const inputPath = join(outputDir, 'invalid-input.json');
    const input = readJson('examples/loop-engineering/success/loop-input.json');
    input.iterations[0].validation.actualStatus = 'red';
    writeFileSync(inputPath, `${JSON.stringify(input, null, 2)}\n`);

    expect(() => buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      inputPath,
      '--generated-at',
      generatedAt,
      '--no-write',
    ]))).toThrow(/loop input schema validation failed/);
    rmSync(outputDir, { recursive: true, force: true });
  });

  it('rejects embedded reference paths that escape the working directory', () => {
    const outputDir = tempDir('loop-runner-reference-path-');
    const inputPath = join(outputDir, 'external-reference-input.json');
    const input = readJson('examples/loop-engineering/success/loop-input.json');
    input.execPlan.path = '../outside-exec-plan.json';
    writeFileSync(inputPath, `${JSON.stringify(input, null, 2)}\n`);

    expect(() => buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      inputPath,
      '--generated-at',
      generatedAt,
      '--no-write',
    ]))).toThrow(/execPlan[.]path must stay within the working directory/);
    rmSync(outputDir, { recursive: true, force: true });
  });

  it('rejects escaping raw-output and evidence paths with the same reference-path guard', () => {
    const outputDir = tempDir('loop-runner-evidence-path-');
    const rawOutputInputPath = join(outputDir, 'external-raw-output-input.json');
    const evidenceInputPath = join(outputDir, 'external-evidence-input.json');
    const rawOutputInput = readJson('examples/loop-engineering/success/loop-input.json');
    rawOutputInput.iterations[0].validation.rawOutputPath = '../outside-raw-output.json';
    writeFileSync(rawOutputInputPath, `${JSON.stringify(rawOutputInput, null, 2)}\n`);

    expect(() => buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      rawOutputInputPath,
      '--generated-at',
      generatedAt,
      '--no-write',
    ]))).toThrow(/validation[.]rawOutputPath must stay within the working directory/);

    const evidenceInput = readJson('examples/loop-engineering/success/loop-input.json');
    evidenceInput.iterations[0].observedEvidence[0].path = '../outside-evidence.json';
    writeFileSync(evidenceInputPath, `${JSON.stringify(evidenceInput, null, 2)}\n`);

    expect(() => buildLoopRun(parseArgs([
      'node',
      scriptPath,
      '--input',
      evidenceInputPath,
      '--generated-at',
      generatedAt,
      '--no-write',
    ]))).toThrow(/observedEvidence\[0\][.]path must stay within the working directory/);
    rmSync(outputDir, { recursive: true, force: true });
  });

  it('rejects symbolic-link output files before writing reports', () => {
    const sandbox = tempDir('loop-runner-output-link-');
    const workRoot = join(sandbox, 'work');
    const outsideRoot = join(sandbox, 'outside');
    const outputDir = join(workRoot, 'artifacts', 'loop');
    const reportPath = join(outputDir, 'loop-run-summary.json');
    mkdirSync(outputDir, { recursive: true });
    mkdirSync(outsideRoot, { recursive: true });
    try {
      symlinkSync(join(outsideRoot, 'missing-report.json'), reportPath, 'file');
    } catch {
      rmSync(sandbox, { recursive: true, force: true });
      return;
    }

    try {
      expect(() => run(parseArgs([
        'node',
        scriptPath,
        '--input',
        'examples/loop-engineering/success/loop-input.json',
        '--generated-at',
        generatedAt,
        '--output-json',
        reportPath,
        '--output-md',
        join(outputDir, 'loop-run-summary.md'),
      ]))).toThrow(/output JSON must not be a symbolic link/);
      expect(existsSync(join(outsideRoot, 'missing-report.json'))).toBe(false);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
