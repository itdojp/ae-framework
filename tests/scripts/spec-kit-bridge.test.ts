import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { describe, expect, it } from 'vitest';

import {
  buildAnalysis,
  parseArgs,
  run,
} from '../../scripts/spec-kit/import-feature.mjs';
import { validateExecPlanV2Payload } from '../../scripts/exec-plan/validate-v2.mjs';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/spec-kit/import-feature.mjs');
const reportSchema = JSON.parse(readFileSync(resolve('schema/spec-kit-bridge-report.schema.json'), 'utf8'));
const contextPackSchema = JSON.parse(readFileSync(resolve('schema/context-pack-v1.schema.json'), 'utf8'));
const execPlanSchema = JSON.parse(readFileSync(resolve('schema/exec-plan.v2.schema.json'), 'utf8'));
const generatedAt = '2026-06-30T00:00:00.000Z';

function readJson(path: string) {
  return JSON.parse(readFileSync(resolve(path), 'utf8'));
}

function makeAjv() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv;
}

function validateWithSchema(schema: unknown, payload: unknown) {
  const ajv = makeAjv();
  const validate = ajv.compile(schema);
  expect(validate(payload), JSON.stringify(validate.errors, null, 2)).toBe(true);
}

describe('Spec Kit bridge importer', () => {
  it('imports the greenfield Spec Kit fixture into report, Context Pack, and ExecPlan v2 artifacts', () => {
    const analysis = buildAnalysis(parseArgs([
      'node',
      'scripts/spec-kit/import-feature.mjs',
      '--feature-dir',
      'fixtures/spec-kit/greenfield/specs/001-reservation-approval',
      '--output-dir',
      'fixtures/spec-kit/greenfield/expected',
      '--generated-at',
      generatedAt,
      '--no-write',
    ]));

    expect(analysis.report).toEqual(readJson('fixtures/spec-kit/greenfield/expected/spec-kit-bridge-report.json'));
    expect(analysis.contextPack).toEqual(readJson('fixtures/spec-kit/greenfield/expected/context-pack.import.json'));
    expect(analysis.execPlan).toEqual(readJson('fixtures/spec-kit/greenfield/expected/exec-plan.v2.json'));
    expect(analysis.report).toMatchObject({
      result: 'pass',
      summary: { requirements: 3, userStories: 2, tasks: 8, contracts: 1, findings: 0 },
    });
    expect(analysis.execPlan?.context.specKitRefs.map((ref: { kind: string }) => ref.kind)).toEqual([
      'spec-kit-spec',
      'spec-kit-plan',
      'spec-kit-task',
      'artifact-contract',
    ]);
    expect(analysis.contextPack?.acceptance_tests.map((test: { id: string }) => test.id)).toEqual(expect.arrayContaining([
      'AT-FR-001',
      'AT-US1',
    ]));

    validateWithSchema(reportSchema, analysis.report);
    validateWithSchema(contextPackSchema, analysis.contextPack);
    validateWithSchema(execPlanSchema, analysis.execPlan);
    expect(validateExecPlanV2Payload(analysis.execPlan, execPlanSchema)).toMatchObject({ result: 'pass', semanticErrors: [] });
  });

  it('keeps brownfield missing and ambiguous mappings report-only', () => {
    const analysis = buildAnalysis(parseArgs([
      'node',
      'scripts/spec-kit/import-feature.mjs',
      '--feature-dir',
      'fixtures/spec-kit/brownfield/specs/042-inventory-modernization',
      '--output-dir',
      'fixtures/spec-kit/brownfield/expected',
      '--generated-at',
      generatedAt,
      '--no-write',
    ]));

    expect(analysis.report.result).toBe('warning');
    expect(analysis.report.findings.map((finding: { code: string }) => finding.code)).toEqual([
      'missing-contracts',
      'ambiguous-task-story',
    ]);
    expect(analysis.report).toEqual(readJson('fixtures/spec-kit/brownfield/expected/spec-kit-bridge-report.json'));
    validateWithSchema(reportSchema, analysis.report);
    expect(validateExecPlanV2Payload(analysis.execPlan, execPlanSchema)).toMatchObject({ result: 'pass', semanticErrors: [] });
  });


  it('returns a schema-valid fail report for an unreadable feature directory', () => {
    const analysis = buildAnalysis(parseArgs([
      'node',
      'scripts/spec-kit/import-feature.mjs',
      '--feature-dir',
      'fixtures/spec-kit/missing/specs/000-missing-feature',
      '--output-dir',
      '.codex-local/tmp/spec-kit-missing',
      '--generated-at',
      generatedAt,
      '--no-write',
    ]));

    expect(analysis.report).toMatchObject({
      result: 'fail',
      summary: { findings: 1 },
    });
    expect(analysis.report.findings[0]).toMatchObject({ code: 'missing-feature-dir', severity: 'error' });
    validateWithSchema(reportSchema, analysis.report);
    expect(analysis.contextPack).toBeNull();
    expect(analysis.execPlan).toBeNull();
  });

  it('rejects feature and output paths that escape the project root', () => {
    expect(() => parseArgs([
      'node',
      'scripts/spec-kit/import-feature.mjs',
      '--feature-dir',
      '../outside-feature',
      '--no-write',
    ])).toThrow(/--feature-dir must stay within --project-root/);

    expect(() => parseArgs([
      'node',
      'scripts/spec-kit/import-feature.mjs',
      '--output-dir',
      resolve(repoRoot, '..', 'outside-output'),
      '--no-write',
    ])).toThrow(/--output-dir must stay within --project-root/);

    expect(() => parseArgs([
      'node',
      'scripts/spec-kit/import-feature.mjs',
      '--report-json',
      '../spec-kit-bridge-report.json',
      '--no-write',
    ])).toThrow(/--report-json must stay within --project-root/);

    const result = spawnSync('node', [
      scriptPath,
      '--feature-dir',
      '../outside-feature',
      '--no-write',
    ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });
    expect(result.status).toBe(1);
    expect(result.stderr).toContain('--feature-dir must stay within --project-root');
  });

  it('rejects symlinked feature and output paths that resolve outside the project root', () => {
    const root = resolve('.codex-local/tmp');
    mkdirSync(root, { recursive: true });
    const sandbox = mkdtempSync(join(root, 'spec-kit-bridge-symlink-'));
    const workRoot = join(sandbox, 'work');
    const outsideRoot = join(sandbox, 'outside');
    mkdirSync(workRoot, { recursive: true });
    mkdirSync(outsideRoot, { recursive: true });

    try {
      symlinkSync(outsideRoot, join(workRoot, 'feature-link'), 'dir');
    } catch {
      rmSync(sandbox, { recursive: true, force: true });
      return;
    }

    try {
      expect(() => parseArgs([
        'node',
        'scripts/spec-kit/import-feature.mjs',
        '--project-root',
        workRoot,
        '--feature-dir',
        'feature-link',
        '--no-write',
      ])).toThrow(/--feature-dir resolves outside --project-root/);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects symbolic-link output files before writing bridge artifacts', () => {
    const root = resolve('.codex-local/tmp');
    mkdirSync(root, { recursive: true });
    const sandbox = mkdtempSync(join(root, 'spec-kit-bridge-output-link-'));
    const workRoot = join(sandbox, 'work');
    const outsideRoot = join(sandbox, 'outside');
    const outputDir = join(workRoot, 'artifacts', 'spec-kit');
    const reportPath = join(outputDir, 'spec-kit-bridge-report.json');
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
        'scripts/spec-kit/import-feature.mjs',
        '--project-root',
        workRoot,
        '--feature-dir',
        'missing-feature',
        '--output-dir',
        'artifacts/spec-kit',
        '--generated-at',
        generatedAt,
      ]))).toThrow(/--report-json must not be a symbolic link/);
      expect(existsSync(join(outsideRoot, 'missing-report.json'))).toBe(false);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('writes bridge artifacts through the CLI and supports pnpm argument separators', () => {
    const root = resolve('.codex-local/tmp');
    mkdirSync(root, { recursive: true });
    const sandbox = mkdtempSync(join(root, 'spec-kit-bridge-'));
    try {
      const result = spawnSync('node', [
        scriptPath,
        '--',
        '--feature-dir',
        'fixtures/spec-kit/greenfield/specs/001-reservation-approval',
        '--output-dir',
        sandbox,
        '--generated-at',
        generatedAt,
      ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const reportPath = join(sandbox, 'spec-kit-bridge-report.json');
      const markdownPath = join(sandbox, 'spec-kit-bridge-report.md');
      const contextPath = join(sandbox, 'context-pack.import.json');
      const execPlanPath = join(sandbox, 'exec-plan.v2.json');
      expect(existsSync(reportPath)).toBe(true);
      expect(existsSync(markdownPath)).toBe(true);
      expect(existsSync(contextPath)).toBe(true);
      expect(existsSync(execPlanPath)).toBe(true);
      expect(readFileSync(markdownPath, 'utf8')).toContain('# Spec Kit Bridge Report: Reservation Approval');
      expect(readJson(reportPath)).toMatchObject({ result: 'pass' });

      const contextResult = spawnSync('node', [
        'scripts/context-pack/validate.mjs',
        '--sources',
        contextPath,
        '--report-json',
        join(sandbox, 'context-pack-report.json'),
        '--report-md',
        join(sandbox, 'context-pack-report.md'),
      ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });
      expect(contextResult.status, contextResult.stderr || contextResult.stdout).toBe(0);

      const execPlanResult = spawnSync('node', [
        'scripts/exec-plan/validate-v2.mjs',
        '--file',
        execPlanPath,
        '--no-write',
      ], { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 });
      expect(execPlanResult.status, execPlanResult.stderr || execPlanResult.stdout).toBe(0);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
