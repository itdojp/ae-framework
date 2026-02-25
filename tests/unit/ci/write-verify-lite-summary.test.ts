import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const writeSummaryScript = resolve(repoRoot, 'scripts/ci/write-verify-lite-summary.mjs');
const validateSummaryScript = resolve(repoRoot, 'scripts/ci/validate-verify-lite-summary.mjs');
const verifyLiteSummarySchemaPath = resolve(repoRoot, 'schema/verify-lite-run-summary.schema.json');

describe('write-verify-lite-summary CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'write-verify-lite-summary-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  const runWriteSummary = (extraEnv: Record<string, string> = {}) => {
    const summaryPath = join(workdir, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json');
    const result = spawnSync(process.execPath, [writeSummaryScript, summaryPath], {
      cwd: workdir,
      env: {
        ...process.env,
        RUN_TIMESTAMP: '2026-02-24T00:00:00.000Z',
        ...extraEnv,
      },
    });
    return { result, summaryPath };
  };

  it('writes phase5 status and artifact paths when files exist', async () => {
    const phase5ReportJsonPath = join(workdir, 'artifacts', 'context-pack', 'context-pack-phase5-report.json');
    const phase5ReportMarkdownPath = join(workdir, 'artifacts', 'context-pack', 'context-pack-phase5-report.md');
    await mkdir(join(workdir, 'artifacts', 'context-pack'), { recursive: true });
    await writeFile(phase5ReportJsonPath, '{}\n', 'utf8');
    await writeFile(phase5ReportMarkdownPath, '# report\n', 'utf8');

    const { result, summaryPath } = runWriteSummary({
      CONTEXT_PACK_PHASE5_STATUS: 'success',
      CONTEXT_PACK_PHASE5_NOTES: 'validated context-pack phase5 templates;violations=0',
      CONTEXT_PACK_PHASE5_REPORT_JSON_PATH: phase5ReportJsonPath,
      CONTEXT_PACK_PHASE5_REPORT_MD_PATH: phase5ReportMarkdownPath,
    });
    expect(result.status).toBe(0);

    const summary = JSON.parse(await readFile(summaryPath, 'utf8'));
    expect(summary.steps.contextPackPhase5Validation).toEqual({
      status: 'success',
      notes: 'validated context-pack phase5 templates;violations=0',
    });
    expect(summary.artifacts.contextPackPhase5ReportJson).toBe(phase5ReportJsonPath);
    expect(summary.artifacts.contextPackPhase5ReportMarkdown).toBe(phase5ReportMarkdownPath);

    const validateResult = spawnSync(
      process.execPath,
      [validateSummaryScript, summaryPath, verifyLiteSummarySchemaPath],
      { cwd: repoRoot },
    );
    expect(validateResult.status).toBe(0);
  });

  it('keeps phase5 artifacts null when report files do not exist', async () => {
    const missingJsonPath = join(workdir, 'artifacts', 'context-pack', 'missing-phase5-report.json');
    const missingMarkdownPath = join(workdir, 'artifacts', 'context-pack', 'missing-phase5-report.md');
    const expectedNotes = `map_not_found:${join('spec', 'context-pack', 'phase5-templates.json')}`;

    const { result, summaryPath } = runWriteSummary({
      CONTEXT_PACK_PHASE5_STATUS: 'skipped',
      CONTEXT_PACK_PHASE5_NOTES: expectedNotes,
      CONTEXT_PACK_PHASE5_REPORT_JSON_PATH: missingJsonPath,
      CONTEXT_PACK_PHASE5_REPORT_MD_PATH: missingMarkdownPath,
    });
    expect(result.status).toBe(0);

    const summary = JSON.parse(await readFile(summaryPath, 'utf8'));
    expect(summary.steps.contextPackPhase5Validation).toEqual({
      status: 'skipped',
      notes: expectedNotes,
    });
    expect(summary.artifacts.contextPackPhase5ReportJson).toBeNull();
    expect(summary.artifacts.contextPackPhase5ReportMarkdown).toBeNull();

    const validateResult = spawnSync(
      process.execPath,
      [validateSummaryScript, summaryPath, verifyLiteSummarySchemaPath],
      { cwd: repoRoot },
    );
    expect(validateResult.status).toBe(0);
  });
});
