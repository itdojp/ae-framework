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

  it('writes discovery rollout status, counters, and artifacts', async () => {
    const outputDir = join(workdir, 'artifacts', 'discovery-pack');
    const validateReportJsonPath = join(outputDir, 'discovery-pack-validate-report.json');
    const validateReportMarkdownPath = join(outputDir, 'discovery-pack-validate-report.md');
    const compileReportJsonPath = join(outputDir, 'discovery-pack-compile-report.json');
    const compileReportMarkdownPath = join(outputDir, 'discovery-pack-compile-report.md');
    const planSpecPath = join(outputDir, 'plan-to-spec-normalized.md');
    await mkdir(outputDir, { recursive: true });
    await writeFile(validateReportJsonPath, '{}\n', 'utf8');
    await writeFile(validateReportMarkdownPath, '# validate\n', 'utf8');
    await writeFile(compileReportJsonPath, '{}\n', 'utf8');
    await writeFile(compileReportMarkdownPath, '# compile\n', 'utf8');
    await writeFile(planSpecPath, '# plan\n', 'utf8');

    const { result, summaryPath } = runWriteSummary({
      DISCOVERY_PACK_MODE: 'strict',
      DISCOVERY_PACK_REASON: 'label:enforce-discovery',
      DISCOVERY_PACK_SOURCE_PRESENT: '1',
      DISCOVERY_PACK_STRICT_APPROVED: '1',
      DISCOVERY_PACK_FAIL_ON:
        'blocking-open-questions,orphan-approved-requirements,orphan-approved-business-use-cases',
      DISCOVERY_PACK_VALIDATION_STATUS: 'success',
      DISCOVERY_PACK_VALIDATION_NOTES:
        'mode=strict;reason=label:enforce-discovery;report=warn;blocking_open_questions=1;orphan_requirements=2;orphan_business_use_cases=3',
      DISCOVERY_PACK_COMPILE_STATUS: 'success',
      DISCOVERY_PACK_COMPILE_NOTES:
        'target=plan-spec;report=warn;selected=8;excluded_by_status=2;skipped_by_target=0',
      DISCOVERY_PACK_REPORT_STATUS: 'warn',
      DISCOVERY_PACK_COMPILE_REPORT_STATUS: 'warn',
      DISCOVERY_PACK_SCANNED_FILES: '4',
      DISCOVERY_PACK_WARNING_FILES: '1',
      DISCOVERY_PACK_FAILED_FILES: '0',
      DISCOVERY_PACK_BLOCKING_OPEN_QUESTIONS: '1',
      DISCOVERY_PACK_ORPHAN_APPROVED_REQUIREMENTS: '2',
      DISCOVERY_PACK_ORPHAN_APPROVED_BUSINESS_USE_CASES: '3',
      DISCOVERY_PACK_COMPILE_SELECTED_COUNT: '8',
      DISCOVERY_PACK_COMPILE_EXCLUDED_BY_STATUS_COUNT: '2',
      DISCOVERY_PACK_COMPILE_SKIPPED_BY_TARGET_COUNT: '0',
      DISCOVERY_PACK_VALIDATE_REPORT_JSON_PATH: validateReportJsonPath,
      DISCOVERY_PACK_VALIDATE_REPORT_MD_PATH: validateReportMarkdownPath,
      DISCOVERY_PACK_COMPILE_REPORT_JSON_PATH: compileReportJsonPath,
      DISCOVERY_PACK_COMPILE_REPORT_MD_PATH: compileReportMarkdownPath,
      DISCOVERY_PACK_PLAN_SPEC_PATH: planSpecPath,
    });
    expect(result.status).toBe(0);

    const summary = JSON.parse(await readFile(summaryPath, 'utf8'));
    expect(summary.steps.discoveryPackValidation).toEqual({
      status: 'success',
      notes:
        'mode=strict;reason=label:enforce-discovery;report=warn;blocking_open_questions=1;orphan_requirements=2;orphan_business_use_cases=3',
    });
    expect(summary.steps.discoveryPackCompile).toEqual({
      status: 'success',
      notes: 'target=plan-spec;report=warn;selected=8;excluded_by_status=2;skipped_by_target=0',
    });
    expect(summary.discoveryPack).toEqual({
      mode: 'strict',
      reason: 'label:enforce-discovery',
      sourcePresent: true,
      strictApproved: true,
      failOn: [
        'blocking-open-questions',
        'orphan-approved-requirements',
        'orphan-approved-business-use-cases',
      ],
      validateStatus: 'warn',
      compileStatus: 'warn',
      scannedFiles: 4,
      warningFiles: 1,
      failedFiles: 0,
      blockingOpenQuestions: 1,
      orphanApprovedRequirements: 2,
      orphanApprovedBusinessUseCases: 3,
      compileSelectedCount: 8,
      compileExcludedByStatusCount: 2,
      compileSkippedByTargetCount: 0,
    });
    expect(summary.artifacts.discoveryPackValidateReportJson).toBe(validateReportJsonPath);
    expect(summary.artifacts.discoveryPackValidateReportMarkdown).toBe(validateReportMarkdownPath);
    expect(summary.artifacts.discoveryPackCompileReportJson).toBe(compileReportJsonPath);
    expect(summary.artifacts.discoveryPackCompileReportMarkdown).toBe(compileReportMarkdownPath);
    expect(summary.artifacts.discoveryPackPlanSpec).toBe(planSpecPath);

    const validateResult = spawnSync(
      process.execPath,
      [validateSummaryScript, summaryPath, verifyLiteSummarySchemaPath],
      { cwd: repoRoot },
    );
    expect(validateResult.status).toBe(0);
  });
});
