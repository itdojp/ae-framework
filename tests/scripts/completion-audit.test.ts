import { describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { randomUUID } from 'node:crypto';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/audit/render-completion-audit.mjs');
const inputPath = resolve(repoRoot, 'fixtures/audit/completion/pr-3566-closeout.input.json');
const expectedJsonPath = resolve(repoRoot, 'fixtures/audit/completion/expected/completion-audit-report.json');
const expectedMarkdownPath = resolve(repoRoot, 'fixtures/audit/completion/expected/completion-audit-report.md');
const schemaPath = resolve(repoRoot, 'schema/completion-audit-report.schema.json');
const generatedAt = '2026-07-01T00:00:00.000Z';

const runScript = (args: string[]) => spawnSync('node', [scriptPath, ...args], {
  cwd: repoRoot,
  encoding: 'utf8',
  timeout: 120_000,
});

const readJson = (filePath: string) => JSON.parse(readFileSync(filePath, 'utf8'));

function compileSchema() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(readJson(schemaPath));
}

describe('completion audit renderer', () => {
  it('renders deterministic PR closeout evidence with required checks separated from advisory findings', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `completion-audit-test-${randomUUID()}`);
    const outputJson = join(outputRoot, 'completion-audit-report.json');
    const outputMd = join(outputRoot, 'completion-audit-report.md');

    try {
      const result = runScript([
        '--input', inputPath,
        '--generated-at', generatedAt,
        '--output-json', outputJson,
        '--output-md', outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(existsSync(outputJson)).toBe(true);
      expect(existsSync(outputMd)).toBe(true);

      const payload = readJson(outputJson);
      expect(payload).toEqual(readJson(expectedJsonPath));
      expect(payload.conclusion).toMatchObject({
        status: 'merged-with-advisory-findings',
        requiredChecksPassed: true,
        advisoryFindingsPresent: true,
        mergeApprovedByAudit: false,
      });
      expect(payload.summary).toMatchObject({
        requiredCheckCount: 3,
        requiredChecksPassedCount: 3,
        advisoryWorkflowFindingCount: 1,
        staleWorkflowRunCount: 1,
      });

      const validate = compileSchema();
      expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toEqual(readFileSync(expectedMarkdownPath, 'utf8'));
      expect(markdown).toContain('Required merge checks passed');
      expect(markdown).toContain('Advisory workflow findings');
      expect(markdown).toContain('Audit grants approval | no');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('supports --no-write for comment-preview validation', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `completion-audit-no-write-${randomUUID()}`);
    const outputJson = join(outputRoot, 'completion-audit-report.json');
    const outputMd = join(outputRoot, 'completion-audit-report.md');

    try {
      const result = runScript([
        '--input', inputPath,
        '--generated-at', generatedAt,
        '--output-json', outputJson,
        '--output-md', outputMd,
        '--no-write',
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('Completion audit report validated without writing files.');
      expect(result.stdout).toContain('requiredChecksPassed: true');
      expect(result.stdout).toContain('advisoryFindings: 1');
      expect(existsSync(outputJson)).toBe(false);
      expect(existsSync(outputMd)).toBe(false);
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('rejects invalid timestamps and malformed required-check arrays', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `completion-audit-invalid-${randomUUID()}`);
    const invalidInputPath = join(outputRoot, 'invalid.input.json');

    try {
      mkdirSync(outputRoot, { recursive: true });
      const invalidTimestamp = readJson(inputPath);
      invalidTimestamp.requiredMergeChecks[0].completedAt = '2026-02-31T00:00:00.000Z';
      writeFileSync(invalidInputPath, `${JSON.stringify(invalidTimestamp, null, 2)}\n`, 'utf8');

      const invalidDate = runScript([
        '--input', invalidInputPath,
        '--generated-at', generatedAt,
        '--no-write',
      ]);
      expect(invalidDate.status).not.toBe(0);
      expect(invalidDate.stderr).toContain('requiredMergeChecks[0].completedAt must be a valid RFC3339 date-time');

      const invalidRequiredChecks = readJson(inputPath);
      invalidRequiredChecks.requiredMergeChecks = {};
      writeFileSync(invalidInputPath, `${JSON.stringify(invalidRequiredChecks, null, 2)}\n`, 'utf8');

      const malformedChecks = runScript([
        '--input', invalidInputPath,
        '--generated-at', generatedAt,
        '--no-write',
      ]);
      expect(malformedChecks.status).not.toBe(0);
      expect(malformedChecks.stderr).toContain('requiredMergeChecks must be an array');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('rejects malformed optional arrays and report-boundary constants', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `completion-audit-boundary-${randomUUID()}`);
    const invalidInputPath = join(outputRoot, 'invalid.input.json');

    try {
      mkdirSync(outputRoot, { recursive: true });
      const malformedAdvisoryRuns = readJson(inputPath);
      malformedAdvisoryRuns.advisoryWorkflowRuns = {};
      writeFileSync(invalidInputPath, `${JSON.stringify(malformedAdvisoryRuns, null, 2)}\n`, 'utf8');

      const advisoryResult = runScript([
        '--input', invalidInputPath,
        '--generated-at', generatedAt,
        '--no-write',
      ]);
      expect(advisoryResult.status).not.toBe(0);
      expect(advisoryResult.stderr).toContain('advisoryWorkflowRuns must be an array');

      const liveApiCalled = readJson(inputPath);
      liveApiCalled.collectionBoundaries.liveGitHubApiCalled = true;
      writeFileSync(invalidInputPath, `${JSON.stringify(liveApiCalled, null, 2)}\n`, 'utf8');

      const boundaryResult = runScript([
        '--input', invalidInputPath,
        '--generated-at', generatedAt,
        '--no-write',
      ]);
      expect(boundaryResult.status).not.toBe(0);
      expect(boundaryResult.stderr).toContain('collectionBoundaries.liveGitHubApiCalled must be false');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('rejects input paths outside the project root', () => {
    const result = runScript(['--input', '../outside-completion-audit.json', '--no-write']);

    expect(result.status).not.toBe(0);
    expect(result.stderr).toContain('--input must stay within --project-root');
  });
});
