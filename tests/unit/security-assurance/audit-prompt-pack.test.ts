import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { generateSecurityAuditPromptPack } from '../../../src/security/assurance/audit-prompt-pack.js';
import { validateSecurityAuditPromptPackSemantics } from '../../../scripts/ci/lib/security-assurance-contract.mjs';

const tasksPath = 'fixtures/security-assurance/sample.security-audit-tasks.json';
const codeMapPath = 'fixtures/security-assurance/sample.security-code-map.json';
const claimsPath = 'fixtures/security-assurance/sample.security-claims.json';
const generatedAt = '2026-05-07T00:00:00.000Z';
const repoRoot = resolve('.');
const cliPath = resolve(repoRoot, 'src/cli/index.ts');

const readJson = <T>(path: string): T => JSON.parse(readFileSync(path, 'utf8')) as T;

const writeJson = (filePath: string, value: unknown) => {
  writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
};

const buildSchemaValidator = () => {
  const schema = readJson('schema/security-audit-prompt-pack-v1.schema.json');
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
};

describe('security audit prompt pack producer', () => {
  it('generates schema-valid Codex-ready prompt pack artifacts without external LLM calls', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-security-audit-prompt-pack-'));
    try {
      const result = await generateSecurityAuditPromptPack(tasksPath, codeMapPath, claimsPath, outDir, { generatedAt });

      expect(result.promptPack).toMatchObject({
        schemaVersion: 'security-audit-prompt-pack/v1',
        generatedAt,
        summary: {
          totalTasks: 1,
          readyTasks: 1,
          blockedTasks: 0,
          totalCandidateLocations: 1,
          totalWarnings: 0,
        },
      });
      expect(result.outputPaths.prompts).toHaveLength(1);
      expect(existsSync(result.outputPaths.promptPack)).toBe(true);
      expect(existsSync(result.outputPaths.summaryMarkdown)).toBe(true);
      expect(existsSync(result.outputPaths.prompts[0])).toBe(true);

      const validate = buildSchemaValidator();
      expect(validate(result.promptPack), JSON.stringify(validate.errors)).toBe(true);
      expect(validateSecurityAuditPromptPackSemantics(result.promptPack)).toHaveLength(0);

      const prompt = readFileSync(result.outputPaths.prompts[0], 'utf8');
      expect(prompt).toContain('# Security proof-attempt audit task');
      expect(prompt).toContain('## Claim');
      expect(prompt).toContain('## Scope and trust boundary');
      expect(prompt).toContain('1. Map:');
      expect(prompt).toContain('2. Prove:');
      expect(prompt).toContain('3. Stress-Test:');
      expect(prompt).toContain('4. Report:');
      expect(prompt).toContain('Do not treat any result as a confirmed vulnerability.');
      expect(prompt).toContain('Report only candidate findings.');
      expect(prompt).toContain('Do not generate exploit automation or weaponized PoC.');
      expect(prompt).toContain('Return JSON compatible with a security-audit-response-fixture/v1 response item.');
      expect(prompt).toContain('For `no-finding`, omit the `finding` object and keep the rationale explicit.');
      expect(prompt).toContain('"result": "finding"');
      expect(prompt).not.toContain('"finding | no-finding"');
      expect(prompt).toContain('src/cache.ts:7-15 (buildCacheKey)');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('marks prompt tasks blocked when candidate locations are unavailable', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-security-audit-prompt-pack-blocked-'));
    const outDir = join(fixtureDir, 'out');
    try {
      const tasks = readJson<{ tasks: Array<Record<string, unknown>> }>(tasksPath);
      tasks.tasks[0].status = 'blocked-no-candidate-location';
      tasks.tasks[0].candidateLocations = [];
      const localTasksPath = join(fixtureDir, 'security-audit-tasks.json');
      writeJson(localTasksPath, tasks);

      const codeMap = readJson<{ mappings: Array<Record<string, unknown>> }>(codeMapPath);
      codeMap.mappings[0].candidateLocations = [];
      const localCodeMapPath = join(fixtureDir, 'security-code-map.json');
      writeJson(localCodeMapPath, codeMap);

      const result = await generateSecurityAuditPromptPack(localTasksPath, localCodeMapPath, claimsPath, outDir, { generatedAt });

      expect(result.promptPack.summary).toMatchObject({
        readyTasks: 0,
        blockedTasks: 1,
        totalCandidateLocations: 0,
        totalWarnings: 1,
      });
      expect(result.warnings).toEqual([
        expect.objectContaining({ code: 'missing-candidate-location' }),
      ]);
      expect(result.promptPack.tasks[0]).toMatchObject({
        status: 'blocked',
        sourceTaskStatus: 'blocked-no-candidate-location',
        warnings: [expect.objectContaining({ code: 'missing-candidate-location' })],
      });
      expect(validateSecurityAuditPromptPackSemantics(result.promptPack)).toHaveLength(0);
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
    }
  });

  it('marks tasks ready when candidate locations are recovered from code-map input', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-security-audit-prompt-pack-recovered-'));
    const outDir = join(fixtureDir, 'out');
    try {
      const tasks = readJson<{ tasks: Array<Record<string, unknown>> }>(tasksPath);
      tasks.tasks[0].status = 'blocked-missing-code-map';
      tasks.tasks[0].candidateLocations = [];
      const localTasksPath = join(fixtureDir, 'security-audit-tasks.json');
      writeJson(localTasksPath, tasks);

      const result = await generateSecurityAuditPromptPack(localTasksPath, codeMapPath, claimsPath, outDir, { generatedAt });

      expect(result.promptPack.summary).toMatchObject({
        readyTasks: 1,
        blockedTasks: 0,
        totalCandidateLocations: 1,
        totalWarnings: 1,
      });
      expect(result.promptPack.tasks[0]).toMatchObject({
        status: 'ready',
        sourceTaskStatus: 'blocked-missing-code-map',
        warnings: [expect.objectContaining({ code: 'candidate-location-recovered-from-code-map' })],
      });
      expect(result.warnings).toEqual([
        expect.objectContaining({ code: 'candidate-location-recovered-from-code-map' }),
      ]);
      expect(validateSecurityAuditPromptPackSemantics(result.promptPack)).toHaveLength(0);
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
    }
  });

  it('exposes ae security audit-prompt through the CLI and npm script entrypoint', () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-security-audit-prompt-pack-cli-'));
    try {
      const result = spawnSync(
        'pnpm',
        [
          '-s',
          'exec',
          'tsx',
          cliPath,
          'security',
          'audit-prompt',
          '--tasks',
          tasksPath,
          '--code-map',
          codeMapPath,
          '--claims',
          claimsPath,
          '--out',
          outDir,
          '--generated-at',
          generatedAt,
        ],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status, `${result.stdout}\n${result.stderr}`).toBe(0);
      expect(result.stdout).toContain('Security audit prompt pack generated');
      expect(result.stdout).toContain('Prompt tasks: 1');
      expect(existsSync(join(outDir, 'security-audit-prompt-pack.json'))).toBe(true);
      expect(existsSync(join(outDir, 'prompts', 'SEC-AUDIT-TASK-001.md'))).toBe(true);
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });
});
