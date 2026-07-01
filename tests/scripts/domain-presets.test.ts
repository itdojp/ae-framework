import { describe, expect, it } from 'vitest';
import { existsSync, readFileSync, rmSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { randomUUID } from 'node:crypto';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/domain-presets/render-preset.mjs');
const schemaPath = resolve(repoRoot, 'schema/domain-assurance-preset.schema.json');
const reportSchemaPath = resolve(repoRoot, 'schema/domain-assurance-preset-report.schema.json');
const generatedAt = '2026-07-01T00:00:00.000Z';

const presetPaths = [
  'templates/domain-presets/web-api-bff/preset.json',
  'templates/domain-presets/event-driven-domain/preset.json',
  'templates/domain-presets/spec-led-brownfield/preset.json',
  'templates/domain-presets/high-assurance-critical-core/preset.json',
];

const deterministicCases = [
  {
    id: 'web-api-bff',
    presetPath: 'templates/domain-presets/web-api-bff/preset.json',
    expectedJsonPath: 'fixtures/domain-presets/web-api-bff/expected/domain-preset-report.json',
    expectedMarkdownPath: 'fixtures/domain-presets/web-api-bff/expected/domain-preset-report.md',
  },
  {
    id: 'event-driven-domain',
    presetPath: 'templates/domain-presets/event-driven-domain/preset.json',
    expectedJsonPath: 'fixtures/domain-presets/event-driven-domain/expected/domain-preset-report.json',
    expectedMarkdownPath: 'fixtures/domain-presets/event-driven-domain/expected/domain-preset-report.md',
  },
];

const runScript = (args: string[]) => spawnSync('node', [scriptPath, ...args], {
  cwd: repoRoot,
  encoding: 'utf8',
  timeout: 120_000,
});

const readJson = (filePath: string) => JSON.parse(readFileSync(resolve(repoRoot, filePath), 'utf8'));

function compileSchema(schemaFilePath = schemaPath) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(JSON.parse(readFileSync(schemaFilePath, 'utf8')));
}

describe('domain assurance presets', () => {
  it('keeps all preset templates schema-valid and report-only', () => {
    const validate = compileSchema();

    for (const presetPath of presetPaths) {
      const preset = readJson(presetPath);
      expect(validate(preset), `${presetPath}: ${JSON.stringify(validate.errors)}`).toBe(true);
      expect(preset.reportOnly).toBe(true);
      expect(preset.integration).toMatchObject({
        contextPackRequired: true,
        execPlanRequired: true,
      });
      expect(preset.reuseContracts).toContain('context-pack/v1');
      expect(preset.reuseContracts).toContain('exec-plan/v2');
    }
  });

  for (const fixture of deterministicCases) {
    it(`renders deterministic offline evidence for ${fixture.id}`, () => {
      const outputRoot = resolve(repoRoot, 'artifacts', `domain-preset-${fixture.id}-${randomUUID()}`);
      const outputJson = join(outputRoot, 'domain-preset-report.json');
      const outputMd = join(outputRoot, 'domain-preset-report.md');

      try {
        const result = runScript([
          '--preset', resolve(repoRoot, fixture.presetPath),
          '--generated-at', generatedAt,
          '--output-json', outputJson,
          '--output-md', outputMd,
        ]);

        expect(result.status, result.stderr || result.stdout).toBe(0);
        expect(existsSync(outputJson)).toBe(true);
        expect(existsSync(outputMd)).toBe(true);

        const payload = JSON.parse(readFileSync(outputJson, 'utf8'));
        expect(payload).toEqual(readJson(fixture.expectedJsonPath));
        const validateReport = compileSchema(reportSchemaPath);
        expect(validateReport(payload), JSON.stringify(validateReport.errors)).toBe(true);
        expect(payload.collectionBoundaries).toMatchObject({
          externalApisCalled: false,
          generatedFromLocalTemplate: true,
        });
        expect(payload.preset.reportOnly).toBe(true);
        expect(payload.summary.contextPackRequired).toBe(true);
        expect(payload.summary.execPlanRequired).toBe(true);

        const markdown = readFileSync(outputMd, 'utf8');
        expect(markdown).toEqual(readFileSync(resolve(repoRoot, fixture.expectedMarkdownPath), 'utf8'));
        expect(markdown).toContain('No live external APIs were called.');
      } finally {
        rmSync(outputRoot, { recursive: true, force: true });
      }
    });
  }

  it('supports --no-write for read-only preset validation and rendering', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `domain-preset-no-write-${randomUUID()}`);
    const outputJson = join(outputRoot, 'domain-preset-report.json');
    const outputMd = join(outputRoot, 'domain-preset-report.md');

    try {
      const result = runScript([
        '--preset', resolve(repoRoot, 'templates/domain-presets/web-api-bff/preset.json'),
        '--generated-at', generatedAt,
        '--output-json', outputJson,
        '--output-md', outputMd,
        '--no-write',
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('Domain preset report validated without writing files.');
      expect(existsSync(outputJson)).toBe(false);
      expect(existsSync(outputMd)).toBe(false);
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('rejects preset paths outside the project root', () => {
    const result = runScript(['--preset', '../outside-domain-preset.json', '--no-write']);

    expect(result.status).not.toBe(0);
    expect(result.stderr).toContain('--preset must stay within --project-root');
  });
});
