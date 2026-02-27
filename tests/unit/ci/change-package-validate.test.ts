import { afterEach, describe, expect, it } from 'vitest';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const validateScript = resolve(repoRoot, 'scripts/change-package/validate.mjs');
const schemaPath = resolve(repoRoot, 'schema/change-package.schema.json');
const fixturePath = resolve(repoRoot, 'fixtures/change-package/sample.change-package.json');
const workdirs: string[] = [];

async function createWorkdir(prefix: string): Promise<string> {
  const workdir = await mkdtemp(join(tmpdir(), prefix));
  workdirs.push(workdir);
  return workdir;
}

afterEach(async () => {
  await Promise.all(workdirs.splice(0).map((workdir) => rm(workdir, { recursive: true, force: true })));
});

async function loadFixture(): Promise<Record<string, unknown>> {
  const raw = await readFile(fixturePath, 'utf8');
  return JSON.parse(raw) as Record<string, unknown>;
}

describe('change-package validate', () => {
  it('passes in strict mode when required evidence is present', async () => {
    const workdir = await createWorkdir('change-package-validate-pass-');
    const inputPath = join(workdir, 'change-package.json');
    const outputJsonPath = join(workdir, 'validation.json');
    const outputMarkdownPath = join(workdir, 'validation.md');

    const fixture = await loadFixture();
    const evidence = (fixture.evidence as {
      items: Array<{ id: string; present: boolean }>;
      presentCount: number;
      missingCount: number;
    });
    evidence.items = evidence.items.map((item) => (item.id === 'verifyLiteSummary' ? { ...item, present: true } : item));
    evidence.presentCount = evidence.items.filter((item) => item.present).length;
    evidence.missingCount = evidence.items.length - evidence.presentCount;

    await writeFile(inputPath, `${JSON.stringify(fixture, null, 2)}\n`, 'utf8');

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', schemaPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--required-evidence', 'verifyLiteSummary',
      '--strict',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      result: string;
      errors: string[];
      warnings: string[];
    };
    expect(report.result).toBe('pass');
    expect(report.errors).toHaveLength(0);
    expect(report.warnings).toHaveLength(0);

    const markdown = await readFile(outputMarkdownPath, 'utf8');
    expect(markdown).toContain('Change Package Validation');
    expect(markdown).toContain('result: PASS');
  });

  it('fails in strict mode when required evidence is missing', async () => {
    const workdir = await createWorkdir('change-package-validate-fail-');
    const inputPath = join(workdir, 'change-package.json');
    const outputJsonPath = join(workdir, 'validation.json');
    const outputMarkdownPath = join(workdir, 'validation.md');

    const fixture = await loadFixture();
    const evidence = (fixture.evidence as {
      items: Array<{ id: string; present: boolean }>;
      presentCount: number;
      missingCount: number;
    });
    evidence.items = evidence.items.map((item) => (item.id === 'verifyLiteSummary' ? { ...item, present: false } : item));
    evidence.presentCount = evidence.items.filter((item) => item.present).length;
    evidence.missingCount = evidence.items.length - evidence.presentCount;

    await writeFile(inputPath, `${JSON.stringify(fixture, null, 2)}\n`, 'utf8');

    const result = spawnSync(process.execPath, [
      validateScript,
      '--file', inputPath,
      '--schema', schemaPath,
      '--output-json', outputJsonPath,
      '--output-md', outputMarkdownPath,
      '--required-evidence', 'verifyLiteSummary',
      '--strict',
    ], {
      cwd: repoRoot,
      encoding: 'utf8',
    });

    expect(result.status).toBe(1);

    const report = JSON.parse(await readFile(outputJsonPath, 'utf8')) as {
      result: string;
      errors: string[];
      warnings: string[];
    };
    expect(report.result).toBe('fail');
    expect(report.errors.some((error) => error.includes('missing required evidence'))).toBe(true);
    expect(report.warnings).toHaveLength(0);
  });
});
