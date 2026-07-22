import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const validateScript = join(process.cwd(), 'scripts/ci/validate-formal-summary-v2.mjs');
const schemaPath = join(process.cwd(), 'schema/formal-summary-v2.schema.json');
const fixturePath = join(process.cwd(), 'fixtures/formal/sample.formal-summary-v2.json');

async function validSummary(): Promise<any> {
  return JSON.parse(await readFile(fixturePath, 'utf8'));
}

describe('validate-formal-summary-v2 CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'formal-summary-v2-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('accepts valid formal summary v2', async () => {
    const summaryPath = join(workdir, 'formal-summary-v2.json');
    const summary = await validSummary();
    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(0);
    expect(result.stderr.toString()).toBe('');
  });

  it('fails for invalid contractId', async () => {
    const summaryPath = join(workdir, 'formal-summary-v2.json');
    const summary = await validSummary();
    summary.contractId = 'formal-summary.v1';
    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('schema validation failed');
  });

  it('fails when present execution evidence omits scope or assumptions', async () => {
    const summaryPath = join(workdir, 'formal-summary-v2.json');
    const summary = await validSummary();
    delete summary.results[0].executionEvidence.scope;
    delete summary.results[0].executionEvidence.assumptions;
    await writeFile(summaryPath, JSON.stringify(summary));

    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], {
      cwd: workdir,
    });
    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('schema validation failed');
  });

  it.each([
    ['artifactStatus omitted', (summary: any) => { delete summary.artifactStatus; }],
    ['artifactStatus synthetic', (summary: any) => { summary.artifactStatus = 'synthetic'; }],
    ['unknown producer', (summary: any) => { summary.producer.id = 'ae.formal.fake-generator'; }],
    ['runner-reported evidence without adapter verification', (summary: any) => {
      summary.results[0].executionEvidence.provenance = 'runner-reported';
      delete summary.results[0].executionEvidence.adapter;
    }],
    ['verified version with unavailable source', (summary: any) => {
      summary.results[0].executionEvidence.tool.version = '6.2.0';
      summary.results[0].executionEvidence.tool.versionStatus = 'verified';
      summary.results[0].executionEvidence.tool.versionSource = 'unavailable';
    }],
    ['schema-invalid evidence', (summary: any) => { summary.results[0].executionEvidence.result.code = '0'; }],
    ['unknown version marked complete', (summary: any) => {
      summary.results[0].executionEvidence.tool.version = 'unknown';
      summary.results[0].executionEvidence.tool.versionStatus = 'unknown';
      summary.results[0].executionEvidence.tool.versionSource = 'unavailable';
    }],
  ])('fails for %s', async (_name, mutate) => {
    const summaryPath = join(workdir, 'formal-summary-v2.json');
    const summary = await validSummary();
    mutate(summary);
    await writeFile(summaryPath, JSON.stringify(summary));
    const result = spawnSync(process.execPath, [validateScript, summaryPath, schemaPath], { cwd: workdir });
    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('schema validation failed');
  });
});
