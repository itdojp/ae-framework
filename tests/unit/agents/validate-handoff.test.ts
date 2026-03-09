import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdtemp, rm, writeFile, readFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

const validateScript = join(process.cwd(), 'scripts/agents/validate-handoff.mjs');
const schemaPath = join(process.cwd(), 'schema/ae-handoff.schema.json');
const fixturePath = join(process.cwd(), 'fixtures/agents/sample.ae-handoff.json');

describe('validate-handoff CLI', () => {
  let workdir: string;

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'ae-handoff-'));
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('accepts valid AE-HANDOFF JSON', async () => {
    const handoffPath = join(workdir, 'ae-handoff.json');
    await writeFile(handoffPath, await readFile(fixturePath, 'utf8'));

    const result = spawnSync(process.execPath, [validateScript, handoffPath, schemaPath], {
      cwd: workdir,
    });

    expect(result.status).toBe(0);
    expect(result.stderr.toString()).toBe('');
  });

  it('fails when artifacts are missing', async () => {
    const handoffPath = join(workdir, 'ae-handoff.json');
    const fixture = JSON.parse(await readFile(fixturePath, 'utf8')) as {
      artifacts: unknown[];
    };
    fixture.artifacts = [];
    await writeFile(handoffPath, JSON.stringify(fixture));

    const result = spawnSync(process.execPath, [validateScript, handoffPath, schemaPath], {
      cwd: workdir,
    });

    expect(result.status).toBe(1);
    expect(result.stderr.toString()).toContain('schema validation failed');
    expect(result.stderr.toString()).toContain('/artifacts');
  });
});
