import { describe, it, expect } from 'vitest';
import { mkdtemp, writeFile, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);

async function withTempDir(fn) {
  const dir = await mkdtemp(join(tmpdir(), 'kvonce-validate-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

const scriptPath = join(process.cwd(), 'scripts/trace/validate-kvonce.mjs');

describe('validate-kvonce CLI', () => {
  it('accepts retry contexts with sequential attempts and matching success', async () => {
    await withTempDir(async (dir) => {
      const inputPath = join(dir, 'projection.json');
      const outputPath = join(dir, 'report.json');

      const projection = {
        perKey: {
          alpha: {
            successCount: 1,
            retries: 1,
            retryContexts: [{ attempts: 1 }],
            successContexts: [{ attempts: 2 }],
            failureReasons: [],
          },
        },
      };

      await writeFile(inputPath, JSON.stringify(projection));

      await execFileAsync('node', [scriptPath, '--input', inputPath, '--output', outputPath]);

      const report = JSON.parse(await readFile(outputPath, 'utf8'));
      expect(report.valid).toBe(true);
      expect(report.issues).toEqual([]);
    });
  });

  it('flags missing retry attempts and mismatched success attempt', async () => {
    await withTempDir(async (dir) => {
      const inputPath = join(dir, 'projection.json');
      const outputPath = join(dir, 'report.json');

      const projection = {
        perKey: {
          beta: {
            successCount: 1,
            retries: 2,
            retryContexts: [{ attempts: 1 }, {}],
            successContexts: [{ attempts: 4 }],
            failureReasons: [],
          },
        },
      };

      await writeFile(inputPath, JSON.stringify(projection));

      await execFileAsync('node', [scriptPath, '--input', inputPath, '--output', outputPath]);

      const report = JSON.parse(await readFile(outputPath, 'utf8'));
      expect(report.valid).toBe(false);
      const types = report.issues.map((issue) => issue.type).sort();
      expect(types).toContain('retry-context-missing');
      expect(types).toContain('success-attempt-mismatch');
    });
  });
});
