import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync, readFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import os from 'node:os';

const scriptPath = join(process.cwd(), 'scripts/trace/publish-envelope.mjs');

describe('publish-envelope CLI', () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = mkdtempSync(join(os.tmpdir(), 'publish-envelope-'));
  });

  afterEach(() => {
    rmSync(tempDir, { recursive: true, force: true });
  });

  it('outputs metadata in dry-run mode without calling AWS', () => {
    const envelopePath = join(tempDir, 'envelope.json');
    const outputPath = join(tempDir, 'publish.json');

    writeFileSync(envelopePath, JSON.stringify({
      correlation: {
        workflow: 'trace-ci',
        branch: 'feature/sample',
        runId: '123',
      },
      tempoLinks: ['https://tempo.example.com/explore?traceId=abc'],
    }, null, 2));

    const result = spawnSync(process.execPath, [
      scriptPath,
      '--envelope', envelopePath,
      '--bucket', 'example-bucket',
      '--key', 'envelopes/sample/envelope.json',
      '--output', outputPath,
      '--slack-webhook', 'https://example.com/webhook',
      '--dry-run',
    ], { encoding: 'utf8' });

    expect(result.status).toBe(0);
    expect(existsSync(outputPath)).toBe(true);
    const metadata = JSON.parse(readFileSync(outputPath, 'utf8'));
    expect(metadata.dryRun).toBe(true);
    expect(metadata.presignedUrl).toBeNull();
    expect(metadata.bucket).toBe('example-bucket');
    expect(metadata.key).toBe('envelopes/sample/envelope.json');
    expect(metadata.notified).toBe(false);
  });
});
