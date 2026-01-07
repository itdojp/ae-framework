import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync, readFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import os from 'node:os';

const scriptPath = join(process.cwd(), 'scripts/trace/post-envelope-comment.mjs');

describe('post-envelope-comment CLI', () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = mkdtempSync(join(os.tmpdir(), 'envelope-comment-'));
  });

  afterEach(() => {
    rmSync(tempDir, { recursive: true, force: true });
  });

  it('prints comment in dry-run mode', () => {
    const envelopePath = join(tempDir, 'envelope.json');
    writeFileSync(envelopePath, JSON.stringify({
      source: 'verify-lite',
      correlation: {
        runId: '123',
        branch: 'feature/x',
        workflow: 'CI',
        traceIds: ['trace-a'],
      },
      summary: {
        status: 'valid',
        trace: {
          status: 'valid',
          traceIds: ['trace-b'],
          domains: [
            {
              key: 'inventory',
              label: 'Inventory',
              status: 'valid',
              issues: 0,
              traceIds: ['trace-b'],
              tempoLinks: ['https://tempo.example.com/explore?traceId=trace-b'],
            },
          ],
        },
        cases: [
          { format: 'current', label: 'Current', valid: true, traceIds: ['trace-b'] },
        ],
        tempoLinks: ['https://tempo.example.com/explore?traceId=trace-a'],
      },
      artifacts: [
        { description: 'Validation', path: 'hermetic-reports/trace/kvonce-validation.json' },
      ],
    }, null, 2));

    const result = spawnSync(process.execPath, [
      scriptPath,
      '--envelope', envelopePath,
      '--dry-run',
    ], { encoding: 'utf8' });

    expect(result.status).toBe(0);
    expect(result.stdout).toContain('## Trace Envelope Summary');
    expect(result.stdout).toContain('Tempo Links');
    expect(result.stdout).toContain('Trace IDs');
    expect(result.stdout).toContain('Trace Cases');
    expect(result.stdout).toContain('Trace Domains');
  });

  it('writes output file when --output is specified', () => {
    const envelopePath = join(tempDir, 'envelope.json');
    const outputPath = join(tempDir, 'comment.md');
    writeFileSync(envelopePath, JSON.stringify({ summary: {} }));

    const result = spawnSync(process.execPath, [
      scriptPath,
      '--envelope', envelopePath,
      '--dry-run',
      '--output', outputPath,
    ], { encoding: 'utf8' });

    expect(result.status).toBe(0);
    expect(existsSync(outputPath)).toBe(true);
    expect(readFileSync(outputPath, 'utf8')).toContain('Trace Envelope Summary');
  });

  it('fails when envelope is missing', () => {
    const missingPath = join(tempDir, 'missing-envelope.json');

    const result = spawnSync(process.execPath, [
      scriptPath,
      '--envelope', missingPath,
      '--dry-run',
    ], { encoding: 'utf8' });

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('envelope not found');
  });
});
