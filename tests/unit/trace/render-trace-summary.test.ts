import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, mkdirSync, writeFileSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import os from 'node:os';

const scriptPath = join(process.cwd(), 'scripts/trace/render-trace-summary.mjs');

describe('render-trace-summary CLI', () => {
  let tempDir: string;
  let reportDir: string;
  let summaryPath: string;
  let outputPath: string;

  beforeEach(() => {
    tempDir = mkdtempSync(join(os.tmpdir(), 'trace-summary-'));
    reportDir = join(tempDir, 'hermetic-reports', 'trace');
    mkdirSync(reportDir, { recursive: true });
    summaryPath = join(tempDir, 'summary.md');
    outputPath = join(tempDir, 'outputs.txt');
  });

  afterEach(() => {
    rmSync(tempDir, { recursive: true, force: true });
  });

  function runScript() {
    return spawnSync(process.execPath, [scriptPath], {
      cwd: tempDir,
      encoding: 'utf8',
      env: {
        ...process.env,
        GITHUB_STEP_SUMMARY: summaryPath,
        GITHUB_OUTPUT: outputPath,
      },
    });
  }

  it('records metadata read errors with details', () => {
    const metadataPath = join(reportDir, 'kvonce-payload-metadata.json');
    mkdirSync(metadataPath, { recursive: true });

    const result = runScript();

    expect(result.status).toBe(0);
    const summary = readFileSync(summaryPath, 'utf8');
    expect(summary).toContain('payload metadata: ⚠️ failed to read');
  });

  it('reports validation parse failures and exits non-zero', () => {
    const otlpDir = join(reportDir, 'otlp');
    mkdirSync(otlpDir, { recursive: true });
    writeFileSync(join(otlpDir, 'kvonce-validation.json'), '{invalid json');

    const result = runScript();

    expect(result.status).toBe(1);
    const summary = readFileSync(summaryPath, 'utf8');
    expect(summary).toContain('failed to parse validation');
    const outputs = readFileSync(outputPath, 'utf8');
    expect(outputs).toContain('valid_otlp=error');
  });

  it('reports validation read failures and exits non-zero', () => {
    const otlpDir = join(reportDir, 'otlp');
    mkdirSync(otlpDir, { recursive: true });
    mkdirSync(join(otlpDir, 'kvonce-validation.json'), { recursive: true });

    const result = runScript();

    expect(result.status).toBe(1);
    const summary = readFileSync(summaryPath, 'utf8');
    expect(summary).toContain('failed to read validation');
    const outputs = readFileSync(outputPath, 'utf8');
    expect(outputs).toContain('valid_otlp=error');
  });
});
