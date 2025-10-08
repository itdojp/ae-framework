import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import os from 'node:os';

const scriptPath = join(process.cwd(), 'scripts/trace/generate-grafana-variables.mjs');

describe('generate-grafana-variables CLI', () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = mkdtempSync(join(os.tmpdir(), 'grafana-vars-'));
  });

  afterEach(() => {
    rmSync(tempDir, { recursive: true, force: true });
  });

  it('collects trace ids and tempo links from envelope, summary, and step summary', () => {
    const envelopePath = join(tempDir, 'envelope.json');
    const summaryPath = join(tempDir, 'trace-summary.json');
    const stepSummaryPath = join(tempDir, 'step-summary.md');
    const outputPath = join(tempDir, 'variables.json');

    writeFileSync(envelopePath, JSON.stringify({
      correlation: {
        runId: '123',
        branch: 'feature/example',
      },
      summary: {
        trace: {
          traceIds: ['trace-a'],
        },
      },
      tempoLinks: ['https://tempo.example.com/explore?traceId=trace-a'],
    }, null, 2));

    writeFileSync(summaryPath, JSON.stringify({
      cases: [
        {
          format: 'current',
          label: 'Current',
          traceIds: ['trace-b'],
          tempoLinks: ['https://tempo.example.com/explore?traceId=trace-b'],
        },
      ],
    }, null, 2));

    writeFileSync(stepSummaryPath, [
      '## Verify Conformance',
      '- trace ids: trace-c, trace-d',
      'Tempo: https://tempo.example.com/explore?traceId=trace-c',
      '- https://tempo.example.com/explore?traceId=trace-d',
    ].join('\n'));

    const result = spawnSync(process.execPath, [
      scriptPath,
      '--envelope', envelopePath,
      '--trace-summary', summaryPath,
      '--step-summary', stepSummaryPath,
      '--output', outputPath,
    ], { encoding: 'utf8' });

    expect(result.status).toBe(0);
    const output = JSON.parse(readFileSync(outputPath, 'utf8'));

    expect(output.trace.traceIds).toEqual([
      'trace-a',
      'trace-b',
      'trace-c',
      'trace-d',
    ]);
    expect(output.trace.tempoLinks).toEqual([
      'https://tempo.example.com/explore?traceId=trace-a',
      'https://tempo.example.com/explore?traceId=trace-b',
      'https://tempo.example.com/explore?traceId=trace-c',
      'https://tempo.example.com/explore?traceId=trace-d',
    ]);
    expect(output.variables.traceIds).toHaveLength(4);
    expect(output.variables.tempoLinks).toHaveLength(4);
    expect(output.variables.cases).toEqual([{ value: 'current', text: 'Current' }]);
    expect(output.metadata.runId).toBe('123');
    expect(output.metadata.branch).toBe('feature/example');
  });

  it('derives tempo links from template when missing', () => {
    const envelopePath = join(tempDir, 'envelope.json');
    const outputPath = join(tempDir, 'variables.json');

    writeFileSync(envelopePath, JSON.stringify({
      summary: {
        trace: {
          traceIds: ['trace-x'],
        },
      },
    }, null, 2));

    const result = spawnSync(process.execPath, [
      scriptPath,
      '--envelope', envelopePath,
      '--output', outputPath,
    ], {
      encoding: 'utf8',
      env: {
        ...process.env,
        REPORT_ENVELOPE_TEMPO_LINK_TEMPLATE: 'https://tempo.example.com/explore?traceId={traceId}',
      },
    });

    expect(result.status).toBe(0);
    const output = JSON.parse(readFileSync(outputPath, 'utf8'));

    expect(output.trace.traceIds).toEqual(['trace-x']);
    expect(output.trace.tempoLinks).toEqual(['https://tempo.example.com/explore?traceId=trace-x']);
  });
});
