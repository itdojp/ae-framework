import { describe, it, expect } from 'vitest';
import { mkdtemp, rm, writeFile, readFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);

async function withTempDir<T>(fn: (dir: string) => Promise<T>) {
  const dir = await mkdtemp(join(tmpdir(), 'verify-conformance-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

describe('verify-conformance --from-envelope', () => {
  it('replays summary data from an existing envelope', async () => {
    await withTempDir(async (dir) => {
      const nodePath = process.execPath;
      const scriptPath = resolve('scripts/formal/verify-conformance.mjs');
      const schemaPath = resolve('observability/trace-schema.yaml');
      const eventsPath = join(dir, 'events.json');
      const tracePath = join(dir, 'trace.ndjson');
      const summaryPath = join(dir, 'summary.json');
      const traceOutputDir = join(dir, 'trace-output');

      const events = [
        {
          traceId: 'trace-1',
          timestamp: '2025-10-08T10:40:00.000Z',
          actor: 'checkout-service',
          event: 'OrderPlaced',
          state: { onHand: 10, allocated: 2 },
        },
      ];
      await writeFile(eventsPath, JSON.stringify(events), 'utf8');
      await writeFile(tracePath, events.map((item) => JSON.stringify(item)).join('\n'), 'utf8');

      await execFileAsync(
        nodePath,
        [
          scriptPath,
          '--in',
          eventsPath,
          '--schema',
          schemaPath,
          '--out',
          summaryPath,
          '--trace',
          tracePath,
          '--trace-format',
          'ndjson',
          '--trace-output',
          traceOutputDir,
          '--trace-skip-replay',
        ],
        {
          env: {
            ...process.env,
            REPORT_ENVELOPE_TEMPO_LINK_TEMPLATE: 'https://tempo.example.com/explore?traceId={traceId}',
          },
        },
      );

      const summary = JSON.parse(await readFile(summaryPath, 'utf8'));
      expect(summary.events).toBe(1);
      expect(summary.trace?.status).toBeDefined();
      expect(summary.trace?.traceIds ?? summary.traceIds).toEqual(['trace-1']);
      expect(summary.trace?.tempoLinks ?? summary.tempoLinks).toEqual(['https://tempo.example.com/explore?traceId=trace-1']);
      expect(summary.trace?.domains?.[0]?.key).toBe('kvonce');
      expect(summary.trace?.domains?.[0]?.traceIds).toEqual(['trace-1']);

      const envelopePath = join(dir, 'envelope.json');
      const envelope = {
        schemaVersion: '1.0.0',
        source: 'unit-test',
        generatedAt: new Date().toISOString(),
        summary,
        artifacts: [],
      };
      await writeFile(envelopePath, JSON.stringify(envelope, null, 2), 'utf8');

      const replaySummaryPath = join(dir, 'summary-from-envelope.json');
      await execFileAsync(
        nodePath,
        [
          scriptPath,
          '--from-envelope',
          envelopePath,
          '--out',
          replaySummaryPath,
        ],
        {
          env: {
            ...process.env,
            REPORT_ENVELOPE_TEMPO_LINK_TEMPLATE: 'https://tempo.example.com/explore?traceId={traceId}',
          },
        },
      );

      const replaySummary = JSON.parse(await readFile(replaySummaryPath, 'utf8'));
      expect(replaySummary.events).toBe(summary.events);
      expect(replaySummary.schemaErrors).toBe(summary.schemaErrors);
      expect(replaySummary.envelopePath).toBeDefined();
      expect(replaySummary.trace?.status).toBe(summary.trace?.status);
      expect(replaySummary.trace?.traceIds ?? replaySummary.traceIds).toEqual(['trace-1']);
      expect(replaySummary.trace?.tempoLinks ?? replaySummary.tempoLinks).toEqual(['https://tempo.example.com/explore?traceId=trace-1']);
      expect(replaySummary.trace?.domains?.[0]?.key).toBe('kvonce');
      expect(replaySummary.trace?.domains?.[0]?.traceIds).toEqual(['trace-1']);
    });
  });
});
