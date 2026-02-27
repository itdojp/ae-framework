import { afterEach, describe, expect, it } from 'vitest';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { parseTraceRedactionRule, runConformanceIngest } from '../../../src/cli/conformance-ingest.js';

const workdirs: string[] = [];

const createWorkdir = async (): Promise<string> => {
  const workdir = await mkdtemp(join(tmpdir(), 'ae-trace-ingest-'));
  workdirs.push(workdir);
  return workdir;
};

afterEach(async () => {
  await Promise.all(workdirs.splice(0).map((workdir) => rm(workdir, { recursive: true, force: true })));
});

describe('conformance ingest utilities', () => {
  it('parses redaction rules in <jsonPath>:<action> format', () => {
    const valid = parseTraceRedactionRule('$.details.secret:mask');
    expect(valid.ok).toBe(true);
    expect(valid.rule).toEqual({ jsonPath: '$.details.secret', action: 'mask' });

    const invalidAction = parseTraceRedactionRule('$.details.secret:drop');
    expect(invalidAction.ok).toBe(false);
    expect(invalidAction.error).toContain('invalid redaction action');

    const invalidPath = parseTraceRedactionRule('details.secret:mask');
    expect(invalidPath.ok).toBe(false);
    expect(invalidPath.error).toContain('unsupported redaction path');
  });

  it('ingests ndjson traces, drops invalid events, and applies redaction', async () => {
    const workdir = await createWorkdir();
    const inputPath = join(workdir, 'trace.ndjson');
    const outputPath = join(workdir, 'artifacts', 'observability', 'trace-bundle.json');
    const summaryOutputPath = join(workdir, 'artifacts', 'observability', 'trace-bundle-summary.json');

    await writeFile(
      inputPath,
      [
        JSON.stringify({
          traceId: 'trace-001',
          timestamp: '2026-02-27T00:00:00.000Z',
          actor: 'checkout-service',
          event: 'OrderPlaced',
          details: { secret: 'token-001' },
        }),
        JSON.stringify({
          traceId: 'trace-002',
          timestamp: '2026-02-27T00:00:01.000Z',
          actor: 'inventory-service',
          event: 'InventoryReserved',
          details: { secret: 'token-002' },
        }),
        JSON.stringify({
          traceId: '',
          timestamp: 'not-date-time',
          actor: 'invalid',
          event: 'broken',
        }),
      ].join('\n'),
      'utf-8',
    );

    const { bundle, summary } = runConformanceIngest({
      inputPath,
      outputPath,
      summaryOutputPath,
      sourceEnv: 'staging',
      sourceService: 'api-gateway',
      sampleRate: 1,
      redactRules: [{ jsonPath: '$.details.secret', action: 'mask' }],
    });

    expect(bundle.schemaVersion).toBe('ae-trace-bundle/v1');
    expect(bundle.source.environment).toBe('staging');
    expect(bundle.source.service).toBe('api-gateway');
    expect(bundle.summary.rawEventCount).toBe(3);
    expect(bundle.summary.validEventCount).toBe(2);
    expect(bundle.summary.invalidEventCount).toBe(1);
    expect(bundle.summary.emittedEventCount).toBe(2);
    expect(bundle.grouping.traceCount).toBe(2);
    expect(bundle.redaction.redactedFieldCount).toBe(2);
    expect(bundle.events.every((event) => event.details && (event.details as { secret: string }).secret === '[REDACTED]')).toBe(true);

    expect(summary.schemaVersion).toBe('ae-trace-bundle-summary/v1');
    expect(summary.counts.invalidEventCount).toBe(1);
    expect(summary.counts.redactedFieldCount).toBe(2);

    const savedBundle = JSON.parse(await readFile(outputPath, 'utf-8')) as { schemaVersion: string };
    const savedSummary = JSON.parse(await readFile(summaryOutputPath, 'utf-8')) as { schemaVersion: string };
    expect(savedBundle.schemaVersion).toBe('ae-trace-bundle/v1');
    expect(savedSummary.schemaVersion).toBe('ae-trace-bundle-summary/v1');
  });

  it('supports deterministic sampling and max-events cap', async () => {
    const workdir = await createWorkdir();
    const inputPath = join(workdir, 'trace.json');
    const outputPath = join(workdir, 'trace-bundle.json');
    const summaryOutputPath = join(workdir, 'trace-bundle-summary.json');

    await writeFile(
      inputPath,
      `${JSON.stringify({
        events: [
          { traceId: 'a', timestamp: '2026-02-27T00:00:00.000Z', actor: 'svc', event: 'E1' },
          { traceId: 'a', timestamp: '2026-02-27T00:00:01.000Z', actor: 'svc', event: 'E2' },
          { traceId: 'b', timestamp: '2026-02-27T00:00:02.000Z', actor: 'svc', event: 'E3' },
        ],
      }, null, 2)}\n`,
      'utf-8',
    );

    const sampledOut = runConformanceIngest({
      inputPath,
      outputPath,
      summaryOutputPath,
      sampleRate: 0,
    });
    expect(sampledOut.bundle.summary.emittedEventCount).toBe(0);
    expect(sampledOut.bundle.summary.sampledOutCount).toBe(3);

    const capped = runConformanceIngest({
      inputPath,
      outputPath,
      summaryOutputPath,
      sampleRate: 1,
      maxEvents: 1,
    });
    expect(capped.bundle.summary.emittedEventCount).toBe(1);
    expect(capped.summary.sampling.maxEvents).toBe(1);
  });
});
