import { describe, it, expect } from 'vitest';
import { mkdtemp, writeFile, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { promisify } from 'node:util';
import { execFile } from 'node:child_process';

const execFileAsync = promisify(execFile);
const scriptPath = resolve(__dirname, '../../../scripts/trace/convert-otlp-kvonce.mjs');

async function withTempDir<T>(fn: (dir: string) => Promise<T>) {
  const dir = await mkdtemp(join(tmpdir(), 'kvonce-convert-'));
  try {
    return await fn(dir);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

describe('convert-otlp-kvonce CLI', () => {
  it('converts OTLP spans to NDJSON with nested context preserved', async () => {
    await withTempDir(async (dir) => {
      const inputPath = join(dir, 'input.json');
      const outputPath = join(dir, 'out.ndjson');

      const payload = {
        resourceSpans: [
          {
            scopeSpans: [
              {
                spans: [
                  {
                    startTimeUnixNano: '1728000000000000000',
                    attributes: [
                      { key: 'kvonce.event.type', value: { stringValue: 'success' } },
                      { key: 'kvonce.event.key', value: { stringValue: 'alpha' } },
                      { key: 'kvonce.event.value', value: { stringValue: 'v1' } },
                      {
                        key: 'kvonce.event.context',
                        value: {
                          mapValue: {
                            fields: [
                              {
                                key: 'attempts',
                                value: { intValue: '2' }
                              },
                              {
                                key: 'metadata',
                                value: {
                                  mapValue: {
                                    fields: [
                                      { key: 'region', value: { stringValue: 'tokyo' } },
                                      {
                                        key: 'flags',
                                        value: {
                                          arrayValue: {
                                            values: [
                                              { stringValue: 'beta' },
                                              { boolValue: true }
                                            ]
                                          }
                                        }
                                      }
                                    ]
                                  }
                                }
                              }
                            ]
                          }
                        }
                      }
                    ]
                  },
                  {
                    startTimeUnixNano: '1728000005000000000',
                    attributes: [
                      { key: 'kvonce.event.type', value: { stringValue: 'failure' } },
                      { key: 'kvonce.event.key', value: { stringValue: 'beta' } },
                      { key: 'kvonce.event.reason', value: { stringValue: 'duplicate' } },
                      { key: 'kvonce.event.context', value: { stringValue: 'short' } }
                    ]
                  }
                ]
              }
            ]
          }
        ]
      };

      await writeFile(inputPath, JSON.stringify(payload));

      await execFileAsync('node', [scriptPath, '--input', inputPath, '--output', outputPath]);

      const raw = await readFile(outputPath, 'utf8');
      const events = raw
        .trim()
        .split('\n')
        .map((line) => JSON.parse(line));

      expect(events).toHaveLength(2);
      expect(events[0]).toMatchObject({
        type: 'success',
        key: 'alpha',
        value: 'v1',
        context: {
          attempts: 2,
          metadata: {
            region: 'tokyo',
            flags: ['beta', true]
          }
        }
      });
      expect(events[1]).toMatchObject({
        type: 'failure',
        key: 'beta',
        reason: 'duplicate',
        context: 'short'
      });
    });
  });

  it('produces empty output when spans lack kvonce keys', async () => {
    await withTempDir(async (dir) => {
      const inputPath = join(dir, 'input.json');

      const payload = {
        resourceSpans: [
          {
            scopeSpans: [
              {
                spans: [
                  {
                    startTimeUnixNano: '0',
                    attributes: [
                      { key: 'other.attribute', value: { stringValue: 'value' } }
                    ]
                  }
                ]
              }
            ]
          }
        ]
      };

      await writeFile(inputPath, JSON.stringify(payload));

      const result = await execFileAsync('node', [scriptPath, '--input', inputPath]).catch((error) => {
        return { stdout: error.stdout, stderr: error.stderr, exitCode: error.code };
      });

      expect(result.exitCode).toBe(2);
      expect(result.stderr).toContain('No kvonce events found in OTLP payload');
      expect(result.stdout ?? '').toBe('');
    });
  });
});
