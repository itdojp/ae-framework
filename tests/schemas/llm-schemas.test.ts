import { describe, expect, test } from 'vitest';
import { AnthropicMsg, GeminiResp, BenchmarkResult } from '../../src/schemas/llm.js';

describe('llm schemas', () => {
  test('AnthropicMsg accepts string content and passthrough fields', () => {
    const result = AnthropicMsg.safeParse({ content: 'hello', id: 'msg_1' });
    expect(result.success).toBe(true);
    if (result.success) {
      expect(result.data.id).toBe('msg_1');
    }
  });

  test('AnthropicMsg accepts structured content arrays', () => {
    const payload = {
      content: [{ text: 'hello' }, { text: 'world' }],
      type: 'message',
    };
    const result = AnthropicMsg.safeParse(payload);
    expect(result.success).toBe(true);
  });

  test('GeminiResp accepts unknown response payloads', () => {
    const result = GeminiResp.safeParse({
      response: { text: () => 'ok' },
      meta: { provider: 'gemini' },
    });
    expect(result.success).toBe(true);
  });

  test('BenchmarkResult accepts benchmark-report/v1 payload', () => {
    const result = BenchmarkResult.safeParse({
      schemaVersion: 'benchmark-report/v1',
      summary: [{
        name: 'test',
        hz: 100,
        meanMs: 10,
        sdMs: 1,
        samples: 30,
        p95: 12,
        errorRate: 0,
        coldStartMs: 15,
      }],
      metrics: {
        p95: 12,
        errorRate: 0,
        coldStartMs: 15,
        peakRssMb: 48.2,
      },
      meta: {
        date: new Date().toISOString(),
        env: {
          node: process.version,
          platform: process.platform,
          arch: process.arch,
          cpu: 'unit-test-cpu',
          totalMem: 1024,
          seed: 12345,
        },
        config: {
          warmupMs: 300,
          iterations: 30,
          seed: 12345,
        },
      },
      extra: 'allowed',
    });
    expect(result.success).toBe(true);
  });

  test('BenchmarkResult rejects payload without required benchmark fields', () => {
    const result = BenchmarkResult.safeParse({
      summary: [{ name: 'test', hz: 100, meanMs: 10 }],
    });
    expect(result.success).toBe(false);
  });
});
