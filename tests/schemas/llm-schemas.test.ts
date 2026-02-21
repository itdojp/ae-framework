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

  test('BenchmarkResult accepts optional unknown env/config objects', () => {
    const result = BenchmarkResult.safeParse({
      summary: [{ name: 'test', hz: 100, meanMs: 10 }],
      env: { ci: true, platform: 'linux' },
      config: { mode: 'fast' },
      extra: 'allowed',
    });
    expect(result.success).toBe(true);
  });
});
