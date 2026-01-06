import { describe, expect, test } from 'vitest';
import { normalizeError } from '../../src/resilience/error-utils.js';

describe('normalizeError', () => {
  test('returns Error instances unchanged', () => {
    const error = new Error('boom');
    expect(normalizeError(error, 'fallback')).toBe(error);
  });

  test('wraps string errors', () => {
    const normalized = normalizeError('oops', 'fallback');
    expect(normalized).toBeInstanceOf(Error);
    expect(normalized.message).toBe('oops');
  });

  test('preserves message, name, and metadata from objects', () => {
    const normalized = normalizeError(
      { message: 'nope', name: 'RetryableError', status: 503, code: 'E_TEST' },
      'fallback'
    );
    expect(normalized.message).toBe('nope');
    expect(normalized.name).toBe('RetryableError');
    expect((normalized as { status?: number }).status).toBe(503);
    expect((normalized as { code?: string }).code).toBe('E_TEST');
  });

  test('falls back to JSON string when message is missing', () => {
    const normalized = normalizeError({ detail: 'missing' }, 'fallback');
    expect(normalized.message).toContain('"detail":"missing"');
  });

  test('uses fallback when JSON serialization fails', () => {
    const circular: { self?: unknown } = {};
    circular.self = circular;
    const normalized = normalizeError(circular, 'fallback');
    expect(normalized.message).toBe('fallback');
  });
});
