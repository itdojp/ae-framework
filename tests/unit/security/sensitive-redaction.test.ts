import { describe, expect, it } from 'vitest';
import {
  REDACTED_VALUE,
  redactSensitiveData,
  redactSensitiveString,
  safeErrorForLogging,
  sanitizeTelemetryAttributes,
  safeUrlPath,
} from '../../../src/security/sensitive-redaction.js';

describe('sensitive redaction policy', () => {
  it('redacts sensitive keys, nested values, bearer tokens, cookies, and connection URLs', () => {
    const input = {
      password: 'raw-password-secret',
      key: 'raw-generic-key-secret',
      sshKey: 'raw-ssh-key-secret',
      headers: {
        Authorization: 'Bearer raw-bearer-secret',
        cookie: 'sid=raw-cookie-secret',
      },
      nested: {
        databaseUrl: 'postgres://app:raw-db-secret@example.test/app',
        message: 'call https://example.test/callback?token=raw-query-token&code=raw-oauth-code',
        detail: 'key=raw-inline-key-secret',
      },
      events: [
        {
          connectionString: 'redis://cache:raw-redis-secret@example.test/0',
          note: 'Cookie: session=raw-cookie-header',
        },
      ],
    };

    const redacted = redactSensitiveData(input);
    const serialized = JSON.stringify(redacted);

    expect(serialized).toContain(REDACTED_VALUE);
    expect(serialized).not.toContain('raw-password-secret');
    expect(serialized).not.toContain('raw-generic-key-secret');
    expect(serialized).not.toContain('raw-ssh-key-secret');
    expect(serialized).not.toContain('raw-bearer-secret');
    expect(serialized).not.toContain('raw-cookie-secret');
    expect(serialized).not.toContain('raw-db-secret');
    expect(serialized).not.toContain('raw-query-token');
    expect(serialized).not.toContain('raw-oauth-code');
    expect(serialized).not.toContain('raw-inline-key-secret');
    expect(serialized).not.toContain('raw-redis-secret');
    expect(serialized).not.toContain('raw-cookie-header');
  });

  it('sanitizes URL paths without retaining query parameters', () => {
    expect(safeUrlPath('/api/users?token=raw-token&password=raw-password')).toBe('/api/users');
    expect(safeUrlPath('https://example.test/api/users?token=raw-token')).toBe('/api/users');
  });

  it('redacts sensitive error messages before logging', () => {
    const logged = safeErrorForLogging(new Error('failed with token=raw-error-token and Bearer raw-bearer-token'));
    const serialized = JSON.stringify(logged);

    expect(serialized).toContain('[REDACTED]');
    expect(serialized).not.toContain('raw-error-token');
    expect(serialized).not.toContain('raw-bearer-token');
  });

  it('redacts sensitive standalone strings', () => {
    const value = redactSensitiveString('dsn=postgres://app:raw-dsn-secret@example.test/app; api_key=raw-api-key');

    expect(value).not.toContain('raw-dsn-secret');
    expect(value).not.toContain('raw-api-key');
    expect(value).toContain('[REDACTED]');
  });

  it('TGT-015-F001: sanitizes telemetry attributes through the shared redaction pipeline', () => {
    const attributes = sanitizeTelemetryAttributes({
      endpoint: '/callback?token=raw-query-token',
      authorization: 'Bearer raw-bearer-token',
      details: {
        password: 'raw-password-secret',
        nested: 'api_key=raw-api-key',
      },
      status_code: 500,
      sampled: true,
    });

    const serialized = JSON.stringify(attributes);

    expect(attributes).toMatchObject({
      authorization: REDACTED_VALUE,
      status_code: 500,
      sampled: true,
    });
    expect(serialized).toContain('[REDACTED]');
    expect(serialized).not.toContain('raw-query-token');
    expect(serialized).not.toContain('raw-bearer-token');
    expect(serialized).not.toContain('raw-password-secret');
    expect(serialized).not.toContain('raw-api-key');
  });
});
