import { describe, it, expect } from 'vitest';
import Ajv from 'ajv';
import addFormats from 'ajv-formats';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const schemaPath = resolve('schema/verify-profile-summary.schema.json');
const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));

describe('verify profile summary schema', () => {
  it('accepts valid payload', () => {
    const ajv = new Ajv({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    const payload = {
      schemaVersion: 'verify-profile-summary/v1',
      profile: 'fast',
      started_at: '2026-02-16T12:00:00Z',
      finished_at: '2026-02-16T12:00:05Z',
      overall_status: 'pass',
      required_fail_count: 0,
      optional_fail_count: 1,
      steps: [
        {
          name: 'build',
          required: true,
          command: 'pnpm run build',
          status: 'passed',
          exit_code: 0,
          duration_ms: 1000,
        },
        {
          name: 'codex:quickstart',
          required: false,
          command: 'pnpm run codex:quickstart',
          status: 'failed',
          exit_code: 1,
          duration_ms: 700,
          error: 'failed',
        },
      ],
    };

    expect(validate(payload)).toBe(true);
  });

  it('rejects missing required fields', () => {
    const ajv = new Ajv({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate({ profile: 'fast' })).toBe(false);
  });
});
