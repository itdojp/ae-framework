import { describe, it, expect } from 'vitest';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const schemaPath = resolve('schema/spec-validation-report.schema.json');
const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));

describe('spec command report schema', () => {
  it('accepts valid report payload', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    const payload = {
      command: 'lint',
      status: 'pass',
      summary: {
        errors: 0,
        warnings: 1,
        info: 2,
      },
      issues: [
        {
          ruleId: 'BIZ_001',
          severity: 'warning',
          message: 'Domain rule is ambiguous',
          category: 'business',
        },
      ],
      input: '.ae/ae-ir.json',
      thresholds: {
        maxErrors: 0,
        maxWarnings: 10,
      },
      generatedAt: '2026-02-16T12:34:56Z',
    };

    expect(validate(payload)).toBe(true);
  });

  it('rejects payload without generatedAt', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    const payload = {
      command: 'validate',
      status: 'fail',
      summary: {
        errors: 1,
        warnings: 0,
        info: 0,
      },
      issues: [],
    };

    expect(validate(payload)).toBe(false);
  });
});
