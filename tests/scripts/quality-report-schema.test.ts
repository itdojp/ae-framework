import { describe, it, expect } from 'vitest';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const schemaPath = resolve('schema/quality-report.schema.json');
const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));

describe('quality report schema', () => {
  it('accepts valid payload', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    const payload = {
      timestamp: '2026-02-19T00:00:00.000Z',
      environment: 'development',
      meta: {
        runId: 'local-123',
        createdAt: '2026-02-19T00:00:00.000Z',
      },
      overallScore: 95,
      totalGates: 2,
      passedGates: 2,
      failedGates: 0,
      results: [
        {
          gateKey: 'linting',
          gateName: 'Code Linting',
          passed: true,
          score: 95,
          violations: [],
          executionTime: 10,
          environment: 'development',
          threshold: {
            maxErrors: 0,
            maxWarnings: 0,
            blockOnErrors: true,
          },
          details: {
            dryRun: true,
          },
        },
      ],
      summary: {
        byCategory: {
          'code-quality': {
            passed: 2,
            total: 2,
          },
        },
        executionTime: 10,
        blockers: [],
      },
    };

    expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects missing summary', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    const payload = {
      timestamp: '2026-02-19T00:00:00.000Z',
      environment: 'development',
      overallScore: 95,
      totalGates: 1,
      passedGates: 1,
      failedGates: 0,
      results: [],
    };

    expect(validate(payload)).toBe(false);
  });
});
