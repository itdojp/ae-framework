import { describe, it, expect } from 'vitest';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const schemaPath = resolve('schema/usefulness-evaluation-report.schema.json');
const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));

describe('usefulness evaluation report schema', () => {
  it('accepts valid payload', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    const payload = {
      schemaVersion: 'usefulness-evaluation/v1',
      generatedAt: '2026-02-17T00:00:00Z',
      inputs: [
        {
          key: 'runIndex',
          path: 'artifacts/runs/index.json',
          provided: false,
          exists: true,
          validJson: true,
          error: null,
        },
      ],
      axes: {
        reproducibility: { available: true, score: 80, reason: null, details: { totalRuns: 10 } },
        traceability: { available: true, score: 75, reason: null, details: { total: 20 } },
        automation: { available: true, score: 90, reason: null, details: { totalSteps: 4 } },
        qualityDetection: { available: true, score: 85, reason: null, details: { components: 3 } },
      },
      overall: {
        score: 83,
        bucket: 'good',
        availableAxes: 4,
        missingAxes: [],
      },
      recommendations: ['Maintain current verification cadence and continue recording artifacts.'],
    };

    expect(validate(payload)).toBe(true);
  });

  it('rejects missing required fields', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate({ schemaVersion: 'usefulness-evaluation/v1' })).toBe(false);
  });
});
