import { describe, it, expect } from 'vitest';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const mapSchema = JSON.parse(readFileSync(resolve('schema/issue-traceability-map.schema.json'), 'utf8'));
const matrixSchema = JSON.parse(readFileSync(resolve('schema/issue-traceability-matrix.schema.json'), 'utf8'));

describe('issue traceability schemas', () => {
  it('accepts valid map payload', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(mapSchema);

    const payload = {
      schemaVersion: 'issue-traceability-map/v1',
      generatedAt: '2026-02-17T00:00:00Z',
      source: {
        type: 'github-issue',
        repository: 'itdojp/ae-framework',
        issueNumber: 1,
        issueUrl: 'https://github.com/itdojp/ae-framework/issues/1',
        title: 'sample',
      },
      pattern: '(?:LG|REQ)-[A-Z0-9_-]+',
      requirementIds: ['LG-1', 'REQ-2'],
      mappings: [
        { id: 'LG-1', tests: ['tests/a.test.ts'], code: ['src/a.ts'], notes: null },
      ],
    };

    expect(validate(payload)).toBe(true);
  });

  it('accepts valid matrix payload', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(matrixSchema);

    const payload = {
      schemaVersion: 'issue-traceability-matrix/v1',
      generatedAt: '2026-02-17T00:00:00Z',
      sourceMap: 'docs/specs/issue-traceability-map.json',
      summary: {
        totalRequirements: 2,
        linkedRequirements: 1,
        unlinkedRequirements: 1,
        coverage: 50,
        contextPackDiagramIds: 1,
        contextPackMorphismIds: 1,
        contextPackAcceptanceTestIds: 1,
        missingDiagramLinks: 1,
        missingMorphismLinks: 1,
        missingAcceptanceTestLinks: 1,
        rowsMissingContextPackLinks: 1,
      },
      rows: [
        {
          requirementId: 'LG-1',
          tests: ['tests/a.test.ts'],
          code: ['src/a.ts'],
          diagramId: ['DGM-1'],
          morphismId: ['MOR-1'],
          acceptanceTestId: ['AT-1'],
          linked: true,
        },
      ],
    };

    expect(validate(payload)).toBe(true);
  });
});
