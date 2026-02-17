import { describe, expect, it } from 'vitest';

import type { ValidationInput } from '../../../src/agents/validation-task-adapter.types';
import { extractTraceabilityMatrixRows } from '../../../src/agents/validation-task-traceability';

function createInput(content: string): ValidationInput {
  return {
    requestedSources: ['traceability.json'],
    resolvedSources: [{ path: 'traceability.json', content }],
    missingSources: [],
    strict: false,
  };
}

describe('validation-task-traceability', () => {
  it('extracts valid rows from issue-traceability-matrix/v1 payload', () => {
    const input = createInput(
      JSON.stringify({
        schemaVersion: 'issue-traceability-matrix/v1',
        rows: [
          { requirementId: 'REQ-1', tests: ['tests/req1.test.ts'], code: ['src/req1.ts'] },
          { requirementId: 'REQ-2', tests: [], code: ['src/req2.ts'] },
        ],
      }),
    );

    const rows = extractTraceabilityMatrixRows(input);

    expect(rows).toEqual([
      {
        requirementId: 'REQ-1',
        tests: ['tests/req1.test.ts'],
        code: ['src/req1.ts'],
        linked: true,
      },
      {
        requirementId: 'REQ-2',
        tests: [],
        code: ['src/req2.ts'],
        linked: false,
      },
    ]);
  });

  it('ignores malformed payloads and unsupported schema versions', () => {
    const input: ValidationInput = {
      requestedSources: ['ok.json', 'bad.json', 'legacy.json'],
      resolvedSources: [
        {
          path: 'ok.json',
          content: JSON.stringify({
            schemaVersion: 'issue-traceability-matrix/v1',
            rows: [{ requirementId: 'REQ-3', tests: ['t'], code: ['c'] }],
          }),
        },
        { path: 'bad.json', content: '{invalid-json' },
        {
          path: 'legacy.json',
          content: JSON.stringify({
            schemaVersion: 'legacy/v0',
            rows: [{ requirementId: 'REQ-4', tests: ['t'], code: ['c'] }],
          }),
        },
      ],
      missingSources: [],
      strict: false,
    };

    const rows = extractTraceabilityMatrixRows(input);

    expect(rows).toHaveLength(1);
    expect(rows[0]?.requirementId).toBe('REQ-3');
  });
});
