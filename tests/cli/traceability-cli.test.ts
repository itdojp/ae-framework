import { describe, it, expect, beforeAll } from 'vitest';

let parseIssueReference: (issueValue: string, repoValue?: string, envRepo?: string) => {
  repository: string;
  issueNumber: number;
  issueUrl: string;
};
let extractRequirementIds: (text: string, patternSource: string) => string[];
let buildTraceabilityMatrix: (
  requirementIds: string[],
  testFiles: Array<{ path: string; content: string }>,
  codeFiles: Array<{ path: string; content: string }>,
  cwd: string,
) => {
  summary: {
    totalRequirements: number;
    linkedRequirements: number;
    unlinkedRequirements: number;
    coverage: number;
    contextPackDiagramIds: number;
    contextPackMorphismIds: number;
    contextPackAcceptanceTestIds: number;
    missingDiagramLinks: number;
    missingMorphismLinks: number;
    missingAcceptanceTestLinks: number;
    rowsMissingContextPackLinks: number;
  };
  rows: Array<{
    requirementId: string;
    linked: boolean;
    tests: string[];
    code: string[];
    diagramId: string[];
    morphismId: string[];
    acceptanceTestId: string[];
  }>;
};

beforeAll(async () => {
  ({
    parseIssueReference,
    extractRequirementIds,
    buildTraceabilityMatrix,
  } = await import('../../src/cli/traceability-cli.js'));
});

describe('traceability cli helpers', () => {
  it('parses GitHub issue URL', () => {
    const parsed = parseIssueReference('https://github.com/itdojp/ae-framework/issues/2013');
    expect(parsed.repository).toBe('itdojp/ae-framework');
    expect(parsed.issueNumber).toBe(2013);
    expect(parsed.issueUrl).toBe('https://github.com/itdojp/ae-framework/issues/2013');
  });

  it('parses issue number with explicit repository', () => {
    const parsed = parseIssueReference('12', 'itdojp/ae-framework');
    expect(parsed.repository).toBe('itdojp/ae-framework');
    expect(parsed.issueNumber).toBe(12);
  });

  it('extracts unique requirement IDs in order', () => {
    const ids = extractRequirementIds(
      'LG-LOGIN-01\nREQ-AUTH-02\nLG-LOGIN-01',
      '(?:LG|REQ)-[A-Z0-9-]+',
    );
    expect(ids).toEqual(['LG-LOGIN-01', 'REQ-AUTH-02']);
  });

  it('builds matrix coverage from mapped files', () => {
    const matrix = buildTraceabilityMatrix(
      ['LG-1', 'LG-2'],
      [
        { path: '/repo/tests/auth.test.ts', content: 'LG-1' },
        { path: '/repo/tests/order.test.ts', content: 'LG-2' },
      ],
      [
        { path: '/repo/src/auth.ts', content: 'LG-1' },
      ],
      '/repo',
    );

    expect(matrix.summary.totalRequirements).toBe(2);
    expect(matrix.summary.linkedRequirements).toBe(1);
    expect(matrix.summary.unlinkedRequirements).toBe(1);
    expect(matrix.summary.coverage).toBe(50);
    expect(matrix.rows.find((row) => row.requirementId === 'LG-1')?.linked).toBe(true);
    expect(matrix.rows.find((row) => row.requirementId === 'LG-2')?.linked).toBe(false);
  });

  it('does not match requirement IDs as substrings of other IDs', () => {
    const matrix = buildTraceabilityMatrix(
      ['LG-1'],
      [
        { path: '/repo/tests/auth.test.ts', content: 'LG-10' },
      ],
      [
        { path: '/repo/src/auth.ts', content: 'LG-10' },
      ],
      '/repo',
    );

    expect(matrix.summary.linkedRequirements).toBe(0);
    expect(matrix.rows[0]?.tests).toEqual([]);
    expect(matrix.rows[0]?.code).toEqual([]);
    expect(matrix.rows[0]?.linked).toBe(false);
  });

  it('maps context-pack IDs when they are present in linked files', () => {
    const matrix = buildTraceabilityMatrix(
      ['LG-1'],
      [
        { path: '/repo/tests/auth.test.ts', content: 'LG-1 DGM-AUTH MOR-AUTH AT-AUTH' },
      ],
      [
        { path: '/repo/src/auth.ts', content: 'LG-1 MOR-AUTH' },
      ],
      '/repo',
      {
        diagramIds: ['DGM-AUTH'],
        morphismIds: ['MOR-AUTH'],
        acceptanceTestIds: ['AT-AUTH'],
      },
    );

    expect(matrix.rows[0]?.diagramId).toEqual(['DGM-AUTH']);
    expect(matrix.rows[0]?.morphismId).toEqual(['MOR-AUTH']);
    expect(matrix.rows[0]?.acceptanceTestId).toEqual(['AT-AUTH']);
    expect(matrix.summary.rowsMissingContextPackLinks).toBe(0);
  });

  it('counts missing context-pack links per requirement row', () => {
    const matrix = buildTraceabilityMatrix(
      ['LG-1', 'LG-2'],
      [
        { path: '/repo/tests/a.test.ts', content: 'LG-1 DGM-A MOR-A AT-A' },
        { path: '/repo/tests/b.test.ts', content: 'LG-2' },
      ],
      [
        { path: '/repo/src/a.ts', content: 'LG-1 DGM-A MOR-A AT-A' },
        { path: '/repo/src/b.ts', content: 'LG-2' },
      ],
      '/repo',
      {
        diagramIds: ['DGM-A'],
        morphismIds: ['MOR-A'],
        acceptanceTestIds: ['AT-A'],
      },
    );

    expect(matrix.summary.missingDiagramLinks).toBe(1);
    expect(matrix.summary.missingMorphismLinks).toBe(1);
    expect(matrix.summary.missingAcceptanceTestLinks).toBe(1);
    expect(matrix.summary.rowsMissingContextPackLinks).toBe(1);
  });
});
