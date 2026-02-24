import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

const repoRoot = resolve('.');
const tsxBin = resolve('node_modules/.bin/tsx');
const cliEntry = resolve('src/cli/index.ts');

const runCli = (args: string[], cwd: string = repoRoot) => {
  const env = {
    ...process.env,
    VITEST: '',
    NODE_ENV: 'production',
    AE_TEST_NO_EXIT: '0',
  };
  return spawnSync(tsxBin, [cliEntry, ...args], {
    encoding: 'utf8',
    timeout: 60_000,
    env,
    cwd,
  });
};

describe('traceability command e2e', () => {
  it('generates matrix json from map', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-traceability-matrix-'));
    try {
      mkdirSync(join(dir, 'src'), { recursive: true });
      mkdirSync(join(dir, 'tests'), { recursive: true });
      mkdirSync(join(dir, 'spec', 'context-pack'), { recursive: true });
      writeFileSync(
        join(dir, 'map.json'),
        JSON.stringify(
          {
            schemaVersion: 'issue-traceability-map/v1',
            generatedAt: '2026-02-17T00:00:00Z',
            source: {
              type: 'github-issue',
              repository: 'itdojp/ae-framework',
              issueNumber: 1,
              issueUrl: 'https://github.com/itdojp/ae-framework/issues/1',
              title: 'sample',
            },
            pattern: 'LG-[A-Z0-9-]+',
            requirementIds: ['LG-1', 'LG-2'],
            mappings: [],
          },
          null,
          2,
        ),
        'utf8',
      );
      writeFileSync(
        join(dir, 'spec', 'context-pack', 'minimal.yaml'),
        [
          'version: 1',
          'name: sample',
          'problem_statement:',
          '  goals: ["g"]',
          '  non_goals: ["ng"]',
          'domain_glossary:',
          '  terms: [{ term: "Order", ja: "受注" }]',
          'objects: [{ id: "Order", kind: "entity" }]',
          'morphisms: [{ id: "MOR-AUTH", input: {}, output: {}, pre: [], post: [], failures: [] }]',
          'diagrams: [{ id: "DGM-AUTH", statement: "commutative", verification: [] }]',
          'constraints: {}',
          'acceptance_tests: [{ id: "AT-AUTH", scenario: "s", expected: ["ok"] }]',
          'coding_conventions:',
          '  language: ts',
          '  directory: ["src"]',
          '  dependencies: {}',
          'forbidden_changes: []',
          '',
        ].join('\n'),
        'utf8',
      );
      writeFileSync(join(dir, 'tests', 'auth.test.ts'), '// LG-1 DGM-AUTH MOR-AUTH AT-AUTH\n', 'utf8');
      writeFileSync(join(dir, 'src', 'auth.ts'), '// LG-1 MOR-AUTH\n', 'utf8');

      const result = runCli(
        [
          'traceability',
          'matrix',
          '--map',
          'map.json',
          '--tests',
          'tests/**/*.ts',
          '--code',
          'src/**/*.ts',
          '--format',
          'json',
          '--output',
          'matrix.json',
        ],
        dir,
      );

      expect(result.status).toBe(0);
      const matrix = JSON.parse(readFileSync(join(dir, 'matrix.json'), 'utf8'));
      expect(matrix.schemaVersion).toBe('issue-traceability-matrix/v1');
      expect(matrix.summary.totalRequirements).toBe(2);
      expect(matrix.summary.linkedRequirements).toBe(1);
      expect(matrix.summary.coverage).toBe(50);
      expect(matrix.summary.contextPackDiagramIds).toBe(1);
      expect(matrix.summary.rowsMissingContextPackLinks).toBe(1);
      expect(matrix.rows[0]?.diagramId).toEqual(['DGM-AUTH']);
      expect(matrix.rows[0]?.morphismId).toEqual(['MOR-AUTH']);
      expect(matrix.rows[0]?.acceptanceTestId).toEqual(['AT-AUTH']);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('fails validate --traceability --strict when matrix has unlinked requirements', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-traceability-strict-fail-'));
    try {
      const matrixPath = join(dir, 'matrix.json');
      writeFileSync(
        matrixPath,
        JSON.stringify(
          {
            schemaVersion: 'issue-traceability-matrix/v1',
            generatedAt: '2026-02-17T00:00:00Z',
            sourceMap: 'map.json',
            summary: {
              totalRequirements: 2,
              linkedRequirements: 1,
              unlinkedRequirements: 1,
              coverage: 50,
            },
            rows: [
              { requirementId: 'LG-1', tests: ['tests/a.test.ts'], code: ['src/a.ts'], linked: true },
              // linked=true is intentionally inconsistent; strict validation must recompute from tests/code.
              { requirementId: 'LG-2', tests: [], code: ['src/b.ts'], linked: true },
            ],
          },
          null,
          2,
        ),
        'utf8',
      );

      const result = runCli(['validate', '--traceability', '--strict', '--sources', matrixPath]);
      expect(result.status).toBe(1);
      expect(result.stdout).toContain('Traceability Validation Complete');
      expect(result.stdout).toContain('Progress blocked');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('passes validate --traceability --strict when all requirements are linked', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-traceability-strict-pass-'));
    try {
      const matrixPath = join(dir, 'matrix.json');
      writeFileSync(
        matrixPath,
        JSON.stringify(
          {
            schemaVersion: 'issue-traceability-matrix/v1',
            generatedAt: '2026-02-17T00:00:00Z',
            sourceMap: 'map.json',
            summary: {
              totalRequirements: 2,
              linkedRequirements: 2,
              unlinkedRequirements: 0,
              coverage: 100,
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
              {
                requirementId: 'LG-2',
                tests: ['tests/b.test.ts'],
                code: ['src/b.ts'],
                diagramId: ['DGM-2'],
                morphismId: ['MOR-2'],
                acceptanceTestId: ['AT-2'],
                linked: true,
              },
            ],
          },
          null,
          2,
        ),
        'utf8',
      );

      const result = runCli(['validate', '--traceability', '--strict', '--sources', matrixPath]);
      expect(result.status).toBe(0);
      expect(result.stdout).toContain('Traceability Validation Complete - 100% traceability coverage');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('fails validate --traceability --strict when context-pack IDs are missing', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ae-traceability-context-strict-fail-'));
    try {
      const matrixPath = join(dir, 'matrix.json');
      writeFileSync(
        matrixPath,
        JSON.stringify(
          {
            schemaVersion: 'issue-traceability-matrix/v1',
            generatedAt: '2026-02-17T00:00:00Z',
            sourceMap: 'map.json',
            summary: {
              totalRequirements: 1,
              linkedRequirements: 1,
              unlinkedRequirements: 0,
              coverage: 100,
              contextPackDiagramIds: 1,
              contextPackMorphismIds: 1,
              contextPackAcceptanceTestIds: 1,
              missingDiagramLinks: 1,
              missingMorphismLinks: 0,
              missingAcceptanceTestLinks: 0,
              rowsMissingContextPackLinks: 1,
            },
            rows: [
              {
                requirementId: 'LG-1',
                tests: ['tests/a.test.ts'],
                code: ['src/a.ts'],
                diagramId: [],
                morphismId: ['MOR-1'],
                acceptanceTestId: ['AT-1'],
                linked: true,
              },
            ],
          },
          null,
          2,
        ),
        'utf8',
      );

      const result = runCli(['validate', '--traceability', '--strict', '--sources', matrixPath]);
      expect(result.status).toBe(1);
      expect(result.stdout).toContain('Traceability Validation Complete');
      expect(result.stdout).toContain('Progress blocked');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
