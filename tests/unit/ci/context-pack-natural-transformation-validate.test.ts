import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const verifyScript = resolve(repoRoot, 'scripts/context-pack/verify-natural-transformation.mjs');
const schemaPath = resolve(repoRoot, 'schema/context-pack-natural-transformation.schema.json');

const BASE_CONTEXT_PACK = `version: 1
name: inventory-minimal-context-pack
problem_statement:
  goals:
    - Keep inventory counts consistent.
  non_goals:
    - Implement pricing logic.
domain_glossary:
  terms:
    - term: inventory_item
      ja: 在庫アイテム
objects:
  - id: InventoryItem
    kind: aggregate
morphisms:
  - id: ReserveInventory
    input:
      itemId: string
      quantity: number
    output:
      reserved: boolean
    pre:
      - quantity > 0
    post:
      - reserved implies stock_decreased
    failures:
      - OutOfStock
diagrams:
  - id: D-1
    statement: ReserveInventory preserves non-negative stock.
    verification:
      - property-test
constraints:
  max_parallel_reservations: 8
acceptance_tests:
  - id: AT-1
    scenario: Reserve succeeds when stock is available.
    expected:
      - reservation accepted
coding_conventions:
  language: TypeScript
  directory:
    - src/
    - tests/
  dependencies:
    runtime:
      - zod
forbidden_changes:
  - Remove ReserveInventory precondition checks.
`;

describe('context-pack natural transformation validate CLI', () => {
  let workdir: string;
  let reportDir: string;
  let mapPath: string;
  let contextPackDir: string;

  const reportJsonPath = () => join(reportDir, 'context-pack-natural-transformation-report.json');
  const reportMarkdownPath = () => join(reportDir, 'context-pack-natural-transformation-report.md');

  const runVerify = () =>
    spawnSync(
      process.execPath,
      [
        verifyScript,
        '--map',
        mapPath,
        '--schema',
        schemaPath,
        '--report-json',
        reportJsonPath(),
        '--report-md',
        reportMarkdownPath(),
      ],
      {
        cwd: workdir,
      },
    );

  const writeContextPack = async (content = BASE_CONTEXT_PACK) => {
    await writeFile(join(contextPackDir, 'minimal.yaml'), content, 'utf8');
  };

  const writeFileInWorkdir = async (relativePath: string, content: string) => {
    const filePath = join(workdir, relativePath);
    await mkdir(dirname(filePath), { recursive: true });
    await writeFile(filePath, content, 'utf8');
  };

  const writeMap = async (payload: object) => {
    await writeFile(mapPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
  };

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'context-pack-natural-transformation-validate-'));
    contextPackDir = join(workdir, 'spec', 'context-pack');
    reportDir = join(workdir, 'artifacts', 'context-pack');
    mapPath = join(workdir, 'spec', 'context-pack', 'natural-transformations.json');
    await mkdir(contextPackDir, { recursive: true });
    await mkdir(reportDir, { recursive: true });
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('validates a consistent natural transformation mapping', async () => {
    await writeContextPack();
    await writeFileInWorkdir(
      'src/domain/services.ts',
      `export class InventoryServiceImpl {
  reserveInventory(): boolean {
    return true;
  }
}
`,
    );
    await writeFileInWorkdir(
      'tests/services/inventory-service.test.ts',
      `describe('inventory-service', () => {
  it('covers regression', () => {});
});
`,
    );
    await writeFileInWorkdir(
      'tests/api/reservations-routes.test.ts',
      `describe('reservations-routes', () => {
  it('covers compatibility', () => {});
});
`,
    );
    await writeMap({
      schemaVersion: 'context-pack-natural-transformation/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      transformations: [
        {
          id: 'ReserveInventoryRefactor',
          changeType: 'refactor',
          before: {
            morphismIds: ['ReserveInventory'],
            diagramIds: ['D-1'],
            acceptanceTestIds: ['AT-1'],
          },
          after: {
            morphismIds: ['ReserveInventory'],
            diagramIds: ['D-1'],
            acceptanceTestIds: ['AT-1'],
          },
          commutativityChecks: {
            regression: ['tests/services/inventory-service.test.ts'],
            compatibility: ['tests/api/reservations-routes.test.ts'],
            differential: [],
          },
          entrypoints: [
            {
              file: 'src/domain/services.ts',
              symbol: 'InventoryServiceImpl',
            },
          ],
          forbiddenChanges: [],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(0);
    expect(result.stderr.toString('utf8')).toBe('');
    expect(existsSync(reportJsonPath())).toBe(true);

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('pass');
    expect(report.summary.totalViolations).toBe(0);
    expect(report.checkedTransformations).toBe(1);
    expect(report.checkedEvidencePatterns).toBe(2);
  });

  it('fails when references, evidence, and forbidden change links are invalid', async () => {
    await writeContextPack();
    await writeMap({
      schemaVersion: 'context-pack-natural-transformation/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      transformations: [
        {
          id: 'ReserveInventoryMigration',
          changeType: 'migration',
          before: {
            morphismIds: ['UnknownMorphism'],
            diagramIds: ['D-1'],
            acceptanceTestIds: ['AT-1'],
          },
          after: {
            morphismIds: ['ReserveInventory'],
            diagramIds: ['UnknownDiagram'],
            acceptanceTestIds: ['UnknownAcceptance'],
          },
          commutativityChecks: {
            regression: ['tests/missing-regression.test.ts'],
            compatibility: [],
            differential: [],
          },
          entrypoints: [
            {
              file: 'src/domain/not-found.ts',
              symbol: 'MissingSymbol',
            },
          ],
          forbiddenChanges: ['Unknown forbidden change'],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);
    expect(result.stderr.toString('utf8')).toContain('validation failed');

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.missingReferences).toBeGreaterThan(0);
    expect(report.summary.missingCommutativity).toBeGreaterThan(0);
    expect(report.summary.missingEvidence).toBeGreaterThan(0);
    expect(report.summary.forbiddenChangeViolations).toBeGreaterThan(0);
    expect(report.summary.missingEntrypoints).toBeGreaterThan(0);
  });

  it('fails breaking changes that do not link forbidden changes', async () => {
    await writeContextPack();
    await writeFileInWorkdir(
      'src/domain/services.ts',
      `export class InventoryServiceImpl {
  reserveInventory(): boolean {
    return true;
  }
}
`,
    );
    await writeFileInWorkdir('tests/services/inventory-service.test.ts', 'export {};\n');
    await writeFileInWorkdir('tests/property/reservation.pbt.test.ts', 'export {};\n');
    await writeMap({
      schemaVersion: 'context-pack-natural-transformation/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      transformations: [
        {
          id: 'ReserveInventoryBreaking',
          changeType: 'breaking',
          before: {
            morphismIds: ['ReserveInventory'],
          },
          after: {
            morphismIds: ['ReserveInventory'],
          },
          commutativityChecks: {
            regression: ['tests/services/inventory-service.test.ts'],
            compatibility: [],
            differential: ['tests/property/reservation.pbt.test.ts'],
          },
          entrypoints: [
            {
              file: 'src/domain/services.ts',
              symbol: 'InventoryServiceImpl',
            },
          ],
          forbiddenChanges: [],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.violations.some((entry: { type: string }) => entry.type === 'forbidden-change-link-missing')).toBe(
      true,
    );
  });
});
