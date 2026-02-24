import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const verifyScript = resolve(repoRoot, 'scripts/context-pack/verify-phase5-templates.mjs');
const schemaPath = resolve(repoRoot, 'schema/context-pack-phase5-templates.schema.json');

const BASE_CONTEXT_PACK = `version: 1
name: inventory-phase5-context-pack
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
  - id: ReservationRecord
    kind: entity
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
  - id: ReleaseInventory
    input:
      itemId: string
      quantity: number
    output:
      released: boolean
    pre:
      - quantity > 0
    post:
      - released implies stock_increased
    failures:
      - ReleaseRejected
  - id: MergeReservations
    input:
      reservationIds: array
    output:
      merged: boolean
    pre:
      - size(reservationIds) > 1
    post:
      - merged implies reservations_compacted
    failures:
      - MergeConflict
diagrams:
  - id: D-1
    statement: ReserveInventory preserves non-negative stock.
    verification:
      - property-test
  - id: D-2
    statement: Reserve/Release composition is balanced.
    verification:
      - model-check
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

describe('context-pack phase5 template validate CLI', () => {
  let workdir: string;
  let reportDir: string;
  let mapPath: string;
  let contextPackDir: string;

  const reportJsonPath = () => join(reportDir, 'context-pack-phase5-report.json');
  const reportMarkdownPath = () => join(reportDir, 'context-pack-phase5-report.md');

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
    workdir = await mkdtemp(join(tmpdir(), 'context-pack-phase5-validate-'));
    contextPackDir = join(workdir, 'spec', 'context-pack');
    reportDir = join(workdir, 'artifacts', 'context-pack');
    mapPath = join(workdir, 'spec', 'context-pack', 'phase5-templates.json');
    await mkdir(contextPackDir, { recursive: true });
    await mkdir(reportDir, { recursive: true });
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('validates complete phase5 template mapping', async () => {
    await writeContextPack();
    await writeFileInWorkdir('tests/services/inventory-service.test.ts', 'export {};\n');
    await writeFileInWorkdir('tests/api/reservations-routes.test.ts', 'export {};\n');
    await writeFileInWorkdir('spec/diagrams/reserve-flow.mmd', 'graph TD;\n');
    await writeFileInWorkdir('src/domain/services.ts', 'export class InventoryService {}\n');

    await writeMap({
      schemaVersion: 'context-pack-phase5-templates/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      pullbacks: [
        {
          id: 'ReserveReleasePullback',
          leftMorphismId: 'ReserveInventory',
          rightMorphismId: 'ReleaseInventory',
          apexObjectId: 'InventoryItem',
          commutingDiagramIds: ['D-1'],
          evidencePaths: ['tests/services/inventory-service.test.ts'],
        },
      ],
      pushouts: [
        {
          id: 'ReserveReleasePushout',
          leftMorphismId: 'ReserveInventory',
          rightMorphismId: 'ReleaseInventory',
          coapexObjectId: 'ReservationRecord',
          commutingDiagramIds: ['D-2'],
          evidencePaths: ['tests/services/inventory-service.test.ts'],
        },
      ],
      monoidalFlows: [
        {
          id: 'ReserveParallelFlow',
          parallelMorphismIds: ['ReserveInventory', 'ReleaseInventory'],
          mergeMorphismId: 'MergeReservations',
          tensorLawChecks: [
            {
              name: 'associativity',
              evidencePaths: ['tests/api/reservations-routes.test.ts'],
            },
          ],
          stringDiagramPaths: ['spec/diagrams/reserve-flow.mmd'],
        },
      ],
      kleisliPipelines: [
        {
          id: 'ReservationEffectPipeline',
          effectType: 'io',
          morphismIds: ['ReserveInventory', 'MergeReservations'],
          pureBoundaryMorphismIds: ['MergeReservations'],
          impureBoundaryMorphismIds: ['ReserveInventory'],
          bindEvidencePaths: ['tests/services/inventory-service.test.ts'],
          sideEffectEvidencePaths: ['src/domain/services.ts'],
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
    expect(report.checkedPullbacks).toBe(1);
    expect(report.checkedPushouts).toBe(1);
    expect(report.checkedMonoidalFlows).toBe(1);
    expect(report.checkedKleisliPipelines).toBe(1);
  });

  it('fails when references, boundaries, and evidence are invalid', async () => {
    await writeContextPack();
    await writeFileInWorkdir('tests/services/inventory-service.test.ts', 'export {};\n');

    await writeMap({
      schemaVersion: 'context-pack-phase5-templates/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      pullbacks: [
        {
          id: 'BrokenPullback',
          leftMorphismId: 'UnknownMorphism',
          rightMorphismId: 'ReleaseInventory',
          apexObjectId: 'InventoryItem',
          commutingDiagramIds: ['D-404'],
          evidencePaths: ['tests/missing-evidence.ts'],
        },
      ],
      pushouts: [
        {
          id: 'BrokenPushout',
          leftMorphismId: 'ReserveInventory',
          rightMorphismId: 'ReleaseInventory',
          coapexObjectId: 'UnknownObject',
          commutingDiagramIds: ['D-2'],
          evidencePaths: ['tests/missing-evidence.ts'],
        },
      ],
      monoidalFlows: [
        {
          id: 'BrokenMonoidal',
          parallelMorphismIds: ['ReserveInventory', 'ReleaseInventory'],
          mergeMorphismId: 'UnknownMerge',
          tensorLawChecks: [
            {
              name: 'associativity',
              evidencePaths: ['tests/missing-evidence.ts'],
            },
          ],
          stringDiagramPaths: ['spec/diagrams/missing.mmd'],
        },
      ],
      kleisliPipelines: [
        {
          id: 'BrokenKleisli',
          effectType: 'io',
          morphismIds: ['ReserveInventory'],
          pureBoundaryMorphismIds: ['ReserveInventory'],
          impureBoundaryMorphismIds: ['ReserveInventory'],
          bindEvidencePaths: ['tests/missing-bind.ts'],
          sideEffectEvidencePaths: ['src/missing/services.ts'],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);
    expect(result.stderr.toString('utf8')).toContain('validation failed');

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.missingMorphismReferences).toBeGreaterThan(0);
    expect(report.summary.missingObjectReferences).toBeGreaterThan(0);
    expect(report.summary.missingDiagramReferences).toBeGreaterThan(0);
    expect(report.summary.boundaryViolations).toBeGreaterThan(0);
    expect(report.summary.missingEvidence).toBeGreaterThan(0);
  });
});
