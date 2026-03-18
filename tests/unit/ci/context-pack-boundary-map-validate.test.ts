import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const verifyScript = resolve(repoRoot, 'scripts/context-pack/verify-boundary-map.mjs');
const schemaPath = resolve(repoRoot, 'schema/context-pack-boundary-map.schema.json');

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
acceptance_tests:
  - id: AT-1
    scenario: Reserve succeeds when stock is available.
    expected:
      - reservation accepted
forbidden_changes:
  - Remove ReserveInventory precondition checks.
`;

describe('context-pack boundary map validate CLI', () => {
  let workdir: string;
  let reportDir: string;
  let mapPath: string;
  let contextPackDir: string;

  const reportJsonPath = () => join(reportDir, 'context-pack-boundary-map-report.json');
  const reportMarkdownPath = () => join(reportDir, 'context-pack-boundary-map-report.md');

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

  const writeMap = async (payload: object) => {
    await writeFile(mapPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
  };

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'context-pack-boundary-map-validate-'));
    contextPackDir = join(workdir, 'spec', 'context-pack');
    reportDir = join(workdir, 'artifacts', 'context-pack');
    mapPath = join(workdir, 'spec', 'context-pack', 'boundary-map.json');
    await mkdir(contextPackDir, { recursive: true });
    await mkdir(reportDir, { recursive: true });
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('validates a consistent boundary map', async () => {
    await writeContextPack();
    await writeMap({
      schemaVersion: 'context-pack-boundary-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      slices: [
        {
          id: 'inventory-item-model',
          produces: [{ kind: 'object', refId: 'InventoryItem' }],
        },
        {
          id: 'reservation-flow',
          consumes: [
            {
              kind: 'object',
              refId: 'InventoryItem',
              upstream: { type: 'slice', sliceId: 'inventory-item-model' },
            },
            {
              kind: 'forbidden-change',
              refId: 'Remove ReserveInventory precondition checks.',
              upstream: { type: 'context-pack' },
            },
          ],
          produces: [
            { kind: 'morphism', refId: 'ReserveInventory' },
            { kind: 'diagram', refId: 'D-1' },
            { kind: 'acceptance-test', refId: 'AT-1' },
          ],
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
    expect(report.checkedSlices).toBe(2);
    expect(report.checkedConsumes).toBe(2);
  });

  it('fails when a consumed ref has no upstream producer', async () => {
    await writeContextPack();
    await writeMap({
      schemaVersion: 'context-pack-boundary-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      slices: [
        {
          id: 'upstream-placeholder',
          consumes: [
            {
              kind: 'forbidden-change',
              refId: 'Remove ReserveInventory precondition checks.',
              upstream: { type: 'context-pack' },
            },
          ],
        },
        {
          id: 'reservation-flow',
          consumes: [
            {
              kind: 'object',
              refId: 'InventoryItem',
              upstream: { type: 'slice', sliceId: 'upstream-placeholder' },
            },
          ],
          produces: [{ kind: 'morphism', refId: 'ReserveInventory' }],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);
    expect(result.stderr.toString('utf8')).toContain('validation failed');

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.missingUpstreamProducers).toBe(1);
    expect(report.violations.some((entry: { type: string }) => entry.type === 'boundary-upstream-producer-missing')).toBe(true);
  });

  it('fails when a consumed ref points to a missing upstream slice', async () => {
    await writeContextPack();
    await writeMap({
      schemaVersion: 'context-pack-boundary-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      slices: [
        {
          id: 'reservation-flow',
          consumes: [
            {
              kind: 'object',
              refId: 'InventoryItem',
              upstream: { type: 'slice', sliceId: 'inventory-item-model' },
            },
          ],
          produces: [{ kind: 'morphism', refId: 'ReserveInventory' }],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.missingUpstreamSlices).toBe(1);
    expect(report.violations.some((entry: { type: string }) => entry.type === 'boundary-upstream-slice-missing')).toBe(true);
  });

  it('fails when two slices produce the same ref', async () => {
    await writeContextPack();
    await writeMap({
      schemaVersion: 'context-pack-boundary-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      slices: [
        {
          id: 'inventory-item-model',
          produces: [{ kind: 'object', refId: 'InventoryItem' }],
        },
        {
          id: 'inventory-shadow-model',
          produces: [{ kind: 'object', refId: 'InventoryItem' }],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.duplicateProducedRefs).toBe(1);
    expect(report.violations.some((entry: { type: string }) => entry.type === 'boundary-producer-duplicate')).toBe(true);
  });

  it('rejects cyclic slice dependencies', async () => {
    await writeContextPack();
    await writeMap({
      schemaVersion: 'context-pack-boundary-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      slices: [
        {
          id: 'inventory-item-model',
          consumes: [
            {
              kind: 'morphism',
              refId: 'ReserveInventory',
              upstream: { type: 'slice', sliceId: 'reservation-flow' },
            },
          ],
          produces: [{ kind: 'object', refId: 'InventoryItem' }],
        },
        {
          id: 'reservation-flow',
          consumes: [
            {
              kind: 'object',
              refId: 'InventoryItem',
              upstream: { type: 'slice', sliceId: 'inventory-item-model' },
            },
          ],
          produces: [{ kind: 'morphism', refId: 'ReserveInventory' }],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.cycleViolations).toBe(1);
    expect(report.violations.some((entry: { type: string }) => entry.type === 'boundary-slice-cycle')).toBe(true);
  });

  it('fails when no context-pack sources remain after excluding the map file itself', async () => {
    await writeMap({
      schemaVersion: 'context-pack-boundary-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      slices: [],
    });

    const result = runVerify();
    expect(result.status).toBe(2);

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.scannedContextPackFiles).toBe(0);
    expect(report.violations.some((entry: { type: string }) => entry.type === 'context-pack-sources-empty')).toBe(true);
  });

  it('counts auxiliary context-pack sidecars as skipped files', async () => {
    await writeContextPack();
    await writeFile(
      join(contextPackDir, 'functor-map.json'),
      `${JSON.stringify(
        {
          schemaVersion: 'context-pack-functor-map/v1',
          contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
          objects: [{ id: 'InventoryItem', moduleGlobs: ['src/domain/**/*.ts'] }],
          morphisms: [{ id: 'ReserveInventory', entrypoints: [{ file: 'src/domain/services.ts' }] }],
        },
        null,
        2,
      )}\n`,
      'utf8',
    );
    await writeMap({
      schemaVersion: 'context-pack-boundary-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      slices: [
        {
          id: 'inventory-item-model',
          produces: [{ kind: 'object', refId: 'InventoryItem' }],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('pass');
    expect(report.scannedContextPackFiles).toBe(1);
    expect(report.skippedAuxiliaryFiles).toBe(1);
  });

  it('escapes backslashes in markdown report cells', async () => {
    await writeContextPack();
    await writeMap({
      schemaVersion: 'context-pack-boundary-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      slices: [
        {
          id: 'reservation-flow',
          consumes: [
            {
              kind: 'object',
              refId: 'Inventory\\\\Item',
              upstream: { type: 'slice', sliceId: 'inventory-item-model' },
            },
          ],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);

    const markdown = await readFile(reportMarkdownPath(), 'utf8');
    expect(markdown).toContain('Inventory\\\\\\\\Item');
  });
});
