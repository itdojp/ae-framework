import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const verifyScript = resolve(repoRoot, 'scripts/context-pack/verify-functor.mjs');
const schemaPath = resolve(repoRoot, 'schema/context-pack-functor-map.schema.json');

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

describe('context-pack functor validate CLI', () => {
  let workdir: string;
  let reportDir: string;
  let mapPath: string;
  let contextPackDir: string;

  const reportJsonPath = () => join(reportDir, 'context-pack-functor-report.json');
  const reportMarkdownPath = () => join(reportDir, 'context-pack-functor-report.md');

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
    workdir = await mkdtemp(join(tmpdir(), 'context-pack-functor-validate-'));
    contextPackDir = join(workdir, 'spec', 'context-pack');
    reportDir = join(workdir, 'artifacts', 'context-pack');
    mapPath = join(workdir, 'spec', 'context-pack', 'functor-map.json');
    await mkdir(contextPackDir, { recursive: true });
    await mkdir(reportDir, { recursive: true });
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('validates consistent context-pack and functor mapping', async () => {
    await writeContextPack();
    await writeFileInWorkdir(
      'src/domain/item.ts',
      `export type InventoryItem = {
  id: string;
  stock: number;
};
`,
    );
    await writeFileInWorkdir(
      'src/domain/reserve.ts',
      `import type { InventoryItem } from './item';

export function reserveInventory(item: InventoryItem, quantity: number): boolean {
  return item.stock >= quantity;
}
`,
    );
    await writeMap({
      schemaVersion: 'context-pack-functor-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      objects: [
        {
          id: 'InventoryItem',
          moduleGlobs: ['src/domain/**/*.ts'],
          layer: 'domain',
        },
      ],
      morphisms: [
        {
          id: 'ReserveInventory',
          entrypoints: [{ file: 'src/domain/reserve.ts', symbol: 'reserveInventory' }],
        },
      ],
      dependencyRules: [{ from: 'InventoryItem', to: 'InventoryItem', allowed: true }],
    });

    const result = runVerify();
    expect(result.status).toBe(0);
    expect(result.stderr.toString('utf8')).toBe('');
    expect(existsSync(reportJsonPath())).toBe(true);

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('pass');
    expect(report.summary.totalViolations).toBe(0);
    expect(report.mappingObjectCount).toBe(1);
    expect(report.mappingMorphismCount).toBe(1);
  });

  it('fails when context-pack object/morphism are not mapped', async () => {
    await writeContextPack();
    await writeFileInWorkdir(
      'src/domain/reserve.ts',
      `export function reserveInventory(): boolean {
  return true;
}
`,
    );
    await writeMap({
      schemaVersion: 'context-pack-functor-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      objects: [{ id: 'OrderAggregate', moduleGlobs: ['src/domain/**/*.ts'] }],
      morphisms: [{ id: 'CreateOrder', entrypoints: [{ file: 'src/domain/reserve.ts', symbol: 'reserveInventory' }] }],
    });

    const result = runVerify();
    expect(result.status).toBe(2);
    expect(result.stderr.toString('utf8')).toContain('validation failed');

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.missingObjectMappings).toBeGreaterThan(0);
    expect(report.summary.missingMorphismMappings).toBeGreaterThan(0);
    expect(report.summary.unknownObjectMappings).toBeGreaterThan(0);
    expect(report.summary.unknownMorphismMappings).toBeGreaterThan(0);
  });

  it('fails on forbidden dependency rule violations', async () => {
    const contextPack = BASE_CONTEXT_PACK.replace(
      'objects:\n  - id: InventoryItem\n    kind: aggregate',
      `objects:
  - id: InventoryItem
    kind: aggregate
  - id: PricingPolicy
    kind: value_object`,
    );
    await writeContextPack(contextPack);
    await writeFileInWorkdir(
      'src/domain/reserve.ts',
      `import { policyVersion } from '../pricing/policy';

export function reserveInventory(quantity: number): string {
  return policyVersion + String(quantity);
}
`,
    );
    await writeFileInWorkdir(
      'src/pricing/policy.ts',
      `export const policyVersion = 'v1-';
`,
    );
    await writeMap({
      schemaVersion: 'context-pack-functor-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      objects: [
        { id: 'InventoryItem', moduleGlobs: ['src/domain/**/*.ts'] },
        { id: 'PricingPolicy', moduleGlobs: ['src/pricing/**/*.ts'] },
      ],
      morphisms: [
        { id: 'ReserveInventory', entrypoints: [{ file: 'src/domain/reserve.ts', symbol: 'reserveInventory' }] },
      ],
      dependencyRules: [{ from: 'InventoryItem', to: 'PricingPolicy', allowed: false, reason: 'layering rule' }],
    });

    const result = runVerify();
    expect(result.status).toBe(2);

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.forbiddenDependencyViolations).toBeGreaterThan(0);
    expect(report.violations.some((entry: { type: string }) => entry.type === 'layer-violation')).toBe(true);
  });

  it('fails when morphism symbol is missing from entrypoint file', async () => {
    await writeContextPack();
    await writeFileInWorkdir(
      'src/domain/reserve.ts',
      `export function reserveInventory(): boolean {
  return true;
}
`,
    );
    await writeMap({
      schemaVersion: 'context-pack-functor-map/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      objects: [{ id: 'InventoryItem', moduleGlobs: ['src/domain/**/*.ts'] }],
      morphisms: [
        { id: 'ReserveInventory', entrypoints: [{ file: 'src/domain/reserve.ts', symbol: 'reserveInventoryV2' }] },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);
    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.missingEntrypoints).toBe(1);
    expect(report.violations.some((entry: { type: string }) => entry.type === 'morphism-entrypoint-missing-symbol')).toBe(true);
  });
});
