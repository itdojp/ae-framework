import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const verifyScript = resolve(repoRoot, 'scripts/context-pack/verify-product-coproduct.mjs');
const schemaPath = resolve(repoRoot, 'schema/context-pack-product-coproduct.schema.json');

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

describe('context-pack product/coproduct validate CLI', () => {
  let workdir: string;
  let reportDir: string;
  let mapPath: string;
  let contextPackDir: string;

  const reportJsonPath = () => join(reportDir, 'context-pack-product-coproduct-report.json');
  const reportMarkdownPath = () => join(reportDir, 'context-pack-product-coproduct-report.md');

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
    workdir = await mkdtemp(join(tmpdir(), 'context-pack-product-coproduct-validate-'));
    contextPackDir = join(workdir, 'spec', 'context-pack');
    reportDir = join(workdir, 'artifacts', 'context-pack');
    mapPath = join(workdir, 'spec', 'context-pack', 'product-coproduct-map.json');
    await mkdir(contextPackDir, { recursive: true });
    await mkdir(reportDir, { recursive: true });
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('validates complete product/coproduct coverage', async () => {
    await writeContextPack();
    await writeFileInWorkdir('tests/services/inventory-service.test.ts', 'export {};\n');
    await writeMap({
      schemaVersion: 'context-pack-product-coproduct/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      products: [
        {
          morphismId: 'ReserveInventory',
          requiredInputKeys: ['itemId', 'quantity'],
          disallowGenericDtoKeys: true,
        },
      ],
      coproducts: [
        {
          morphismId: 'ReserveInventory',
          variants: [{ name: 'OutOfStock', evidencePaths: ['tests/services/inventory-service.test.ts'] }],
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
    expect(report.totalFailureVariants).toBe(1);
    expect(report.coveredFailureVariants).toBe(1);
    expect(report.uncoveredFailureVariants).toBe(0);
  });

  it('fails when required input and variant coverage are incomplete', async () => {
    await writeContextPack();
    await writeMap({
      schemaVersion: 'context-pack-product-coproduct/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      products: [
        {
          morphismId: 'ReserveInventory',
          requiredInputKeys: ['itemId'],
        },
      ],
      coproducts: [
        {
          morphismId: 'ReserveInventory',
          variants: [],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);
    expect(result.stderr.toString('utf8')).toContain('validation failed');

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.inputCoverageGaps).toBeGreaterThan(0);
    expect(report.summary.variantCoverageGaps).toBeGreaterThan(0);
    expect(report.uncoveredFailureVariants).toBeGreaterThan(0);
  });

  it('fails when ambiguous DTO keys and missing evidence exist', async () => {
    const dtoContextPack = BASE_CONTEXT_PACK.replace(
      'input:\n      itemId: string\n      quantity: number',
      `input:
      payload: object`,
    );
    await writeContextPack(dtoContextPack);
    await writeMap({
      schemaVersion: 'context-pack-product-coproduct/v1',
      contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
      products: [
        {
          morphismId: 'ReserveInventory',
          requiredInputKeys: ['payload'],
          disallowGenericDtoKeys: true,
        },
      ],
      coproducts: [
        {
          morphismId: 'ReserveInventory',
          variants: [{ name: 'OutOfStock', evidencePaths: ['tests/missing-outofstock.test.ts'] }],
        },
      ],
    });

    const result = runVerify();
    expect(result.status).toBe(2);

    const report = JSON.parse(await readFile(reportJsonPath(), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.summary.ambiguousDtoKeys).toBeGreaterThan(0);
    expect(report.summary.missingEvidence).toBeGreaterThan(0);
  });
});
