import { describe, expect, it, beforeEach, afterEach } from 'vitest';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { existsSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const validateScript = resolve(repoRoot, 'scripts/context-pack/validate.mjs');
const schemaPath = resolve(repoRoot, 'schema/context-pack-v1.schema.json');

const VALID_CONTEXT_PACK_YAML = `version: 1
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

describe('context-pack validate CLI', () => {
  let workdir: string;
  let sourcesDir: string;
  let reportDir: string;

  const runValidate = (sourcesPattern: string) =>
    spawnSync(
      process.execPath,
      [
        validateScript,
        '--sources',
        sourcesPattern,
        '--schema',
        schemaPath,
        '--report-json',
        join(reportDir, 'context-pack-validate-report.json'),
        '--report-md',
        join(reportDir, 'context-pack-validate-report.md'),
      ],
      {
        cwd: workdir,
      }
    );

  beforeEach(async () => {
    workdir = await mkdtemp(join(tmpdir(), 'context-pack-validate-'));
    sourcesDir = join(workdir, 'spec', 'context-pack');
    reportDir = join(workdir, 'artifacts', 'context-pack');
    await mkdir(sourcesDir, { recursive: true });
  });

  afterEach(async () => {
    await rm(workdir, { recursive: true, force: true });
  });

  it('validates a valid YAML context-pack file', async () => {
    await writeFile(join(sourcesDir, 'valid.yaml'), VALID_CONTEXT_PACK_YAML, 'utf8');

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'));
    expect(result.status).toBe(0);
    expect(result.stderr.toString('utf8')).toBe('');
    expect(result.stdout.toString('utf8')).toContain('validation passed');

    const reportPath = join(reportDir, 'context-pack-validate-report.json');
    expect(existsSync(reportPath)).toBe(true);
    const report = JSON.parse(await readFile(reportPath, 'utf8'));
    expect(report.status).toBe('pass');
    expect(report.scannedFiles).toBe(1);
    expect(report.validFiles).toBe(1);
    expect(report.invalidFiles).toBe(0);
    expect(Array.isArray(report.errors)).toBe(true);
    expect(report.errors.length).toBe(0);
  });

  it('fails with exit code 2 when a file violates schema', async () => {
    const invalidPayload = {
      version: 1,
      name: 'invalid-context-pack',
      problem_statement: {
        goals: ['x'],
        non_goals: [],
      },
      domain_glossary: {
        terms: [{ term: 'inventory_item' }],
      },
      objects: [{ id: 'InventoryItem', kind: 'aggregate' }],
      morphisms: [],
      diagrams: [],
      constraints: {},
      acceptance_tests: [],
      coding_conventions: {
        language: 'TypeScript',
        directory: ['src/'],
        dependencies: {},
      },
      forbidden_changes: [],
    };
    await writeFile(join(sourcesDir, 'invalid.json'), `${JSON.stringify(invalidPayload, null, 2)}\n`, 'utf8');

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'));
    expect(result.status).toBe(2);
    expect(result.stderr.toString('utf8')).toContain('validation failed');

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.scannedFiles).toBe(1);
    expect(report.validFiles).toBe(0);
    expect(report.invalidFiles).toBe(1);
    expect(report.errors.length).toBeGreaterThan(0);
    expect(report.errors[0]?.file).toContain('invalid.json');
    expect(report.errors[0]?.instancePath).toContain('/domain_glossary/terms/0');
    expect(report.errors[0]?.keyword).toBe('required');
  });

  it('fails when one of multiple files is invalid', async () => {
    await writeFile(join(sourcesDir, 'valid.yaml'), VALID_CONTEXT_PACK_YAML, 'utf8');
    await writeFile(
      join(sourcesDir, 'invalid.json'),
      JSON.stringify(
        {
          version: 1,
          name: 'invalid-context-pack',
        },
        null,
        2
      ),
      'utf8'
    );

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'));
    expect(result.status).toBe(2);

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.scannedFiles).toBe(2);
    expect(report.validFiles).toBe(1);
    expect(report.invalidFiles).toBe(1);
    expect(report.skippedFiles).toBe(0);
    expect(report.errors.some((entry: { file: string }) => entry.file.includes('invalid.json'))).toBe(true);
  });

  it('skips functor map files under context-pack sources', async () => {
    await writeFile(join(sourcesDir, 'valid.yaml'), VALID_CONTEXT_PACK_YAML, 'utf8');
    await writeFile(
      join(sourcesDir, 'functor-map.json'),
      JSON.stringify(
        {
          schemaVersion: 'context-pack-functor-map/v1',
          contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
          objects: [{ id: 'InventoryItem', moduleGlobs: ['src/domain/**/*.ts'] }],
          morphisms: [{ id: 'ReserveInventory', entrypoints: [{ file: 'src/domain/services.ts' }] }],
        },
        null,
        2
      ),
      'utf8'
    );

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'));
    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('pass');
    expect(report.scannedFiles).toBe(2);
    expect(report.validFiles).toBe(1);
    expect(report.invalidFiles).toBe(0);
    expect(report.skippedFiles).toBe(1);
  });

  it('skips natural transformation map files under context-pack sources', async () => {
    await writeFile(join(sourcesDir, 'valid.yaml'), VALID_CONTEXT_PACK_YAML, 'utf8');
    await writeFile(
      join(sourcesDir, 'natural-transformations.json'),
      JSON.stringify(
        {
          schemaVersion: 'context-pack-natural-transformation/v1',
          contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
          transformations: [
            {
              id: 'ReserveInventoryRefactor',
              changeType: 'refactor',
              before: { morphismIds: ['ReserveInventory'] },
              after: { morphismIds: ['ReserveInventory'] },
              commutativityChecks: {
                regression: ['tests/services/inventory-service.test.ts'],
                compatibility: ['tests/api/reservations-routes.test.ts'],
                differential: [],
              },
            },
          ],
        },
        null,
        2
      ),
      'utf8'
    );

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'));
    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('pass');
    expect(report.scannedFiles).toBe(2);
    expect(report.validFiles).toBe(1);
    expect(report.invalidFiles).toBe(0);
    expect(report.skippedFiles).toBe(1);
  });

  it('skips product/coproduct map files under context-pack sources', async () => {
    await writeFile(join(sourcesDir, 'valid.yaml'), VALID_CONTEXT_PACK_YAML, 'utf8');
    await writeFile(
      join(sourcesDir, 'product-coproduct-map.json'),
      JSON.stringify(
        {
          schemaVersion: 'context-pack-product-coproduct/v1',
          contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
          products: [
            {
              morphismId: 'ReserveInventory',
              requiredInputKeys: ['itemId', 'quantity'],
            },
          ],
          coproducts: [
            {
              morphismId: 'ReserveInventory',
              variants: [{ name: 'OutOfStock', evidencePaths: ['tests/services/inventory-service.test.ts'] }],
            },
          ],
        },
        null,
        2
      ),
      'utf8'
    );

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'));
    expect(result.status).toBe(0);

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('pass');
    expect(report.scannedFiles).toBe(2);
    expect(report.validFiles).toBe(1);
    expect(report.invalidFiles).toBe(0);
    expect(report.skippedFiles).toBe(1);
  });

  it('rejects context-pack payload with unsupported version', async () => {
    await writeFile(
      join(sourcesDir, 'invalid-version.json'),
      JSON.stringify(
        {
          version: 2,
          name: 'future-context-pack',
          problem_statement: { goals: [], non_goals: [] },
          domain_glossary: { terms: [] },
          objects: [],
          morphisms: [],
          diagrams: [],
          constraints: {},
          acceptance_tests: [],
          coding_conventions: { language: 'TypeScript', directory: [], dependencies: {} },
          forbidden_changes: [],
        },
        null,
        2
      ),
      'utf8'
    );

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'));
    expect(result.status).toBe(2);

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.errors.some((entry: { keyword: string }) => entry.keyword === 'const')).toBe(true);
  });

  it('escapes markdown table cells in validation report', async () => {
    const dangerousName = 'invalid|<tag>.json';
    await writeFile(join(sourcesDir, dangerousName), '<invalid-json>', 'utf8');

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'));
    expect(result.status).toBe(2);

    const markdown = await readFile(join(reportDir, 'context-pack-validate-report.md'), 'utf8');
    expect(markdown).toContain('invalid\\|&lt;tag&gt;.json');
    expect(markdown).toContain('&lt;');
  });
});
