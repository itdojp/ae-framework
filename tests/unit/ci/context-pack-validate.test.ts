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
assurance:
  profile: inventory-consistency-v1
  claim_refs:
    - no-negative-stock
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

const VALID_DISCOVERY_PACK_YAML = `version: 1
profile: rdra-lite
sources:
  - id: SRC-1
    kind: markdown
    path: docs/discovery.md
actors: []
external_systems: []
goals:
  - id: GOAL-1
    status: approved
    title: Keep checkout traceable.
    source_refs: [SRC-1]
    traces_to: []
requirements:
  - id: REQ-1
    status: approved
    title: Reserve inventory on checkout.
    source_refs: [SRC-1]
    traces_to: []
business_use_cases:
  - id: BUC-1
    status: approved
    title: Complete checkout.
    source_refs: [SRC-1]
    traces_to: []
flows: []
decisions:
  - id: DEC-1
    status: reviewed
    title: Validate before submit.
    source_refs: [SRC-1]
    traces_to: []
assumptions: []
open_questions: []
`;

const VALID_CONTEXT_PACK_WITH_DISCOVERY_YAML = `version: 1
name: inventory-discovery-context-pack
upstream:
  discovery_pack:
    path: spec/discovery-pack/sample.yaml
    profile: rdra-lite
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
    upstream_refs:
      goal_ids: [GOAL-1]
      requirement_ids: [REQ-1]
      business_use_case_ids: [BUC-1]
      decision_ids: [DEC-1]
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
    upstream_refs:
      requirement_ids: [REQ-1]
constraints:
  max_parallel_reservations: 8
assurance:
  profile: inventory-consistency-v1
  claim_refs:
    - no-negative-stock
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

  const runValidate = (sourcesPattern: string, extraArgs: string[] = []) =>
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
        ...extraArgs,
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

  it('skips phase5 template map files under context-pack sources', async () => {
    await writeFile(join(sourcesDir, 'valid.yaml'), VALID_CONTEXT_PACK_YAML, 'utf8');
    await writeFile(
      join(sourcesDir, 'phase5-templates.json'),
      JSON.stringify(
        {
          schemaVersion: 'context-pack-phase5-templates/v1',
          contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
          pullbacks: [],
          pushouts: [],
          monoidalFlows: [],
          kleisliPipelines: [],
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

  it('skips boundary map files under context-pack sources', async () => {
    await writeFile(join(sourcesDir, 'valid.yaml'), VALID_CONTEXT_PACK_YAML, 'utf8');
    await writeFile(
      join(sourcesDir, 'boundary-map.json'),
      JSON.stringify(
        {
          schemaVersion: 'context-pack-boundary-map/v1',
          contextPackSources: ['spec/context-pack/**/*.{yml,yaml,json}'],
          slices: [
            {
              id: 'inventory-item-model',
              produces: [{ kind: 'object', refId: 'InventoryItem' }],
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

  it('passes with discovery upstream refs when the source pack matches', async () => {
    const discoveryDir = join(workdir, 'spec', 'discovery-pack');
    await mkdir(discoveryDir, { recursive: true });
    await writeFile(join(discoveryDir, 'sample.yaml'), VALID_DISCOVERY_PACK_YAML, 'utf8');
    await writeFile(join(sourcesDir, 'valid.yaml'), VALID_CONTEXT_PACK_WITH_DISCOVERY_YAML, 'utf8');

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'), [
      '--discovery-pack',
      join(discoveryDir, '*.{yaml,yml,json}'),
    ]);

    expect(result.status).toBe(0);
    expect(result.stderr.toString('utf8')).toBe('');

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('pass');
    expect(report.warnings).toEqual([]);
  });

  it('warns when approved discovery requirements are unmapped', async () => {
    const discoveryDir = join(workdir, 'spec', 'discovery-pack');
    await mkdir(discoveryDir, { recursive: true });
    await writeFile(
      join(discoveryDir, 'sample.yaml'),
      VALID_DISCOVERY_PACK_YAML.replace(
        'requirements:\n  - id: REQ-1\n    status: approved\n    title: Reserve inventory on checkout.\n    source_refs: [SRC-1]\n    traces_to: []\n',
        [
          'requirements:',
          '  - id: REQ-1',
          '    status: approved',
          '    title: Reserve inventory on checkout.',
          '    source_refs: [SRC-1]',
          '    traces_to: []',
          '  - id: REQ-2',
          '    status: approved',
          '    title: Additional approved requirement.',
          '    source_refs: [SRC-1]',
          '    traces_to: []',
          '',
        ].join('\n'),
      ),
      'utf8',
    );
    await writeFile(join(sourcesDir, 'valid.yaml'), VALID_CONTEXT_PACK_WITH_DISCOVERY_YAML, 'utf8');

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'), [
      '--discovery-pack',
      join(discoveryDir, '*.{yaml,yml,json}'),
    ]);

    expect(result.status).toBe(0);
    expect(result.stdout.toString('utf8')).toContain('validation completed with warnings');

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('warn');
    expect(report.warnings.some((entry: { type: string }) => entry.type === 'unmapped-approved-requirement')).toBe(true);
  });

  it('warns when approved discovery business use cases are unmapped', async () => {
    const discoveryDir = join(workdir, 'spec', 'discovery-pack');
    await mkdir(discoveryDir, { recursive: true });
    await writeFile(
      join(discoveryDir, 'sample.yaml'),
      VALID_DISCOVERY_PACK_YAML.replace(
        'business_use_cases:\n  - id: BUC-1\n    status: approved\n    title: Complete checkout.\n    source_refs: [SRC-1]\n    traces_to: []\n',
        [
          'business_use_cases:',
          '  - id: BUC-1',
          '    status: approved',
          '    title: Complete checkout.',
          '    source_refs: [SRC-1]',
          '    traces_to: []',
          '  - id: BUC-2',
          '    status: approved',
          '    title: Additional approved business use case.',
          '    source_refs: [SRC-1]',
          '    traces_to: []',
          '',
        ].join('\n'),
      ),
      'utf8',
    );
    await writeFile(join(sourcesDir, 'valid.yaml'), VALID_CONTEXT_PACK_WITH_DISCOVERY_YAML, 'utf8');

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'), [
      '--discovery-pack',
      join(discoveryDir, '*.{yaml,yml,json}'),
    ]);

    expect(result.status).toBe(0);
    expect(result.stdout.toString('utf8')).toContain('validation completed with warnings');

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('warn');
    expect(report.warnings.some((entry: { type: string }) => entry.type === 'unmapped-approved-business-use-case')).toBe(true);
  });

  it('fails when upstream refs point to unknown discovery IDs', async () => {
    const discoveryDir = join(workdir, 'spec', 'discovery-pack');
    await mkdir(discoveryDir, { recursive: true });
    await writeFile(join(discoveryDir, 'sample.yaml'), VALID_DISCOVERY_PACK_YAML, 'utf8');
    await writeFile(
      join(sourcesDir, 'invalid-upstream.yaml'),
      VALID_CONTEXT_PACK_WITH_DISCOVERY_YAML.replace('requirement_ids: [REQ-1]', 'requirement_ids: [REQ-404]'),
      'utf8',
    );

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'), [
      '--discovery-pack',
      join(discoveryDir, '*.{yaml,yml,json}'),
    ]);

    expect(result.status).toBe(2);
    expect(result.stderr.toString('utf8')).toContain('validation failed');

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('fail');
    expect(report.errors.some((entry: { type: string }) => entry.type === 'upstream-ref-missing')).toBe(true);
  });

  it('warns when required upstream_refs are missing', async () => {
    const discoveryDir = join(workdir, 'spec', 'discovery-pack');
    await mkdir(discoveryDir, { recursive: true });
    await writeFile(join(discoveryDir, 'sample.yaml'), VALID_DISCOVERY_PACK_YAML, 'utf8');
    await writeFile(
      join(sourcesDir, 'missing-upstream-refs.yaml'),
      VALID_CONTEXT_PACK_WITH_DISCOVERY_YAML.replace(
        [
          '    upstream_refs:',
          '      goal_ids: [GOAL-1]',
          '      requirement_ids: [REQ-1]',
          '      business_use_case_ids: [BUC-1]',
          '      decision_ids: [DEC-1]',
        ].join('\n'),
        '',
      ),
      'utf8',
    );

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'), [
      '--discovery-pack',
      join(discoveryDir, '*.{yaml,yml,json}'),
    ]);

    expect(result.status).toBe(0);
    expect(result.stdout.toString('utf8')).toContain('validation completed with warnings');

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('warn');
    expect(report.warnings.some((entry: { type: string }) => entry.type === 'upstream-refs-missing')).toBe(true);
  });

  it('warns when declared discovery profile does not match the source profile', async () => {
    const discoveryDir = join(workdir, 'spec', 'discovery-pack');
    await mkdir(discoveryDir, { recursive: true });
    await writeFile(join(discoveryDir, 'sample.yaml'), VALID_DISCOVERY_PACK_YAML, 'utf8');
    await writeFile(
      join(sourcesDir, 'profile-mismatch.yaml'),
      VALID_CONTEXT_PACK_WITH_DISCOVERY_YAML.replace('profile: rdra-lite', 'profile: rdra-strict'),
      'utf8',
    );

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'), [
      '--discovery-pack',
      join(discoveryDir, '*.{yaml,yml,json}'),
    ]);

    expect(result.status).toBe(0);
    expect(result.stdout.toString('utf8')).toContain('validation completed with warnings');

    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.status).toBe('warn');
    expect(report.warnings.some((entry: { type: string }) => entry.type === 'discovery-pack-profile-mismatch')).toBe(true);
  });

  it('does not treat a missing declared discovery path as an ambiguous source when one real CLI source exists', async () => {
    const discoveryDir = join(workdir, 'spec', 'discovery-pack');
    await mkdir(discoveryDir, { recursive: true });
    await writeFile(join(discoveryDir, 'sample.yaml'), VALID_DISCOVERY_PACK_YAML, 'utf8');
    await writeFile(
      join(sourcesDir, 'valid.yaml'),
      VALID_CONTEXT_PACK_WITH_DISCOVERY_YAML.replace(
        'path: spec/discovery-pack/sample.yaml',
        'path: spec/discovery-pack/missing.yaml',
      ),
      'utf8',
    );

    const result = runValidate(join(sourcesDir, '*.{yaml,yml,json}'), [
      '--discovery-pack',
      join(discoveryDir, '*.{yaml,yml,json}'),
    ]);

    expect(result.status).toBe(0);
    const report = JSON.parse(await readFile(join(reportDir, 'context-pack-validate-report.json'), 'utf8'));
    expect(report.errors.some((entry: { type: string }) => entry.type === 'discovery-pack-source-ambiguous')).toBe(false);
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
