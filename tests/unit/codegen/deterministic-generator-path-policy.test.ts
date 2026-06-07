import { existsSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { DeterministicCodeGenerator } from '../../../src/codegen/deterministic-generator.js';

const testRoot = path.join(process.cwd(), 'artifacts', 'codegen-path-policy-test');

const validAeir = {
  version: '1.0.0',
  metadata: {
    name: 'PathPolicyTest',
    created: '2025-01-01T00:00:00.000Z',
    updated: '2025-01-01T00:00:00.000Z',
  },
  glossary: [],
  domain: [
    {
      name: 'Product',
      fields: [
        { name: 'id', type: 'string', required: true },
        { name: 'name', type: 'string', required: true },
      ],
    },
  ],
  invariants: [],
  usecases: [],
  api: [],
};

describe('DeterministicCodeGenerator path policy', () => {
  beforeEach(() => {
    rmSync(testRoot, { recursive: true, force: true });
    mkdirSync(testRoot, { recursive: true });
  });

  afterEach(() => {
    rmSync(testRoot, { recursive: true, force: true });
  });

  it('writes generated files only under the configured output directory', async () => {
    const inputPath = path.join(testRoot, 'ae-ir.json');
    const outputDir = path.join(testRoot, 'generated');
    writeFileSync(inputPath, JSON.stringify(validAeir, null, 2), 'utf8');

    const generator = new DeterministicCodeGenerator({
      inputPath,
      outputDir,
      target: 'react',
      enableDriftDetection: false,
    });

    const manifest = await generator.generate();

    expect(manifest.files.map((file) => file.filePath).sort()).toEqual([
      'components/ProductForm.tsx',
      'components/ProductList.tsx',
    ]);
    expect(manifest.metadata.boundary).toMatchObject({
      kind: 'generated-code',
      source: 'ae-ir',
      materialized: true,
    });
    expect(manifest.files[0]?.boundary).toMatchObject({
      kind: 'generated-code',
      source: 'ae-ir',
      target: 'react',
      materialized: true,
    });
    expect(existsSync(path.join(outputDir, 'components', 'ProductForm.tsx'))).toBe(true);
    expect(existsSync(path.join(outputDir, '.codegen-manifest.json'))).toBe(true);
  });

  it('previews generated files without materializing executable artifacts in dry-run mode', async () => {
    const inputPath = path.join(testRoot, 'ae-ir.json');
    const outputDir = path.join(testRoot, 'generated-dry-run');
    writeFileSync(inputPath, JSON.stringify(validAeir, null, 2), 'utf8');

    const generator = new DeterministicCodeGenerator({
      inputPath,
      outputDir,
      target: 'react',
      enableDriftDetection: false,
      materialize: false,
    });

    const manifest = await generator.generate();

    expect(manifest.metadata.boundary).toMatchObject({
      kind: 'generated-code',
      source: 'ae-ir',
      materialized: false,
    });
    expect(manifest.metadata.boundary).not.toHaveProperty('approvalScope');
    expect(manifest.files).toHaveLength(2);
    expect(manifest.files[0]?.boundary.materialized).toBe(false);
    expect(existsSync(path.join(outputDir, 'components', 'ProductForm.tsx'))).toBe(false);
    expect(existsSync(path.join(outputDir, '.codegen-manifest.json'))).toBe(false);
  });

  it('rejects IR-derived entity names that could become path traversal components', async () => {
    const inputPath = path.join(testRoot, 'bad-ae-ir.json');
    const outputDir = path.join(testRoot, 'generated');
    writeFileSync(
      inputPath,
      JSON.stringify({
        ...validAeir,
        domain: [{ ...validAeir.domain[0], name: '../Escape' }],
      }),
      'utf8',
    );

    const generator = new DeterministicCodeGenerator({
      inputPath,
      outputDir,
      target: 'database',
      enableDriftDetection: false,
    });

    await expect(generator.generate()).rejects.toThrow('Invalid AE-IR domain entity name');
    expect(existsSync(path.join(testRoot, 'Escape.ts'))).toBe(false);
  });

  it('allows case-distinct identifiers that do not exactly match reserved words', async () => {
    const inputPath = path.join(testRoot, 'case-sensitive-ae-ir.json');
    const outputDir = path.join(testRoot, 'generated-case-sensitive');
    writeFileSync(
      inputPath,
      JSON.stringify({
        ...validAeir,
        domain: [{ ...validAeir.domain[0], name: 'Class' }],
        api: [],
      }),
      'utf8',
    );

    const generator = new DeterministicCodeGenerator({
      inputPath,
      outputDir,
      target: 'typescript',
      enableDriftDetection: false,
      materialize: false,
    });

    const manifest = await generator.generate();
    const typeFile = manifest.files.find((file) => file.filePath === 'types/domain.ts');

    expect(typeFile?.content).toContain('export interface Class');
  });

  it('rejects reserved TypeScript identifiers before generated modules are emitted', async () => {
    const inputPath = path.join(testRoot, 'reserved-ae-ir.json');
    const outputDir = path.join(testRoot, 'generated');
    writeFileSync(
      inputPath,
      JSON.stringify({
        ...validAeir,
        domain: [{ ...validAeir.domain[0], name: 'class' }],
      }),
      'utf8',
    );

    const generator = new DeterministicCodeGenerator({
      inputPath,
      outputDir,
      target: 'typescript',
      enableDriftDetection: false,
    });

    await expect(generator.generate()).rejects.toThrow('reserved identifier "class"');
    expect(existsSync(path.join(outputDir, 'types', 'domain.ts'))).toBe(false);
  });

  it('escapes repository-controlled API paths in generated handler comments', async () => {
    const inputPath = path.join(testRoot, 'api-ae-ir.json');
    const outputDir = path.join(testRoot, 'generated');
    writeFileSync(
      inputPath,
      JSON.stringify({
        ...validAeir,
        api: [{
          method: 'get',
          path: '/orders\n*/\nimport fs from "fs"',
          description: 'malicious comment payload',
        }],
      }),
      'utf8',
    );

    const generator = new DeterministicCodeGenerator({
      inputPath,
      outputDir,
      target: 'api',
      enableDriftDetection: false,
    });

    const manifest = await generator.generate();
    const handler = manifest.files[0]?.content ?? '';

    expect(handler).toContain('// Generated API handler for get /orders | *\\/ | import fs from "fs"');
    expect(handler).not.toContain('*/\n');
    expect(existsSync(path.join(outputDir, 'handlers', '_orders____import_fs_from__fs__get.ts'))).toBe(true);
  });
});
