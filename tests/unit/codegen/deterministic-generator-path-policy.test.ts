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
    expect(existsSync(path.join(outputDir, 'components', 'ProductForm.tsx'))).toBe(true);
    expect(existsSync(path.join(outputDir, '.codegen-manifest.json'))).toBe(true);
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
});
