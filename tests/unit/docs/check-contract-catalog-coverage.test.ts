import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';

import {
  checkCatalogCoverage,
  listSchemas,
  parseArgs,
  run,
} from '../../../scripts/docs/check-contract-catalog-coverage.mjs';

describe('check-contract-catalog-coverage', () => {
  it('parses CLI options', () => {
    const options = parseArgs([
      'node',
      'check-contract-catalog-coverage.mjs',
      '--root',
      '/tmp/repo',
      '--catalog',
      'docs/reference/CATALOG.md',
      '--schema-dir',
      'schemas',
    ]);
    expect(options).toEqual({
      rootDir: path.resolve('/tmp/repo'),
      catalogPath: 'docs/reference/CATALOG.md',
      schemaDir: 'schemas',
      format: 'text',
      unknown: [],
      help: false,
    });
  });

  it('collects unknown CLI options instead of throwing', () => {
    const options = parseArgs([
      'node',
      'check-contract-catalog-coverage.mjs',
      '--bogus',
      '--root',
    ]);
    expect(options.unknown).toEqual(['--bogus', '--root']);
  });

  it('lists schema files in lexical order', () => {
    const root = mkdtempSync(path.join(os.tmpdir(), 'ae-contract-catalog-'));
    try {
      mkdirSync(path.join(root, 'schema'), { recursive: true });
      writeFileSync(path.join(root, 'schema', 'z.schema.json'), '{}\n', 'utf8');
      writeFileSync(path.join(root, 'schema', 'a.schema.json'), '{}\n', 'utf8');
      expect(listSchemas(root, 'schema')).toEqual([
        'schema/a.schema.json',
        'schema/z.schema.json',
      ]);
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });

  it('checks catalog coverage for schema list', () => {
    const root = mkdtempSync(path.join(os.tmpdir(), 'ae-contract-catalog-'));
    try {
      mkdirSync(path.join(root, 'schema'), { recursive: true });
      mkdirSync(path.join(root, 'docs', 'reference'), { recursive: true });
      writeFileSync(path.join(root, 'schema', 'a.schema.json'), '{}\n', 'utf8');
      writeFileSync(path.join(root, 'schema', 'b.schema.json'), '{}\n', 'utf8');
      writeFileSync(
        path.join(root, 'docs', 'reference', 'CONTRACT-CATALOG.md'),
        [
          '# Contract Catalog',
          '',
          '- `schema/a.schema.json`',
        ].join('\n'),
        'utf8',
      );

      const failResult = checkCatalogCoverage({
        rootDir: root,
        catalogPath: 'docs/reference/CONTRACT-CATALOG.md',
        schemaDir: 'schema',
      });
      expect(failResult.ok).toBe(false);
      expect(failResult.missingInCatalog).toEqual(['schema/b.schema.json']);

      writeFileSync(
        path.join(root, 'docs', 'reference', 'CONTRACT-CATALOG.md'),
        [
          '# Contract Catalog',
          '',
          '- `schema/a.schema.json`',
          '- `schema/b.schema.json`',
        ].join('\n'),
        'utf8',
      );

      const okResult = checkCatalogCoverage({
        rootDir: root,
        catalogPath: 'docs/reference/CONTRACT-CATALOG.md',
        schemaDir: 'schema',
      });
      expect(okResult.ok).toBe(true);
      expect(okResult.missingInCatalog).toEqual([]);
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });

  it('returns exit code 2 when unknown options are provided', () => {
    const exitCode = run([
      'node',
      'check-contract-catalog-coverage.mjs',
      '--bogus',
    ]);
    expect(exitCode).toBe(2);
  });
});
