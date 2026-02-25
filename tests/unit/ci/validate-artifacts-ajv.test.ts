import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';

import { validateArtifactsAjv } from '../../../scripts/ci/validate-artifacts-ajv.mjs';

function withTempDir(fn: (dir: string) => void): void {
  const dir = mkdtempSync(path.join(tmpdir(), 'ae-validate-artifacts-ajv-'));
  try {
    fn(dir);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function writeJson(filePath: string, payload: unknown): void {
  mkdirSync(path.dirname(filePath), { recursive: true });
  writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`);
}

describe('validate-artifacts-ajv', () => {
  it('non-strict mode keeps exit code 0 and writes summary artifacts', () => {
    withTempDir((rootDir) => {
      writeJson(path.join(rootDir, 'schema', 'sample.schema.json'), {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: 'https://example.test/schema/sample.schema.json',
        type: 'object',
        required: ['name'],
        properties: {
          name: { type: 'string' },
        },
        additionalProperties: false,
      });
      writeJson(path.join(rootDir, 'artifacts', 'sample.json'), { invalid: true });

      const result = validateArtifactsAjv({
        rootDir,
        strict: false,
        outputDir: 'artifacts/schema-validation',
        rules: [
          {
            id: 'sample',
            schemaPath: 'schema/sample.schema.json',
            patterns: ['artifacts/sample.json'],
          },
        ],
      });

      expect(result.exitCode).toBe(0);
      expect(result.summary.totals.failedFiles).toBe(1);
      expect(result.errors.length).toBeGreaterThan(0);

      const summaryPath = path.join(rootDir, 'artifacts', 'schema-validation', 'summary.json');
      const errorsPath = path.join(rootDir, 'artifacts', 'schema-validation', 'errors.json');
      expect(JSON.parse(readFileSync(summaryPath, 'utf8')).totals.failedFiles).toBe(1);
      expect(JSON.parse(readFileSync(errorsPath, 'utf8')).errors.length).toBeGreaterThan(0);
    });
  });

  it('strict mode returns exit code 1 when validation errors exist', () => {
    withTempDir((rootDir) => {
      writeJson(path.join(rootDir, 'schema', 'sample.schema.json'), {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: 'https://example.test/schema/sample.schema.json',
        type: 'object',
        required: ['ok'],
        properties: {
          ok: { type: 'boolean' },
        },
        additionalProperties: false,
      });
      writeJson(path.join(rootDir, 'artifacts', 'sample.json'), { ok: 'yes' });

      const result = validateArtifactsAjv({
        rootDir,
        strict: true,
        rules: [
          {
            id: 'sample',
            schemaPath: 'schema/sample.schema.json',
            patterns: ['artifacts/sample.json'],
          },
        ],
      });

      expect(result.exitCode).toBe(1);
      expect(result.summary.totals.failedFiles).toBe(1);
      expect(result.errors.some((error) => error.instancePath === '/ok')).toBe(true);
    });
  });

  it('iterateArrayItems validates each element and reports index path', () => {
    withTempDir((rootDir) => {
      writeJson(path.join(rootDir, 'schema', 'item.schema.json'), {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: 'https://example.test/schema/item.schema.json',
        type: 'object',
        required: ['value'],
        properties: {
          value: { type: 'integer' },
        },
        additionalProperties: false,
      });
      writeJson(path.join(rootDir, 'artifacts', 'items.json'), [{ value: 1 }, { value: 'x' }]);

      const result = validateArtifactsAjv({
        rootDir,
        strict: true,
        rules: [
          {
            id: 'array-items',
            schemaPath: 'schema/item.schema.json',
            patterns: ['artifacts/items.json'],
            iterateArrayItems: true,
          },
        ],
      });

      expect(result.exitCode).toBe(1);
      expect(result.errors.some((error) => error.instancePath.startsWith('/1'))).toBe(true);
    });
  });
});
