import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, expect, it } from 'vitest';

import { DEFAULT_RULES, validateArtifactsAjv } from '../../../scripts/ci/validate-artifacts-ajv.mjs';

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

  it('reports schema_missing as rule error without counting failed files', () => {
    withTempDir((rootDir) => {
      writeJson(path.join(rootDir, 'artifacts', 'sample.json'), { name: 'ok' });

      const result = validateArtifactsAjv({
        rootDir,
        strict: true,
        rules: [
          {
            id: 'missing-schema',
            schemaPath: 'schema/missing.schema.json',
            patterns: ['artifacts/sample.json'],
          },
        ],
      });

      expect(result.exitCode).toBe(1);
      expect(result.summary.totals.failedFiles).toBe(0);
      expect(result.summary.totals.schemaRuleErrors).toBe(1);
      expect(result.summary.rules[0]?.ruleError).toBe('schema_missing');
    });
  });

  it('reports invalid_json and fails in strict mode', () => {
    withTempDir((rootDir) => {
      writeJson(path.join(rootDir, 'schema', 'sample.schema.json'), {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: 'https://example.test/schema/sample.schema.json',
        type: 'object',
        properties: {
          name: { type: 'string' },
        },
      });
      const invalidJsonPath = path.join(rootDir, 'artifacts', 'broken.json');
      mkdirSync(path.dirname(invalidJsonPath), { recursive: true });
      writeFileSync(invalidJsonPath, '{"name":"ok",}\n');

      const result = validateArtifactsAjv({
        rootDir,
        strict: true,
        rules: [
          {
            id: 'invalid-json',
            schemaPath: 'schema/sample.schema.json',
            patterns: ['artifacts/broken.json'],
          },
        ],
      });

      expect(result.exitCode).toBe(1);
      expect(result.errors.some((error) => error.keyword === 'invalid_json')).toBe(true);
      expect(result.summary.totals.failedFiles).toBe(1);
    });
  });

  it('marks no-match rules as skipped without errors', () => {
    withTempDir((rootDir) => {
      writeJson(path.join(rootDir, 'schema', 'sample.schema.json'), {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: 'https://example.test/schema/sample.schema.json',
        type: 'object',
        properties: {
          name: { type: 'string' },
        },
      });

      const result = validateArtifactsAjv({
        rootDir,
        strict: true,
        rules: [
          {
            id: 'no-match',
            schemaPath: 'schema/sample.schema.json',
            patterns: ['artifacts/not-found-*.json'],
          },
        ],
      });

      expect(result.exitCode).toBe(0);
      expect(result.errors.length).toBe(0);
      expect(result.summary.rules[0]?.skipped).toBe(true);
      expect(result.summary.rules[0]?.skipReason).toBe('no files matched');
    });
  });

  it('requiredWhenStrict rule fails only in strict mode when files are missing', () => {
    withTempDir((rootDir) => {
      writeJson(path.join(rootDir, 'schema', 'required.schema.json'), {
        $schema: 'https://json-schema.org/draft/2020-12/schema',
        $id: 'https://example.test/schema/required.schema.json',
        type: 'object',
        properties: {
          ok: { type: 'boolean' },
        },
        additionalProperties: false,
      });

      const sharedRule = {
        id: 'required-strict-only',
        schemaPath: 'schema/required.schema.json',
        patterns: ['artifacts/required-target.json'],
        requiredWhenStrict: true,
      };

      const nonStrictResult = validateArtifactsAjv({
        rootDir,
        strict: false,
        rules: [sharedRule],
      });
      expect(nonStrictResult.exitCode).toBe(0);
      expect(nonStrictResult.errors.length).toBe(0);
      expect(nonStrictResult.summary.rules[0]?.skipped).toBe(true);
      expect(nonStrictResult.summary.rules[0]?.ruleError).toBeNull();

      const strictResult = validateArtifactsAjv({
        rootDir,
        strict: true,
        rules: [sharedRule],
      });
      expect(strictResult.exitCode).toBe(1);
      expect(strictResult.errors.some((error) => error.keyword === 'required_when_strict')).toBe(true);
      expect(strictResult.summary.rules[0]?.ruleError).toBe('required_when_strict');
      expect(strictResult.summary.rules[0]?.skipped).toBe(false);
    });
  });

  it('default rules include strict-required trace validation and trace envelope checks', () => {
    const traceValidationRule = DEFAULT_RULES.find((rule) => rule.id === 'trace-validation');
    expect(traceValidationRule).toBeDefined();
    expect(traceValidationRule?.requiredWhenStrict).toBe(true);
    expect(traceValidationRule?.schemaPath).toBe('schema/trace-validation.schema.json');

    const traceEnvelopeRule = DEFAULT_RULES.find((rule) => rule.id === 'trace-envelope');
    expect(traceEnvelopeRule).toBeDefined();
    expect(traceEnvelopeRule?.requiredWhenStrict).toBe(true);
    expect(traceEnvelopeRule?.patterns).toContain('artifacts/trace/report-envelope.json');

    const formalSummaryV2Rule = DEFAULT_RULES.find((rule) => rule.id === 'formal-summary-v2');
    expect(formalSummaryV2Rule).toBeDefined();
    expect(formalSummaryV2Rule?.schemaPath).toBe('schema/formal-summary-v2.schema.json');
    expect(formalSummaryV2Rule?.patterns).toContain('artifacts/formal/formal-summary-v2.json');

    const benchCompareRule = DEFAULT_RULES.find((rule) => rule.id === 'bench-compare');
    expect(benchCompareRule).toBeDefined();
    expect(benchCompareRule?.schemaPath).toBe('schema/bench-compare.schema.json');
    expect(benchCompareRule?.patterns).toContain('artifacts/bench-compare.json');
  });
});
