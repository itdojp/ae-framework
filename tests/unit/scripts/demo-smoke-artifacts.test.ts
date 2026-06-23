import { describe, expect, it } from 'vitest';
import { writeFileSync, mkdirSync, rmSync } from 'node:fs';
import { resolve, dirname } from 'node:path';
import { randomUUID } from 'node:crypto';
import { checkDemoSmokeArtifacts, parseArgs } from '../../../scripts/demo/check-demo-smoke-artifacts.mjs';

const repoRoot = resolve('.');

describe('demo smoke artifact checker', () => {
  it('accepts schema-backed JSON and non-empty text artifacts', () => {
    const report = checkDemoSmokeArtifacts({
      repoRoot,
      outputRoot: 'examples/assurance-control-plane/scope-drift-demo',
      artifacts: [
        {
          demo: 'fixture',
          type: 'json',
          relativePath: 'expected/producer-normalization-summary.json',
          schemaPath: 'schema/producer-normalization-summary.schema.json',
          customValidate: null,
        },
        {
          demo: 'fixture',
          type: 'text',
          relativePath: 'README.md',
          schemaPath: null,
          customValidate: null,
        },
      ],
    });

    expect(report.ok).toBe(true);
    expect(report.failures).toEqual([]);
    expect(report.checked).toHaveLength(2);
  });

  it('reports missing artifacts with an actionable failure category', () => {
    const report = checkDemoSmokeArtifacts({
      repoRoot,
      outputRoot: 'artifacts',
      artifacts: [
        {
          demo: 'missing',
          type: 'json',
          relativePath: `artifacts/missing-demo-${randomUUID()}.json`,
          schemaPath: 'schema/assurance-summary.schema.json',
          customValidate: null,
        },
      ],
    });

    expect(report.ok).toBe(false);
    expect(report.failures).toHaveLength(1);
    expect(report.failures[0].reason).toContain('[artifact missing]');
  });

  it('reports JSON parsing and schema validation failures distinctly', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `demo-smoke-check-test-${randomUUID()}`);
    const invalidJsonPath = resolve(outputRoot, 'invalid-json.json');
    const invalidSchemaPath = resolve(outputRoot, 'invalid-schema.json');

    try {
      mkdirSync(dirname(invalidJsonPath), { recursive: true });
      writeFileSync(invalidJsonPath, '{', 'utf8');
      writeFileSync(invalidSchemaPath, `${JSON.stringify({ schemaVersion: 'wrong' })}\n`, 'utf8');

      const report = checkDemoSmokeArtifacts({
        repoRoot,
        outputRoot,
        artifacts: [
          {
            demo: 'invalid-json',
            type: 'json',
            relativePath: 'invalid-json.json',
            schemaPath: 'schema/assurance-summary.schema.json',
            customValidate: null,
          },
          {
            demo: 'invalid-schema',
            type: 'json',
            relativePath: 'invalid-schema.json',
            schemaPath: 'schema/assurance-summary.schema.json',
            customValidate: null,
          },
        ],
      });

      expect(report.ok).toBe(false);
      expect(report.failures.map((failure) => failure.reason)).toEqual([
        expect.stringContaining('[json invalid]'),
        expect.stringContaining('[schema invalid]'),
      ]);
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('parses an optional output root for CI and local runs', () => {
    expect(parseArgs(['--output-root', 'artifacts/demo-smoke'])).toMatchObject({
      outputRoot: 'artifacts/demo-smoke',
      help: false,
    });
    expect(parseArgs(['--help'])).toMatchObject({ help: true });
  });
});
