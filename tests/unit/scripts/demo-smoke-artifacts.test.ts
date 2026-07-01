import { describe, expect, it } from 'vitest';
import { writeFileSync, mkdirSync, rmSync } from 'node:fs';
import { resolve, dirname } from 'node:path';
import { randomUUID } from 'node:crypto';
import {
  AGENT_ASSURANCE_DEMO_ARTIFACTS,
  artifactsForDemo,
  checkDemoSmokeArtifacts,
  knownDemoNames,
  parseArgs,
} from '../../../scripts/demo/check-demo-smoke-artifacts.mjs';

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
      demo: null,
      help: false,
    });
    expect(parseArgs(['--demo', 'agent-assurance'])).toMatchObject({
      outputRoot: 'artifacts',
      demo: 'agent-assurance',
      help: false,
    });
    expect(() => parseArgs(['--demo='])).toThrow('--demo requires a non-empty demo name');
    expect(parseArgs(['--help'])).toMatchObject({ help: true });
  });

  it('can narrow checks to the first-run agent-assurance artifact set', () => {
    const selected = artifactsForDemo('agent-assurance');

    expect(knownDemoNames()).toEqual(['agent-assurance', 'high-risk-escalation', 'scope-drift']);
    expect(selected).toEqual(AGENT_ASSURANCE_DEMO_ARTIFACTS);
    expect(selected).toHaveLength(8);
    expect(selected.map((artifact) => artifact.demo)).toEqual(Array(8).fill('agent-assurance'));
    expect(selected.map((artifact) => artifact.relativePath)).toContain(
      'review/agent-assurance-demo/assurance-review.md',
    );
  });

  it('rejects unknown demo names before checking the filesystem', () => {
    expect(() => artifactsForDemo('unknown-demo')).toThrow(
      'unknown demo: unknown-demo; expected one of: agent-assurance, high-risk-escalation, scope-drift',
    );
  });
});
