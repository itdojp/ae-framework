import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { describe, expect, it } from 'vitest';
import {
  aggregateLanes,
  buildArtifactMetadata,
  evaluatePolicyGate,
  listCuratedSchemas,
  parseProfile,
  renderReviewSurface,
  validateProfile,
  validateWithSchema,
} from '../src/index.js';

const testDir = dirname(fileURLToPath(import.meta.url));
const repoRoot = resolve(testDir, '../../..');
const minimalProfileText = readFileSync(resolve(repoRoot, 'profiles/minimal.yaml'), 'utf8');
const releasePolicyText = readFileSync(resolve(repoRoot, 'policy/release-policy.yml'), 'utf8');

describe('@ae-framework/core', () => {
  it('validates the minimal deploy-time profile and curated schema list', () => {
    const profileValidation = validateProfile(minimalProfileText);
    expect(profileValidation, JSON.stringify(profileValidation.errors)).toMatchObject({ ok: true, errors: [] });

    const schemaNames = listCuratedSchemas().map((schema) => schema.name);
    expect(schemaNames).toContain('assurance-profile.schema.json');
    expect(schemaNames).toContain('assurance-summary.schema.json');
    expect(schemaNames).toContain('policy-gate-summary-v1.schema.json');
  });

  it('keeps packaged curated schemas synchronized with the repository contracts', () => {
    for (const schema of listCuratedSchemas()) {
      const packagedSchema = JSON.parse(readFileSync(resolve(repoRoot, 'packages/core', schema.path), 'utf8'));
      const rootSchema = JSON.parse(readFileSync(resolve(repoRoot, 'schema', schema.name), 'utf8'));
      expect(packagedSchema, schema.name).toEqual(rootSchema);
    }
  });

  it('builds and validates artifact metadata and a minimal envelope', () => {
    const metadata = buildArtifactMetadata({
      now: '2026-07-04T00:00:00.000Z',
      env: { CI: 'true' },
      gitCommit: '1ee3bcee',
      branch: 'feat/3617-core-package',
      runnerName: 'core-test-runner',
      runnerOs: 'Linux',
      runnerArch: 'X64',
      toolVersions: { pnpm: '10.0.0' },
    });

    expect(validateWithSchema('artifact-metadata', metadata)).toMatchObject({ ok: true, errors: [] });
    expect(metadata.toolVersions).toHaveProperty('node');
    expect(metadata.toolVersions).toHaveProperty('pnpm', '10.0.0');

    const envelope = {
      schemaVersion: '1.0.0',
      source: '@ae-framework/core',
      generatedAt: metadata.generatedAtUtc,
      traceCorrelation: { runId: 'core-api-test' },
      summary: { profile: 'minimal', status: 'observed' },
    };
    expect(validateWithSchema('envelope', envelope)).toMatchObject({ ok: true, errors: [] });
  });

  it('aggregates profile evidence into a schema-valid assurance summary', () => {
    const profile = parseProfile(minimalProfileText);
    const summary = aggregateLanes({
      profile,
      generatedAt: '2026-07-04T00:00:00.000Z',
      assuranceProfilePath: 'profiles/minimal.yaml',
      evidence: [
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'spec',
          kind: 'schema',
          sourceKind: 'spec-derived',
          origin: 'profile-contract',
          generatorLineage: 'profile-contract/v1',
        },
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'behavior',
          kind: 'integration',
          sourceKind: 'source-derived',
          origin: 'core-api-test',
          generatorLineage: 'vitest',
        },
      ],
    });

    expect(summary.summary).toMatchObject({ claimCount: 1, satisfiedClaims: 1, warningCount: 0 });
    const validation = validateWithSchema('assurance-summary', summary);
    expect(validation, JSON.stringify(validation.errors)).toMatchObject({ ok: true, errors: [] });
  });

  it('evaluates YAML release-policy required evidence without OPA', () => {
    const blocked = evaluatePolicyGate({
      policy: releasePolicyText,
      evidenceIds: ['postDeployVerify'],
      generatedAt: '2026-07-04T00:00:00.000Z',
      repository: 'itdojp/ae-framework',
      prNumber: 3617,
      inputPath: 'policy/release-policy.yml',
    });
    expect(blocked).toMatchObject({ result: 'block', missingEvidence: ['qualityGates'] });

    const passed = evaluatePolicyGate({
      policy: releasePolicyText,
      evidenceIds: ['postDeployVerify', 'qualityGates'],
      generatedAt: '2026-07-04T00:00:00.000Z',
    });
    expect(passed).toMatchObject({ result: 'pass', missingEvidence: [] });
  });

  it('renders a review surface from aggregate and policy results', () => {
    const profile = parseProfile(minimalProfileText);
    const summary = aggregateLanes({
      profile,
      generatedAt: '2026-07-04T00:00:00.000Z',
      evidence: [],
    });
    const decision = evaluatePolicyGate({
      policy: releasePolicyText,
      evidenceIds: [],
      generatedAt: '2026-07-04T00:00:00.000Z',
      mode: 'report-only',
    });

    const markdown = renderReviewSurface(summary, { policyDecision: decision });
    expect(markdown).toContain('# PR Assurance Review Surface');
    expect(markdown).toContain('minimal-assurance-gate-reviewable');
    expect(markdown).toContain('Policy decision: report-only');
  });

  it('keeps runtime dependencies bounded and rejects root src imports', () => {
    const packageJson = JSON.parse(readFileSync(resolve(repoRoot, 'packages/core/package.json'), 'utf8')) as {
      dependencies?: Record<string, string>;
    };
    const dependencyNames = Object.keys(packageJson.dependencies ?? {});
    expect(dependencyNames).toEqual(['ajv', 'ajv-formats', 'yaml']);
    expect(dependencyNames.length).toBeLessThanOrEqual(5);

    const output = execFileSync('node', ['packages/core/scripts/check-no-src-imports.mjs'], {
      cwd: repoRoot,
      encoding: 'utf8',
    });
    expect(output).toContain('No root src/** imports found');
  });
});
