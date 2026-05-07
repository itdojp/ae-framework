import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { extractSecurityClaimsFromSpec } from '../../../src/security/assurance/claim-extractor.js';

const inputSpec = 'fixtures/security-assurance/extract-claims/spec.md';
const generatedAt = '2026-05-07T00:00:00.000Z';
const tsxBin = resolve('node_modules/.bin/tsx');

const readJson = <T>(path: string): T => JSON.parse(readFileSync(path, 'utf8')) as T;

describe('security claim extractor', () => {
  it('extracts explicit SEC-CLAIM blocks into schema-valid security claims', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-claim-extract-'));
    try {
      const result = await extractSecurityClaimsFromSpec(inputSpec, outDir, { generatedAt });

      expect(result.claims).toEqual(
        expect.objectContaining({
          schemaVersion: 'security-claim/v1',
          generatedAt,
          summary: {
            totalClaims: 2,
            byCriticality: { low: 0, medium: 1, high: 1, critical: 0 },
          },
        }),
      );
      expect(result.claims.claims.map((claim) => claim.id)).toEqual(['SEC-CLAIM-101', 'SEC-CLAIM-002']);
      expect(result.claims.claims[0]).toEqual(
        expect.objectContaining({
          type: 'invariant',
          criticality: 'high',
          targetLevel: 'A2',
          statement: 'Cache key must include all attacker-controlled fields that affect the verification result.',
          threatTags: { stride: ['Tampering'], cwe: ['CWE-20'] },
          trustBoundary: expect.objectContaining({
            boundaryIds: ['TB-001'],
            entryPoints: ['api', 'p2p'],
            attackerControlled: true,
            dataClasses: ['verification-input'],
          }),
          requiredLanes: ['spec', 'adversarial', 'behavior'],
          provenance: expect.objectContaining({ origin: 'manual-block', generator: 'security-claim-extractor' }),
        }),
      );
      expect(result.claims.claims[1]).toEqual(
        expect.objectContaining({
          id: 'SEC-CLAIM-002',
          type: 'precondition',
          threatTags: { stride: ['Spoofing', 'Elevation of Privilege'], cwe: ['CWE-287', 'CWE-613'] },
        }),
      );
      expect(result.warnings).toHaveLength(0);
      expect(readJson<{ schemaVersion: string }>(join(outDir, 'security-claims.json')).schemaVersion).toBe('security-claim/v1');
      expect(readFileSync(join(outDir, 'security-claims.md'), 'utf8')).toContain('Security claim extraction summary');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('exposes extraction through ae security extract-claims', () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-claim-extract-cli-'));
    try {
      const result = spawnSync(
        tsxBin,
        [
          'src/cli/index.ts',
          'security',
          'extract-claims',
          '--spec',
          inputSpec,
          '--out',
          outDir,
          '--generated-at',
          generatedAt,
        ],
        {
          encoding: 'utf8',
          timeout: 60_000,
          env: {
            ...process.env,
            VITEST: '',
            NODE_ENV: 'production',
            AE_TEST_NO_EXIT: '0',
            DISABLE_TELEMETRY: 'true',
          },
        },
      );

      expect(result.status, `${result.stdout}\n${result.stderr}`).toBe(0);
      expect(result.stdout).toContain('Security claims extraction completed');
      expect(result.stdout).toContain('Claims: 2');
      expect(readJson<{ claims: unknown[] }>(join(outDir, 'security-claims.json')).claims).toHaveLength(2);
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('reports schema validation errors for invalid explicit claim fields', async () => {
    const specDir = mkdtempSync(join(tmpdir(), 'ae-claim-invalid-spec-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-claim-invalid-out-'));
    const specPath = join(specDir, 'invalid.md');
    try {
      writeFileSync(
        specPath,
        [
          '# Invalid claim fixture',
          '',
          'SEC-CLAIM:',
          'id: SEC-CLAIM-BAD',
          'type: vulnerability',
          'criticality: urgent',
          'statement: Invalid claim fields should surface through schema validation.',
          'stride: Tampering',
          'cwe: CWE-20',
          'entryPoints: api',
          '',
        ].join('\n'),
        'utf8',
      );

      await expect(extractSecurityClaimsFromSpec(specPath, outDir, { generatedAt })).rejects.toThrow(
        /Generated security claims failed schema validation/,
      );
    } finally {
      rmSync(specDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('preserves explicit canonical IDs and avoids generated ID collisions', async () => {
    const specDir = mkdtempSync(join(tmpdir(), 'ae-claim-collision-spec-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-claim-collision-out-'));
    const specPath = join(specDir, 'collision.md');
    try {
      writeFileSync(
        specPath,
        [
          '# Collision fixture',
          '',
          'SEC-CLAIM:',
          'type: invariant',
          'criticality: high',
          'statement: Generated claim must not reuse the later explicit SEC-CLAIM-001.',
          'stride: Tampering',
          'cwe: CWE-20',
          'entryPoints: api',
          '',
          'SEC-CLAIM:',
          'id: SEC-CLAIM-001',
          'type: invariant',
          'criticality: medium',
          'statement: Explicit claim keeps its canonical id.',
          'stride: Tampering',
          'cwe: CWE-20',
          'entryPoints: api',
          '',
        ].join('\n'),
        'utf8',
      );

      const result = await extractSecurityClaimsFromSpec(specPath, outDir, { generatedAt });
      expect(result.claims.claims.map((claim) => claim.id)).toEqual(['SEC-CLAIM-002', 'SEC-CLAIM-001']);
      expect(result.warnings).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ code: 'id-collision-normalized' }),
        ]),
      );
    } finally {
      rmSync(specDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('ignores SEC-CLAIM examples inside fenced Markdown code blocks', async () => {
    const specDir = mkdtempSync(join(tmpdir(), 'ae-claim-fenced-spec-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-claim-fenced-out-'));
    const specPath = join(specDir, 'fenced.md');
    try {
      writeFileSync(
        specPath,
        [
          '# Fenced example fixture',
          '',
          '```md',
          'SEC-CLAIM:',
          'id: SEC-CLAIM-EXAMPLE',
          'type: vulnerability',
          'criticality: urgent',
          'statement: This example must not be extracted.',
          '```',
          '',
          '## Actual claim',
          '',
          'SEC-CLAIM:',
          'id: SEC-CLAIM-ACTUAL',
          'type: invariant',
          'criticality: high',
          'statement: Only the real claim outside code fences is extracted.',
          'stride: Tampering',
          'cwe: CWE-20',
          'entryPoints: api',
          '',
        ].join('\n'),
        'utf8',
      );

      const result = await extractSecurityClaimsFromSpec(specPath, outDir, { generatedAt });
      expect(result.claims.claims.map((claim) => claim.id)).toEqual(['SEC-CLAIM-ACTUAL']);
      expect(result.claims.summary.totalClaims).toBe(1);
    } finally {
      rmSync(specDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('normalizes empty IDs and de-duplicates list fields before schema validation', async () => {
    const specDir = mkdtempSync(join(tmpdir(), 'ae-claim-list-spec-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-claim-list-out-'));
    const specPath = join(specDir, 'lists.md');
    try {
      writeFileSync(
        specPath,
        [
          '# List fixture',
          '',
          'SEC-CLAIM:',
          'id:   ',
          'type: invariant',
          'criticality: high',
          'statement: Duplicate list values are normalized before validation.',
          'stride: Tampering, Tampering',
          'cwe: CWE-20, CWE-20',
          'boundaryIds: TB-001, TB-001',
          'entryPoints: api, api',
          'dataClasses: token, token',
          'requiredLanes: spec, spec, behavior',
          '',
        ].join('\n'),
        'utf8',
      );

      const result = await extractSecurityClaimsFromSpec(specPath, outDir, { generatedAt });
      expect(result.claims.claims[0]).toEqual(
        expect.objectContaining({
          id: 'SEC-CLAIM-001',
          threatTags: { stride: ['Tampering'], cwe: ['CWE-20'] },
          trustBoundary: expect.objectContaining({
            boundaryIds: ['TB-001'],
            entryPoints: ['api'],
            dataClasses: ['token'],
          }),
          requiredLanes: ['spec', 'behavior'],
        }),
      );
      expect(result.warnings).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ code: 'empty-id-normalized', path: '/claims/0/id' }),
        ]),
      );
    } finally {
      rmSync(specDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('supports an explicit JSON output path with a Markdown summary sibling', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-claim-file-out-'));
    const claimsPath = join(outDir, 'custom-security-claims.json');
    try {
      const result = await extractSecurityClaimsFromSpec(inputSpec, claimsPath, { generatedAt });
      expect(result.outputPaths.claims.endsWith('custom-security-claims.json')).toBe(true);
      expect(result.outputPaths.summaryMarkdown.endsWith('custom-security-claims.md')).toBe(true);
      expect(readJson<{ claims: unknown[] }>(claimsPath).claims).toHaveLength(2);
      expect(readFileSync(join(outDir, 'custom-security-claims.md'), 'utf8')).toContain('Claims: 2');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });
});
