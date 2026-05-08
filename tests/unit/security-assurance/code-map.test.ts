import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { generateSecurityCodeMap } from '../../../src/security/assurance/code-map.js';

const claimsPath = 'fixtures/security-assurance/sample.security-claims.json';
const scopePath = 'fixtures/security-assurance/sample.security-audit-scope.json';
const targetPath = 'fixtures/security-assurance/code-map-target';
const symbolIndexPath = 'fixtures/security-assurance/sample.symbol-index.json';
const generatedAt = '2026-05-07T00:00:00.000Z';
const tsxBin = resolve('node_modules/.bin/tsx');

const readJson = <T>(path: string): T => JSON.parse(readFileSync(path, 'utf8')) as T;

const writeJson = (filePath: string, value: unknown) => {
  writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
};

describe('security code-map producer', () => {
  it('maps security claims to schema-valid candidate source locations', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-'));
    try {
      const result = await generateSecurityCodeMap(claimsPath, scopePath, targetPath, outDir, { generatedAt });

      expect(result.codeMap).toEqual(
        expect.objectContaining({
          schemaVersion: 'security-code-map/v1',
          generatedAt,
          summary: expect.objectContaining({
            totalClaims: 1,
            mappedClaims: 1,
            totalCandidateLocations: 1,
          }),
        }),
      );
      expect(result.codeMap.mappings[0]).toEqual(
        expect.objectContaining({
          claimId: 'SEC-CLAIM-001',
          coverage: 'partial',
          candidateLocations: [
            expect.objectContaining({
              path: 'src/cache.ts',
              symbol: 'buildCacheKey',
              startLine: 7,
              matchedTerms: expect.arrayContaining(['cache', 'key', 'verification']),
            }),
          ],
        }),
      );
      expect(result.warnings).toHaveLength(0);
      expect(readJson<{ schemaVersion: string }>(join(outDir, 'security-code-map.json')).schemaVersion).toBe('security-code-map/v1');
      expect(readFileSync(join(outDir, 'security-code-map.md'), 'utf8')).toContain('Security code-map summary');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('exposes mapping through ae security map-code', () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-cli-'));
    try {
      const result = spawnSync(
        tsxBin,
        [
          'src/cli/index.ts',
          'security',
          'map-code',
          '--claims',
          claimsPath,
          '--scope',
          scopePath,
          '--target',
          targetPath,
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
      expect(result.stdout).toContain('Security code-map generation completed');
      expect(result.stdout).toContain('Mapped claims: 1');
      expect(readJson<{ mappings: unknown[] }>(join(outDir, 'security-code-map.json')).mappings).toHaveLength(1);
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('uses optional symbol-index input before keyword source scanning', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-symbol-index-'));
    try {
      const result = await generateSecurityCodeMap(claimsPath, scopePath, targetPath, outDir, {
        generatedAt,
        symbolIndexPath,
      });

      expect(result.codeMap.summary.symbolIndex).toEqual({
        used: true,
        input: symbolIndexPath,
        totalSymbols: 1,
        inScopeSymbols: 1,
        matchedSymbols: 1,
        fallbackClaims: 0,
      });
      expect(result.codeMap.provenance.symbolIndex).toBe(symbolIndexPath);
      expect(result.codeMap.mappings[0]?.candidateLocations[0]).toEqual(
        expect.objectContaining({
          path: 'src/cache.ts',
          symbol: 'buildCacheKey',
          startLine: 7,
          endLine: 15,
          reason: expect.stringContaining('symbol-index entry SYM-001'),
          matchedTerms: expect.arrayContaining(['attacker', 'cache', 'controlled', 'key', 'verification']),
        }),
      );
      expect(result.warnings).toHaveLength(0);
      expect(readFileSync(join(outDir, 'security-code-map.md'), 'utf8')).toContain('Symbol index: fixtures/security-assurance/sample.symbol-index.json');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('exposes optional symbol-index mapping through ae security map-code', () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-cli-symbol-index-'));
    try {
      const result = spawnSync(
        tsxBin,
        [
          'src/cli/index.ts',
          'security',
          'map-code',
          '--claims',
          claimsPath,
          '--scope',
          scopePath,
          '--target',
          targetPath,
          '--symbol-index',
          symbolIndexPath,
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
      expect(result.stdout).toContain('Security code-map generation completed');
      expect(result.stdout).toContain('Symbol index: fixtures/security-assurance/sample.symbol-index.json');
      expect(readJson<{ summary: { symbolIndex?: { fallbackClaims: number } } }>(join(outDir, 'security-code-map.json')).summary.symbolIndex?.fallbackClaims).toBe(0);
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('respects out-of-scope globs during candidate collection', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-code-map-scope-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-scope-out-'));
    try {
      mkdirSync(join(fixtureDir, 'src'), { recursive: true });
      mkdirSync(join(fixtureDir, 'tests'), { recursive: true });
      writeFileSync(
        join(fixtureDir, 'src/cache.ts'),
        [
          'export function buildCacheKey(): string {',
          "  return ['cache', 'key', 'verification'].join(':');",
          '}',
          '',
        ].join('\n'),
        'utf8',
      );
      writeFileSync(
        join(fixtureDir, 'tests/cache.test.ts'),
        [
          'export function matchingTestOnly(): string {',
          "  return ['cache', 'key', 'verification', 'attacker'].join(':');",
          '}',
          '',
        ].join('\n'),
        'utf8',
      );
      const localScopePath = join(fixtureDir, 'scope.json');
      writeJson(localScopePath, {
        schemaVersion: 'security-audit-scope/v1',
        generatedAt,
        target: { repository: 'fixture/repo', commit: 'HEAD' },
        inScope: ['**/*.ts'],
        outOfScope: ['tests/**'],
        trustBoundaries: [{ id: 'TB-001', name: 'fixture', entryPoints: ['api'], attackerControlled: true }],
      });

      const result = await generateSecurityCodeMap(claimsPath, localScopePath, fixtureDir, outDir, { generatedAt });
      const paths = result.codeMap.mappings.flatMap((mapping) => mapping.candidateLocations.map((location) => location.path));

      expect(paths).toContain('src/cache.ts');
      expect(paths).not.toContain('tests/cache.test.ts');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('ignores in-scope globs that escape the target root', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-code-map-escape-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-escape-out-'));
    try {
      mkdirSync(join(fixtureDir, 'target', 'src'), { recursive: true });
      writeFileSync(
        join(fixtureDir, 'outside.ts'),
        'export function outsideCacheKey(): string { return \"cache key verification attacker\"; }\n',
        'utf8',
      );
      writeFileSync(
        join(fixtureDir, 'target', 'src', 'cache.ts'),
        'export function insideCacheKey(): string { return \"cache key verification\"; }\n',
        'utf8',
      );
      const localScopePath = join(fixtureDir, 'scope.json');
      writeJson(localScopePath, {
        schemaVersion: 'security-audit-scope/v1',
        generatedAt,
        target: { repository: 'fixture/repo', commit: 'HEAD' },
        inScope: ['../*.ts', 'src/**/*.ts'],
        outOfScope: [],
        trustBoundaries: [{ id: 'TB-001', name: 'fixture', entryPoints: ['api'], attackerControlled: true }],
      });

      const result = await generateSecurityCodeMap(claimsPath, localScopePath, join(fixtureDir, 'target'), outDir, { generatedAt });
      const paths = result.codeMap.mappings.flatMap((mapping) => mapping.candidateLocations.map((location) => location.path));

      expect(paths).toEqual(['src/cache.ts']);
      expect(result.codeMap.warnings).toEqual([
        expect.objectContaining({
          code: 'unsafe-glob-pattern',
          path: '/scope/inScope/0',
        }),
      ]);
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('filters symbol-index paths through the scoped target file set and falls back to keyword scanning', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-code-map-symbol-index-scope-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-symbol-index-scope-out-'));
    try {
      mkdirSync(join(fixtureDir, 'src'), { recursive: true });
      mkdirSync(join(fixtureDir, 'tests'), { recursive: true });
      writeFileSync(
        join(fixtureDir, 'src/cache.ts'),
        [
          'export function buildCacheKey(): string {',
          "  return ['cache', 'key', 'verification'].join(':');",
          '}',
          '',
        ].join('\n'),
        'utf8',
      );
      writeFileSync(
        join(fixtureDir, 'tests/cache.test.ts'),
        [
          'export function testOnlyCacheKey(): string {',
          "  return ['cache', 'key', 'verification', 'attacker'].join(':');",
          '}',
          '',
        ].join('\n'),
        'utf8',
      );
      const localScopePath = join(fixtureDir, 'scope.json');
      const localSymbolIndexPath = join(fixtureDir, 'symbol-index.json');
      writeJson(localScopePath, {
        schemaVersion: 'security-audit-scope/v1',
        generatedAt,
        target: { repository: 'fixture/repo', commit: 'HEAD' },
        inScope: ['src/**/*.ts'],
        outOfScope: ['tests/**'],
        trustBoundaries: [{ id: 'TB-001', name: 'fixture', entryPoints: ['api'], attackerControlled: true }],
      });
      writeJson(localSymbolIndexPath, {
        schemaVersion: 'symbol-index/v1',
        generatedAt,
        symbols: [
          {
            id: 'SYM-OUT-001',
            language: 'typescript',
            kind: 'function',
            name: 'testOnlyCacheKey',
            path: 'tests/cache.test.ts',
            startLine: 1,
            endLine: 3,
            tags: ['cache', 'key', 'verification', 'attacker'],
          },
        ],
        summary: { totalSymbols: 1, byLanguage: { typescript: 1 } },
      });

      const result = await generateSecurityCodeMap(claimsPath, localScopePath, fixtureDir, outDir, {
        generatedAt,
        symbolIndexPath: localSymbolIndexPath,
      });
      const mapping = result.codeMap.mappings[0];

      expect(result.codeMap.summary.symbolIndex).toEqual(
        expect.objectContaining({
          totalSymbols: 1,
          inScopeSymbols: 0,
          matchedSymbols: 0,
          fallbackClaims: 1,
        }),
      );
      expect(result.codeMap.warnings).toEqual([
        expect.objectContaining({
          code: 'symbol-index-out-of-scope',
          path: '/symbolIndex/symbols/0/path',
        }),
      ]);
      expect(mapping?.warnings).toEqual([
        expect.objectContaining({
          code: 'symbol-index-no-match-fallback',
          source: expect.stringContaining('symbol-index.json'),
        }),
      ]);
      expect(mapping?.candidateLocations.map((location) => location.path)).toEqual(['src/cache.ts']);
      expect(mapping?.candidateLocations[0]?.reason).not.toContain('symbol-index entry');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('rejects symbol-index ranges beyond the matched source file and falls back to keyword scanning', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-code-map-symbol-index-bounds-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-symbol-index-bounds-out-'));
    try {
      mkdirSync(join(fixtureDir, 'src'), { recursive: true });
      writeFileSync(
        join(fixtureDir, 'src/cache.ts'),
        [
          'export function buildCacheKey(): string {',
          "  return ['cache', 'key', 'verification'].join(':');",
          '}',
          '',
        ].join('\n'),
        'utf8',
      );
      const localScopePath = join(fixtureDir, 'scope.json');
      const localSymbolIndexPath = join(fixtureDir, 'symbol-index.json');
      writeJson(localScopePath, {
        schemaVersion: 'security-audit-scope/v1',
        generatedAt,
        target: { repository: 'fixture/repo', commit: 'HEAD' },
        inScope: ['src/**/*.ts'],
        outOfScope: [],
        trustBoundaries: [{ id: 'TB-001', name: 'fixture', entryPoints: ['api'], attackerControlled: true }],
      });
      writeJson(localSymbolIndexPath, {
        schemaVersion: 'symbol-index/v1',
        generatedAt,
        symbols: [
          {
            id: 'SYM-OOB-001',
            language: 'typescript',
            kind: 'function',
            name: 'buildCacheKey',
            path: 'src/cache.ts',
            startLine: 100,
            endLine: 120,
            tags: ['cache', 'key', 'verification'],
          },
        ],
        summary: { totalSymbols: 1, byLanguage: { typescript: 1 } },
      });

      const result = await generateSecurityCodeMap(claimsPath, localScopePath, fixtureDir, outDir, {
        generatedAt,
        symbolIndexPath: localSymbolIndexPath,
      });

      expect(result.codeMap.warnings).toEqual([
        expect.objectContaining({
          code: 'symbol-range-out-of-bounds',
          path: '/symbolIndex/symbols/0/endLine',
        }),
      ]);
      expect(result.codeMap.summary.symbolIndex).toEqual(
        expect.objectContaining({
          inScopeSymbols: 0,
          matchedSymbols: 0,
          fallbackClaims: 1,
        }),
      );
      expect(result.codeMap.mappings[0]?.candidateLocations).toEqual([
        expect.objectContaining({
          path: 'src/cache.ts',
          startLine: 1,
          endLine: 4,
        }),
      ]);
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('keeps symbol-index parser requirements aligned with the schema when validation is disabled', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-code-map-symbol-index-invalid-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-symbol-index-invalid-out-'));
    try {
      mkdirSync(join(fixtureDir, 'src'), { recursive: true });
      writeFileSync(join(fixtureDir, 'src/cache.ts'), 'export function buildCacheKey(): string { return \"cache key\"; }\n', 'utf8');
      const localScopePath = join(fixtureDir, 'scope.json');
      const localSymbolIndexPath = join(fixtureDir, 'symbol-index.json');
      writeJson(localScopePath, {
        schemaVersion: 'security-audit-scope/v1',
        generatedAt,
        target: { repository: 'fixture/repo', commit: 'HEAD' },
        inScope: ['src/**/*.ts'],
        outOfScope: [],
        trustBoundaries: [{ id: 'TB-001', name: 'fixture', entryPoints: ['api'], attackerControlled: true }],
      });
      writeJson(localSymbolIndexPath, {
        schemaVersion: 'symbol-index/v1',
        generatedAt,
        symbols: [
          {
            id: 'SYM-MISSING-KIND',
            language: 'typescript',
            name: 'buildCacheKey',
            path: 'src/cache.ts',
            startLine: 1,
            endLine: 1,
          },
        ],
        summary: { totalSymbols: 1, byLanguage: { typescript: 1 } },
      });

      await expect(generateSecurityCodeMap(claimsPath, localScopePath, fixtureDir, outDir, {
        generatedAt,
        symbolIndexPath: localSymbolIndexPath,
        validate: false,
      })).rejects.toThrow('must have a non-empty kind');
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('keeps claims without candidates as warning-only mappings', async () => {
    const fixtureDir = mkdtempSync(join(tmpdir(), 'ae-code-map-none-'));
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-none-out-'));
    try {
      mkdirSync(join(fixtureDir, 'src'), { recursive: true });
      writeFileSync(join(fixtureDir, 'src/unrelated.ts'), 'export const health = "ok";\n', 'utf8');
      const localClaimsPath = join(fixtureDir, 'claims.json');
      const localScopePath = join(fixtureDir, 'scope.json');
      writeJson(localClaimsPath, {
        schemaVersion: 'security-claim/v1',
        generatedAt,
        claims: [
          {
            id: 'SEC-CLAIM-NONE',
            type: 'invariant',
            statement: 'Quantum banana zebra invariant must be preserved.',
            sourceRefs: [{ kind: 'spec', uri: 'spec/none.md' }],
            criticality: 'medium',
            targetLevel: 'A2',
            threatTags: { stride: ['Tampering'], cwe: ['CWE-20'] },
            trustBoundary: { entryPoints: ['api'], attackerControlled: true },
            requiredLanes: ['spec'],
            provenance: { origin: 'manual', generator: 'test' },
          },
        ],
        summary: { totalClaims: 1, byCriticality: { low: 0, medium: 1, high: 0, critical: 0 } },
      });
      writeJson(localScopePath, {
        schemaVersion: 'security-audit-scope/v1',
        generatedAt,
        target: { repository: 'fixture/repo', commit: 'HEAD' },
        inScope: ['src/**/*.ts'],
        outOfScope: [],
        trustBoundaries: [{ id: 'TB-001', name: 'fixture', entryPoints: ['api'], attackerControlled: true }],
      });

      const result = await generateSecurityCodeMap(localClaimsPath, localScopePath, fixtureDir, outDir, { generatedAt });
      expect(result.codeMap.mappings[0]).toEqual(
        expect.objectContaining({
          claimId: 'SEC-CLAIM-NONE',
          coverage: 'none',
          candidateLocations: [],
          warnings: [expect.objectContaining({ code: 'no-candidate-location' })],
        }),
      );
      expect(result.codeMap.summary.totalWarnings).toBe(1);
      expect(result.warnings).toEqual([expect.objectContaining({ code: 'no-candidate-location' })]);
    } finally {
      rmSync(fixtureDir, { recursive: true, force: true });
      rmSync(outDir, { recursive: true, force: true });
    }
  });

  it('supports an explicit JSON output path with a Markdown summary sibling', async () => {
    const outDir = mkdtempSync(join(tmpdir(), 'ae-code-map-file-out-'));
    const codeMapPath = join(outDir, 'custom-security-code-map.json');
    try {
      const result = await generateSecurityCodeMap(claimsPath, scopePath, targetPath, codeMapPath, { generatedAt });
      expect(result.outputPaths.codeMap.endsWith('custom-security-code-map.json')).toBe(true);
      expect(result.outputPaths.summaryMarkdown.endsWith('custom-security-code-map.md')).toBe(true);
      expect(readJson<{ mappings: unknown[] }>(codeMapPath).mappings).toHaveLength(1);
      expect(readFileSync(join(outDir, 'custom-security-code-map.md'), 'utf8')).toContain('Candidate locations: 1');
    } finally {
      rmSync(outDir, { recursive: true, force: true });
    }
  });
});
