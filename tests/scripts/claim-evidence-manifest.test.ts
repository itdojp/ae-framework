import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { validateClaimEvidenceManifestSemantics } from '../../scripts/ci/lib/claim-evidence-manifest-contract.mjs';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/assurance/build-claim-evidence-manifest.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

const runScript = (args: string[]) =>
  spawnSync('node', [scriptPath, ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
    timeout: 120_000,
  });

const writeJson = (targetPath: string, payload: unknown) => {
  writeFileSync(targetPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
};

const buildSchemaValidator = () => {
  const schema = JSON.parse(readFileSync(resolve(repoRoot, 'schema/claim-evidence-manifest.schema.json'), 'utf8'));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
};

describe.sequential('claim evidence manifest generator', () => {
  it('parses arguments and generates a schema-valid JSON plus Markdown manifest', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs([])).toMatchObject({
      assuranceSummary: 'artifacts/assurance/assurance-summary.json',
      securityClaims: 'artifacts/security/security-claims.json',
      securityFindings: 'artifacts/security/security-findings.json',
      securityReview: 'artifacts/security/security-review.json',
      outputJson: 'artifacts/assurance/claim-evidence-manifest.json',
      outputMd: 'artifacts/assurance/claim-evidence-manifest.md',
      validate: true,
    });
    expect(() => mod.parseArgs(['--assurance-summary'])).toThrow('--assurance-summary requires a value');
    expect(() => mod.parseArgs(['--change-package', 'a.json', '--change-package', 'b.json'])).toThrow(
      '--change-package can only be provided once',
    );

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-claim-evidence-manifest-'));
    const outputJson = join(sandbox, 'claim-evidence-manifest.json');
    const outputMd = join(sandbox, 'claim-evidence-manifest.md');

    try {
      const result = runScript([
        '--assurance-summary',
        'fixtures/assurance/sample.assurance-summary.json',
        '--change-package',
        'fixtures/change-package/sample.change-package-v2.json',
        '--quality-scorecard',
        'fixtures/quality/sample.quality-scorecard.json',
        '--generated-at',
        '2026-04-28T18:20:00.000Z',
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('[claim-evidence-manifest] wrote');

      const manifest = JSON.parse(readFileSync(outputJson, 'utf8'));
      const validate = buildSchemaValidator();
      expect(validate(manifest), JSON.stringify(validate.errors)).toBe(true);
      expect(validateClaimEvidenceManifestSemantics(manifest)).toEqual([]);
      expect(manifest).toMatchObject({
        schemaVersion: 'claim-evidence-manifest/v1',
        generatedAt: '2026-04-28T18:20:00.000Z',
        summary: {
          totalClaims: 2,
          fullySupported: 1,
          partiallySupported: 1,
          waived: 0,
          unresolved: 0,
        },
      });
      expect(manifest.sourceArtifacts).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ id: 'assurance-summary', present: true, required: true }),
          expect.objectContaining({ id: 'change-package-v2', present: true, schemaVersion: 'change-package/v2' }),
          expect.objectContaining({ id: 'quality-scorecard', present: true, schemaVersion: 'quality-scorecard/v1' }),
        ]),
      );

      const stockClaim = manifest.claims.find((claim: { id: string }) => claim.id === 'no-negative-stock');
      expect(stockClaim).toMatchObject({
        targetLevel: 'A2',
        achievedLevel: 'A2',
        status: 'satisfied',
      });
      expect(stockClaim.evidenceRefs).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ sourceArtifactId: 'assurance-summary', kind: 'behavior' }),
          expect.objectContaining({ sourceArtifactId: 'quality-scorecard', kind: 'quality' }),
        ]),
      );

      const balanceClaim = manifest.claims.find((claim: { id: string }) => claim.id === 'no-negative-balance');
      expect(balanceClaim).toMatchObject({
        targetLevel: 'A3',
        achievedLevel: 'A2',
        status: 'partial',
      });
      expect(balanceClaim.proofObligationRefs).toEqual([
        expect.objectContaining({ id: 'obl-1', status: 'discharged', method: 'tla' }),
      ]);
      expect(balanceClaim.missingEvidenceRefs.length).toBeGreaterThan(0);

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toContain('# Claim Evidence Manifest');
      expect(markdown).toContain('| no-negative-balance | n/a | high | A3 | A2 | partial |');
      expect(markdown).toContain('## Missing evidence');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('integrates security claims, findings, and three-gate reviews as report-only assurance evidence', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-claim-evidence-manifest-security-'));
    const securityReviewPath = join(sandbox, 'security-review-with-repeat.json');
    const outputJson = join(sandbox, 'claim-evidence-manifest.json');
    const outputMd = join(sandbox, 'claim-evidence-manifest.md');

    try {
      const securityReviewFixture = JSON.parse(
        readFileSync(resolve(repoRoot, 'fixtures/security-assurance/sample.security-review.json'), 'utf8'),
      );
      securityReviewFixture.reviews.push({
        ...securityReviewFixture.reviews[0],
        reviewer: 'human-security-reviewer',
        reviewerNotes: ['Human reviewer rechecked the same finding and kept the review state.'],
      });
      writeJson(securityReviewPath, securityReviewFixture);

      const result = runScript([
        '--assurance-summary',
        'fixtures/assurance/sample.assurance-summary.json',
        '--security-claims',
        'fixtures/security-assurance/sample.security-claims.json',
        '--security-findings',
        'fixtures/security-assurance/sample.security-findings.json',
        '--security-review',
        securityReviewPath,
        '--generated-at',
        '2026-05-07T00:00:00.000Z',
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);

      const manifest = JSON.parse(readFileSync(outputJson, 'utf8'));
      const validate = buildSchemaValidator();
      expect(validate(manifest), JSON.stringify(validate.errors)).toBe(true);
      expect(validateClaimEvidenceManifestSemantics(manifest)).toEqual([]);
      expect(manifest.summary.security).toMatchObject({
        claims: 1,
        findings: 3,
        reviews: 4,
        needsHumanReview: 1,
        outOfScope: 1,
        rejected: 1,
        highOrCriticalOpen: 1,
      });
      expect(manifest.sourceArtifacts).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ id: 'security-claims', present: true, schemaVersion: 'security-claim/v1' }),
          expect.objectContaining({ id: 'security-findings', present: true, schemaVersion: 'security-finding/v1' }),
          expect.objectContaining({ id: 'security-review', present: true, schemaVersion: 'security-review/v1' }),
        ]),
      );

      const securityClaim = manifest.claims.find((claim: { id: string }) => claim.id === 'sec-claim-001');
      expect(securityClaim).toMatchObject({
        criticality: 'high',
        securityClaimType: 'invariant',
        status: 'partial',
      });
      expect(securityClaim.externalIds).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            kind: 'security-claim',
            id: 'SEC-CLAIM-001',
            sourceArtifactId: 'security-claims',
            artifactPath: 'fixtures/security-assurance/sample.security-claims.json#/claims/0',
          }),
        ]),
      );
      expect(securityClaim.evidenceRefs).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ sourceArtifactId: 'security-claims', kind: 'spec' }),
          expect.objectContaining({ sourceArtifactId: 'security-findings', kind: 'adversarial' }),
          expect.objectContaining({ sourceArtifactId: 'security-review', kind: 'manual' }),
        ]),
      );
      const securityClaimEvidenceRef = securityClaim.evidenceRefs.find(
        (ref: { sourceArtifactId: string }) => ref.sourceArtifactId === 'security-claims',
      );
      expect(securityClaimEvidenceRef?.externalIds).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            kind: 'security-claim',
            id: 'SEC-CLAIM-001',
            sourceArtifactId: 'security-claims',
          }),
        ]),
      );
      const findingEvidenceRef = securityClaim.evidenceRefs.find(
        (ref: { sourceArtifactId: string }) => ref.sourceArtifactId === 'security-findings',
      );
      expect(findingEvidenceRef?.externalIds).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            kind: 'security-finding',
            id: 'SEC-FINDING-001',
            sourceArtifactId: 'security-findings',
            artifactPath: 'fixtures/security-assurance/sample.security-findings.json#/findings/0',
          }),
        ]),
      );
      const reviewEvidenceRefs = securityClaim.evidenceRefs.filter(
        (ref: { sourceArtifactId: string }) => ref.sourceArtifactId === 'security-review',
      );
      expect(reviewEvidenceRefs).toHaveLength(4);
      expect(reviewEvidenceRefs.map((ref: { id: string }) => ref.id)).toEqual(
        expect.arrayContaining(['security-review:sec-finding-001:0', 'security-review:sec-finding-001:3']),
      );
      expect(reviewEvidenceRefs.flatMap((ref: { externalIds?: Array<{ id: string }> }) => ref.externalIds ?? [])).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            kind: 'security-review',
            id: 'SEC-FINDING-001:review:0',
            sourceArtifactId: 'security-review',
          }),
          expect.objectContaining({
            kind: 'security-review',
            id: 'SEC-FINDING-001:review:3',
            sourceArtifactId: 'security-review',
          }),
        ]),
      );
      expect(securityClaim.missingEvidenceRefs).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            id: 'security-human-review:sec-finding-001',
            expectedKind: 'manual',
          }),
        ]),
      );
      expect(securityClaim.notes).toEqual(
        expect.arrayContaining([
          expect.stringContaining('security-finding:SEC-FINDING-001'),
          expect.stringContaining('security-attention:high SEC-FINDING-001'),
          expect.stringContaining('reviewResult=out-of-scope falsePositiveRootCause=out-of-scope'),
          expect.stringContaining('reviewResult=rejected falsePositiveRootCause=dead-code'),
        ]),
      );

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toContain('## Security findings');
      expect(markdown).toContain('securityType');
      expect(markdown).toContain('## External IDs');
      expect(markdown).toContain('security-claim:SEC-CLAIM-001 (security-claims)');
      expect(markdown).toContain('security-finding:SEC-FINDING-001 (security-findings)');
      expect(markdown).toContain('- highOrCriticalOpen: 1');
      expect(markdown).toContain('| sec-claim-001 | invariant | high | A2 | A1 | partial |');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('tracks assumption-derived security findings as assumption handling evidence', async () => {
    const mod = await import(moduleUrl);
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-claim-evidence-manifest-assumption-'));
    const outputJson = join(sandbox, 'claim-evidence-manifest.json');
    const outputMd = join(sandbox, 'claim-evidence-manifest.md');

    try {
      const result = runScript([
        '--assurance-summary',
        'fixtures/security-assurance/cache-key/expected/assurance-summary.json',
        '--security-claims',
        'fixtures/security-assurance/cache-key/expected/security-claims.json',
        '--security-findings',
        'fixtures/security-assurance/cache-key/expected/security-findings.json',
        '--security-review',
        'fixtures/security-assurance/cache-key/expected/security-review.json',
        '--generated-at',
        '2026-05-07T00:00:00.000Z',
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const manifest = JSON.parse(readFileSync(outputJson, 'utf8'));
      const validate = buildSchemaValidator();
      expect(validate(manifest), JSON.stringify(validate.errors)).toBe(true);
      const assumptionClaim = manifest.claims.find((claim: { id: string }) => claim.id === 'sec-claim-003');

      expect(assumptionClaim).toMatchObject({
        securityClaimType: 'assumption',
        assumptionHandlingRefs: expect.arrayContaining([
          expect.objectContaining({
            mode: 'residual-risk',
            findingId: 'SEC-FINDING-002',
            reviewResult: 'out-of-scope',
          }),
        ]),
      });
      expect(assumptionClaim.missingEvidenceRefs).not.toEqual(
        expect.arrayContaining([
          expect.objectContaining({ id: 'security-human-review:sec-finding-002' }),
        ]),
      );
      expect(manifest.summary.security).toMatchObject({
        assumptionValidationRequired: 0,
        assumptionResidualRisk: 1,
      });

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toContain('## Assumption handling');
      expect(markdown).toContain('SEC-FINDING-002');
      expect(markdown).toContain('residual-risk');

      assumptionClaim.assumptionHandlingRefs.push({
        ...assumptionClaim.assumptionHandlingRefs[0],
        id: 'security-assumption:sec-finding-002:residual-risk:duplicate-source',
        sourceArtifactId: 'duplicate-source',
      });
      const duplicateSourceMarkdown = mod.renderClaimEvidenceManifestMarkdown(manifest);
      const assumptionClaimSummaryLine = duplicateSourceMarkdown
        .split('\n')
        .find((line: string) => line.startsWith('| sec-claim-003 |'));
      expect(assumptionClaimSummaryLine?.match(/SEC-FINDING-002:residual-risk/g)).toHaveLength(1);
      expect(duplicateSourceMarkdown).toContain(
        '| sec-claim-003 | security-assumption:sec-finding-002:residual-risk:duplicate-source | residual-risk | SEC-FINDING-002 | out-of-scope | duplicate-source |',
      );
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('attaches assurance warnings when a claim uses id instead of claimId', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-claim-evidence-manifest-id-warning-'));
    const fixture = JSON.parse(readFileSync(resolve(repoRoot, 'fixtures/assurance/sample.assurance-summary.json'), 'utf8'));
    const assuranceSummaryPath = join(sandbox, 'assurance-summary.json');
    const outputJson = join(sandbox, 'claim-evidence-manifest.json');
    const outputMd = join(sandbox, 'claim-evidence-manifest.md');

    try {
      const claim = fixture.claims[0];
      claim.id = 'id-only-claim';
      delete claim.claimId;
      for (const evidence of claim.evidence ?? []) {
        evidence.claimRefs = ['id-only-claim'];
      }
      fixture.summary.warningCount = 1;
      fixture.warnings = [
        {
          claimId: 'id-only-claim',
          code: 'id-only-warning',
          message: 'warning is attached via computed claim id',
        },
      ];
      writeJson(assuranceSummaryPath, fixture);

      const result = runScript([
        '--assurance-summary',
        assuranceSummaryPath,
        '--generated-at',
        '2026-04-28T18:20:00.000Z',
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const manifest = JSON.parse(readFileSync(outputJson, 'utf8'));
      const idOnlyClaim = manifest.claims.find((entry: { id: string }) => entry.id === 'id-only-claim');

      expect(idOnlyClaim?.notes).toEqual(
        expect.arrayContaining([
          'assurance-warning:id-only-warning warning is attached via computed claim id',
        ]),
      );
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('escapes backslashes before markdown table delimiters', async () => {
    const mod = await import(moduleUrl);
    const markdown = mod.renderClaimEvidenceManifestMarkdown({
      schemaVersion: 'claim-evidence-manifest/v1',
      generatedAt: '2026-04-28T18:20:00.000Z',
      sourceArtifacts: [
        {
          id: String.raw`artifact\id|pipe`,
          kind: 'assurance-summary',
          present: true,
          required: true,
          path: String.raw`artifacts\assurance|summary.json`,
          schemaVersion: 'assurance-summary/v1',
        },
      ],
      claims: [
        {
          id: String.raw`claim\id|pipe`,
          statement: 'claim statement',
          criticality: 'high',
          targetLevel: 'A2',
          achievedLevel: 'A2',
          status: 'satisfied',
          evidenceRefs: [],
          missingEvidenceRefs: [],
          proofObligationRefs: [],
          counterexampleRefs: [],
          waiverRefs: [],
          notes: [],
        },
      ],
      summary: {
        totalClaims: 1,
        fullySupported: 1,
        partiallySupported: 0,
        waived: 0,
        unresolved: 0,
      },
    });

    expect(markdown).toContain(
      String.raw`| artifact\\id\|pipe | assurance-summary | true | true | artifacts\\assurance\|summary.json | assurance-summary/v1 |`,
    );
    expect(markdown).toContain(String.raw`| claim\\id\|pipe | n/a | high | A2 | A2 | satisfied | 0 | 0 | 0 | n/a | n/a |`);
  });

  it('preserves lower explicit change-package achievedLevel when a claim is also present in assurance summary', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-claim-evidence-manifest-explicit-achieved-'));
    const fixture = JSON.parse(
      readFileSync(resolve(repoRoot, 'fixtures/change-package/sample.change-package-v2.json'), 'utf8'),
    );
    const changePackagePath = join(sandbox, 'change-package-v2.json');
    const outputJson = join(sandbox, 'claim-evidence-manifest.json');
    const outputMd = join(sandbox, 'claim-evidence-manifest.md');

    try {
      fixture.assurance = {
        targetLevel: 'A3',
        achievedLevel: 'A1',
        status: 'partial',
      };
      fixture.claims[0] = {
        ...fixture.claims[0],
        id: 'no-negative-stock',
        statement: 'Inventory stock never becomes negative after an accepted reservation.',
        criticality: 'high',
      };
      fixture.proofObligations[0].claimId = 'no-negative-stock';
      fixture.counterexamples[0].claimIds = ['no-negative-stock'];
      writeJson(changePackagePath, fixture);

      const result = runScript([
        '--assurance-summary',
        'fixtures/assurance/sample.assurance-summary.json',
        '--change-package',
        changePackagePath,
        '--quality-scorecard',
        'fixtures/quality/sample.quality-scorecard.json',
        '--generated-at',
        '2026-04-28T18:20:00.000Z',
        '--output-json',
        outputJson,
        '--output-md',
        outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const manifest = JSON.parse(readFileSync(outputJson, 'utf8'));
      const stockClaim = manifest.claims.find((claim: { id: string }) => claim.id === 'no-negative-stock');

      expect(stockClaim).toMatchObject({
        targetLevel: 'A3',
        achievedLevel: 'A1',
        status: 'partial',
      });
      expect(stockClaim.notes).toEqual(
        expect.arrayContaining([
          expect.stringContaining('achievedLevel imported from change-package/v2 top-level assurance'),
        ]),
      );
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects change-package v2 references to claims that are not anchored by source claims', () => {
    const fixture = JSON.parse(
      readFileSync(resolve(repoRoot, 'fixtures/change-package/sample.change-package-v2.json'), 'utf8'),
    );
    const cases = [
      {
        label: 'proof obligation',
        mutate: (payload: typeof fixture) => {
          payload.proofObligations[0].claimId = 'phantom-claim';
        },
        expectedContext: 'proofObligations[0].claimId',
      },
      {
        label: 'counterexample',
        mutate: (payload: typeof fixture) => {
          payload.counterexamples[0].claimIds = ['phantom-claim'];
        },
        expectedContext: 'counterexamples[0].claimIds',
      },
      {
        label: 'waiver',
        mutate: (payload: typeof fixture) => {
          payload.waivers = [
            {
              owner: '@team-risk',
              expires: '2026-06-30',
              reason: 'Orphan waiver should not create a synthetic claim.',
              relatedClaimIds: ['phantom-claim'],
            },
          ];
        },
        expectedContext: 'waivers[0].relatedClaimIds',
      },
    ];

    for (const testCase of cases) {
      const sandbox = mkdtempSync(join(tmpdir(), `ae-claim-evidence-manifest-orphan-${testCase.label}-`));
      const changePackagePath = join(sandbox, 'change-package-v2.json');
      const outputJson = join(sandbox, 'claim-evidence-manifest.json');
      const outputMd = join(sandbox, 'claim-evidence-manifest.md');

      try {
        const payload = structuredClone(fixture);
        testCase.mutate(payload);
        writeJson(changePackagePath, payload);

        const result = runScript([
          '--assurance-summary',
          'fixtures/assurance/sample.assurance-summary.json',
          '--change-package',
          changePackagePath,
          '--quality-scorecard',
          'fixtures/quality/sample.quality-scorecard.json',
          '--generated-at',
          '2026-04-28T18:20:00.000Z',
          '--output-json',
          outputJson,
          '--output-md',
          outputMd,
        ]);

        expect(result.status, result.stderr || result.stdout).toBe(1);
        expect(result.stderr).toContain(testCase.expectedContext);
        expect(result.stderr).toContain("references unknown claim 'phantom-claim'");
      } finally {
        rmSync(sandbox, { recursive: true, force: true });
      }
    }
  });
});
