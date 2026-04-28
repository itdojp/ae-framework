import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { validateClaimEvidenceManifestSemantics } from '../../scripts/ci/lib/claim-evidence-manifest-contract.mjs';

const schema = JSON.parse(
  readFileSync(resolve('schema/claim-evidence-manifest.schema.json'), 'utf8'),
) as Record<string, unknown>;
const fixture = JSON.parse(
  readFileSync(resolve('fixtures/assurance/sample.claim-evidence-manifest.json'), 'utf8'),
) as Record<string, unknown>;

const buildValidator = () => {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
};

describe('claim evidence manifest contract', () => {
  it('validates the sample claim evidence manifest fixture', () => {
    const validate = buildValidator();

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
    expect(validateClaimEvidenceManifestSemantics(fixture)).toEqual([]);
  });

  it('requires per-claim target and achieved assurance levels', () => {
    const validate = buildValidator();
    const invalidFixture = structuredClone(fixture) as {
      claims: Array<Record<string, unknown>>;
    };

    delete invalidFixture.claims[0].targetLevel;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/claims/0')).toBe(true);
  });

  it('rejects present source artifacts without a path', () => {
    const validate = buildValidator();
    const invalidFixture = structuredClone(fixture) as {
      sourceArtifacts: Array<Record<string, unknown>>;
    };

    invalidFixture.sourceArtifacts[0] = {
      ...invalidFixture.sourceArtifacts[0],
      path: null,
    };

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/sourceArtifacts/0/path')).toBe(true);
  });

  it('rejects negative claim summary counts', () => {
    const validate = buildValidator();
    const invalidFixture = structuredClone(fixture) as {
      summary: Record<string, unknown>;
    };

    invalidFixture.summary.unresolved = -1;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/summary/unresolved')).toBe(true);
  });

  it('rejects duplicate source artifact ids at the semantic contract layer', () => {
    const invalidFixture = structuredClone(fixture) as {
      sourceArtifacts: Array<Record<string, unknown>>;
    };

    invalidFixture.sourceArtifacts.push({
      ...invalidFixture.sourceArtifacts[0],
      path: 'artifacts/duplicate-source.json',
      description: 'duplicate source id with a different payload',
    });

    const duplicateSourceArtifactIndex = invalidFixture.sourceArtifacts.length - 1;
    const errors = validateClaimEvidenceManifestSemantics(invalidFixture);

    expect(errors.some((entry) => entry.keyword === 'duplicate_id')).toBe(true);
    expect(
      errors.some(
        (entry) => entry.instancePath === `/sourceArtifacts/${duplicateSourceArtifactIndex}/id`,
      ),
    ).toBe(true);
  });

  it('rejects duplicate claim ids at the semantic contract layer', () => {
    const invalidFixture = structuredClone(fixture) as {
      claims: Array<Record<string, unknown>>;
    };

    invalidFixture.claims.push({
      ...invalidFixture.claims[0],
      statement: 'Duplicate claim id with a different statement.',
      status: 'unresolved',
    });

    const duplicateClaimIndex = invalidFixture.claims.length - 1;
    const errors = validateClaimEvidenceManifestSemantics(invalidFixture);

    expect(errors.some((entry) => entry.keyword === 'duplicate_id')).toBe(true);
    expect(
      errors.some((entry) => entry.instancePath === `/claims/${duplicateClaimIndex}/id`),
    ).toBe(true);
  });

  it('rejects dangling source artifact references at the semantic contract layer', () => {
    const invalidFixture = structuredClone(fixture) as {
      claims: Array<{
        evidenceRefs: Array<Record<string, unknown>>;
      }>;
    };

    invalidFixture.claims[0].evidenceRefs[0].sourceArtifactId = 'missing-source-artifact';

    const errors = validateClaimEvidenceManifestSemantics(invalidFixture);

    expect(errors.some((entry) => entry.keyword === 'dangling_source_artifact_ref')).toBe(true);
    expect(errors.some((entry) => entry.instancePath === '/claims/0/evidenceRefs/0/sourceArtifactId')).toBe(true);
  });

  it('rejects references to source artifacts marked absent at the semantic contract layer', () => {
    const invalidFixture = structuredClone(fixture) as {
      claims: Array<{
        evidenceRefs: Array<Record<string, unknown>>;
      }>;
    };

    invalidFixture.claims[0].evidenceRefs[0].sourceArtifactId = 'verify-lite-run-summary';

    const errors = validateClaimEvidenceManifestSemantics(invalidFixture);

    expect(errors.some((entry) => entry.keyword === 'absent_source_artifact_ref')).toBe(true);
    expect(errors.some((entry) => entry.instancePath === '/claims/0/evidenceRefs/0/sourceArtifactId')).toBe(true);
  });

  it('rejects summary counts that do not match claim statuses at the semantic contract layer', () => {
    const invalidFixture = structuredClone(fixture) as {
      summary: Record<string, unknown>;
    };

    invalidFixture.summary.totalClaims = 999;

    const errors = validateClaimEvidenceManifestSemantics(invalidFixture);

    expect(errors.some((entry) => entry.keyword === 'summary_mismatch')).toBe(true);
    expect(errors.some((entry) => entry.instancePath === '/summary/totalClaims')).toBe(true);
  });
});
