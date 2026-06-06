import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const schema = JSON.parse(
  readFileSync(resolve('schema/change-package-v2.schema.json'), 'utf8'),
) as Record<string, unknown>;
const fixture = JSON.parse(
  readFileSync(resolve('fixtures/change-package/sample.change-package-v2.json'), 'utf8'),
) as Record<string, unknown>;

describe('change-package v2 contract', () => {
  it('validates the sample proof-carrying change package fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects waivers without related claim ids', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      waivers: Array<Record<string, unknown>>;
    };

    invalidFixture.waivers = [
      {
        owner: '@team-platform',
        expires: '2026-12-31',
        reason: 'temporary rollout exception',
        relatedClaimIds: [],
      },
    ];

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/waivers/0/relatedClaimIds')).toBe(true);
  });

  it('preserves failed and not-applicable as package outcome states', () => {
    const claims = (fixture as { claims: Array<{ id: string; status: string }> }).claims;

    expect(claims).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: 'strict-proof-failure', status: 'failed' }),
      expect.objectContaining({ id: 'ui-out-of-scope', status: 'not-applicable' }),
    ]));
  });

  it('requires waiver evidence refs in the stabilized v2 contract', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      claims: Array<Record<string, unknown>>;
      waivers: Array<Record<string, unknown>>;
    };

    invalidFixture.claims.push({
      id: 'waived-without-evidence',
      statement: 'Waiver evidence must remain linked.',
      status: 'waived',
      criticality: 'medium',
      targetLevel: 'A2',
      achievedLevel: 'A1',
      requirementRefs: [],
      artifactRefs: ['docs/ci/change-package.md'],
    });
    invalidFixture.waivers = [
      {
        owner: '@team-platform',
        expires: '2026-12-31',
        reason: 'temporary rollout exception',
        relatedClaimIds: ['waived-without-evidence'],
      },
    ];

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/waivers/0')).toBe(true);
  });

  it('validates contract migration notes as an additive preview summary surface', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      contractMigrationNotes: Array<Record<string, unknown>>;
    };

    expect(Array.isArray(invalidFixture.contractMigrationNotes)).toBe(true);
    expect(invalidFixture.contractMigrationNotes[0]).toMatchObject({
      contractId: 'change-package/v2',
      compatibilityState: 'preview',
      dualWriteStatus: 'active',
      dualValidateStatus: 'active',
    });

    invalidFixture.contractMigrationNotes[0].compatibilityState = 'silent-breaking-change';
    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/contractMigrationNotes/0/compatibilityState')).toBe(true);
  });
});
