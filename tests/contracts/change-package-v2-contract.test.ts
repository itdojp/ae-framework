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
});
