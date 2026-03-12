import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const schema = JSON.parse(
  readFileSync(resolve('schema/context-pack-boundary-map.schema.json'), 'utf8'),
) as Record<string, unknown>;
const fixture = JSON.parse(
  readFileSync(resolve('fixtures/context-pack/sample.boundary-map.json'), 'utf8'),
) as Record<string, unknown>;

describe('context-pack boundary map contract', () => {
  it('validates the sample boundary map fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects slice upstream refs without sliceId', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      slices: Array<{
        consumes?: Array<{
          upstream: { type: string; sliceId?: string };
        }>;
      }>;
    };

    invalidFixture.slices[1].consumes = [
      {
        ...invalidFixture.slices[1].consumes?.[0],
        upstream: { type: 'slice' },
      },
    ];

    expect(validate(invalidFixture)).toBe(false);
    expect(
      validate.errors?.some((entry) => entry.instancePath.includes('/upstream')),
    ).toBe(true);
  });

  it('rejects slices without produces or consumes', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      slices: Array<Record<string, unknown>>;
    };

    invalidFixture.slices = [{ id: 'empty-slice' }];

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/slices/0')).toBe(true);
  });

  it('rejects empty produces or consumes arrays', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      slices: Array<Record<string, unknown>>;
    };

    invalidFixture.slices = [
      {
        id: 'empty-producer',
        produces: [],
      },
    ];

    expect(validate(invalidFixture)).toBe(false);
    expect(
      validate.errors?.some((entry) => entry.instancePath === '/slices/0/produces' || entry.instancePath === '/slices/0'),
    ).toBe(true);
  });
});
