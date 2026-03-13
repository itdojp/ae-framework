import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const schema = JSON.parse(
  readFileSync(resolve('schema/notice-readiness-audit.schema.json'), 'utf8'),
) as Record<string, unknown>;
const fixture = JSON.parse(
  readFileSync(resolve('fixtures/legal/sample.notice-readiness-audit.json'), 'utf8'),
) as Record<string, unknown>;

describe('notice readiness audit contract', () => {
  it('validates the sample fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects missing proposed NOTICE lines', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const invalidFixture = structuredClone(fixture) as {
      proposedRootNotice: { lines: string[] };
    };

    invalidFixture.proposedRootNotice.lines = [];

    expect(validate(invalidFixture)).toBe(false);
    expect(
      validate.errors?.some((entry) => entry.instancePath.startsWith('/proposedRootNotice/lines')),
    ).toBe(true);
  });
});
