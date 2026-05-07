import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const schema = JSON.parse(
  readFileSync(resolve('schema/temporal-run-summary.schema.json'), 'utf8'),
) as Record<string, unknown>;
const fixture = JSON.parse(
  readFileSync(resolve('fixtures/temporal/sample.temporal-run-summary.json'), 'utf8'),
) as Record<string, unknown>;

const buildValidator = () => {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
};

describe('temporal run summary contract', () => {
  it('validates the sample Temporal adapter run summary fixture', () => {
    const validate = buildValidator();

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('requires workflow identity and run identity', () => {
    const validate = buildValidator();
    const invalidFixture = structuredClone(fixture) as {
      execution: Record<string, unknown>;
    };

    delete invalidFixture.execution.workflowId;
    delete invalidFixture.execution.runId;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/execution')).toBe(true);
  });

  it('keeps Temporal metadata out of existing assurance artifact refs', () => {
    const validate = buildValidator();
    const validFixture = structuredClone(fixture) as {
      outputArtifacts: Record<string, { kind: string; schemaVersion: string }>;
    };

    expect(validFixture.outputArtifacts.temporalRunSummary.kind).toBe('temporal-run-summary');
    expect(validFixture.outputArtifacts.assuranceSummary.kind).toBe('assurance-summary');
    expect(validFixture.outputArtifacts.claimEvidenceManifest.kind).toBe('claim-evidence-manifest');
    expect(validate(validFixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects unsupported signal status values', () => {
    const validate = buildValidator();
    const invalidFixture = structuredClone(fixture) as {
      signals: {
        awaited: Array<Record<string, unknown>>;
      };
    };

    invalidFixture.signals.awaited[0].status = 'approved';

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/signals/awaited/0/status')).toBe(true);
  });

  it('marks the adapter as optional rather than a mandatory dependency', () => {
    const validate = buildValidator();
    const invalidFixture = structuredClone(fixture) as {
      adapter: Record<string, unknown>;
    };

    invalidFixture.adapter.mandatoryDependency = 'false';

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/adapter/mandatoryDependency')).toBe(true);
  });
});
