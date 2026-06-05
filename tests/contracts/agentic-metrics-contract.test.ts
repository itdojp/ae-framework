import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const schema = JSON.parse(
  readFileSync(resolve('schema/agentic-metrics.schema.json'), 'utf8'),
) as Record<string, unknown>;
const sampleFixture = JSON.parse(
  readFileSync(resolve('fixtures/agentic-metrics/sample.agentic-metrics.json'), 'utf8'),
) as Record<string, unknown>;
const agentPrAssuranceFixture = JSON.parse(
  readFileSync(resolve('fixtures/agentic-metrics/agent-pr-assurance-metrics.example.json'), 'utf8'),
) as Record<string, unknown>;

function compileSchema() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
}

describe('agentic-metrics contract', () => {
  it('validates existing agentic metrics fixtures with and without report-only PR assurance metrics', () => {
    const validate = compileSchema();

    expect(validate(sampleFixture), JSON.stringify(validate.errors)).toBe(true);
    expect(validate(agentPrAssuranceFixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('keeps agentPrAssurance report-only', () => {
    const validate = compileSchema();
    const invalidFixture = structuredClone(agentPrAssuranceFixture) as {
      agentPrAssurance: { reportOnly?: boolean };
    };

    invalidFixture.agentPrAssurance.reportOnly = false;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/agentPrAssurance/reportOnly')).toBe(true);
  });

  it('allows n/a lane compliance when no lanes are required', () => {
    const validate = compileSchema();
    const nAComplianceFixture = structuredClone(agentPrAssuranceFixture) as {
      agentPrAssurance: {
        metrics: {
          required_lane_compliance: {
            satisfied: number;
            required: number;
            ratio: number | null;
            missingLanes?: string[];
            notApplicable?: boolean;
          };
        };
      };
    };

    nAComplianceFixture.agentPrAssurance.metrics.required_lane_compliance = {
      satisfied: 0,
      required: 0,
      ratio: null,
      missingLanes: [],
      notApplicable: true,
    };

    expect(validate(nAComplianceFixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('requires all named report-only agent PR assurance metrics when the extension is present', () => {
    const validate = compileSchema();
    const invalidFixture = structuredClone(agentPrAssuranceFixture) as {
      agentPrAssurance: { metrics: Record<string, unknown> };
    };

    delete invalidFixture.agentPrAssurance.metrics.false_block_rate;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/agentPrAssurance/metrics')).toBe(true);
  });
});
