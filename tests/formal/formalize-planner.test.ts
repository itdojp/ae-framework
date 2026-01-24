import { describe, it, expect } from 'vitest';
import {
  FORMAL_PLAN_REQUIRED_FIELDS,
  FORMAL_PLAN_SCHEMA_VERSION,
  buildPlannerPrompt,
  samplingDefaults,
  samplingProfiles,
} from '../../packages/formalize-planner/src/index.js';

describe('formalize-planner prompt', () => {
  it('includes required fields and schema version', () => {
    const prompt = buildPlannerPrompt({ requirements: 'Example requirement' });
    expect(prompt).toContain(`schemaVersion: ${FORMAL_PLAN_SCHEMA_VERSION}`);
    for (const field of FORMAL_PLAN_REQUIRED_FIELDS) {
      expect(prompt).toContain(field);
    }
  });
});

describe('formalize-planner sampling', () => {
  it('exposes deterministic and balanced profiles', () => {
    expect(samplingProfiles.deterministic.temperature).toBe(0);
    expect(samplingProfiles.balanced.temperature).toBe(0.2);
  });

  it('defaults to balanced sampling', () => {
    expect(samplingDefaults).toEqual(samplingProfiles.balanced);
  });
});
