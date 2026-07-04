import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import yaml from 'yaml';

const assuranceProfileSchema = JSON.parse(
  readFileSync(resolve('schema/assurance-profile.schema.json'), 'utf8'),
) as Record<string, unknown>;
const assuranceProfileFixture = JSON.parse(
  readFileSync(resolve('fixtures/assurance/sample.assurance-profile.json'), 'utf8'),
) as Record<string, unknown>;
const deployTimeProfilePaths = [
  'profiles/minimal.yaml',
  'profiles/standard.yaml',
  'profiles/full.yaml',
];
const currentRequiredCheckContexts = ['verify-lite', 'policy-gate', 'gate'];

describe('assurance profile contract', () => {
  it('validates the sample assurance profile fixture', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(assuranceProfileSchema);

    expect(validate(assuranceProfileFixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('validates deploy-time adoption profiles with required deployment metadata', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(assuranceProfileSchema);

    for (const profilePath of deployTimeProfilePaths) {
      const profile = yaml.parse(readFileSync(resolve(profilePath), 'utf8')) as {
        profileId?: string;
        deployment?: {
          tier?: string;
          artifactSchemas?: Array<{ path?: string; purpose?: string; required?: boolean }>;
          activeLanes?: string[];
          gatePolicy?: { evaluator?: string; source?: string };
          requiredChecks?: string[];
        };
      };

      expect(validate(profile), `${profilePath}: ${JSON.stringify(validate.errors)}`).toBe(true);
      expect(profile.deployment?.tier).toBe(profile.profileId);
      expect(profile.deployment?.artifactSchemas?.length).toBeGreaterThan(0);
      expect(profile.deployment?.artifactSchemas?.every((entry) => entry.path && entry.purpose)).toBe(true);
      expect(profile.deployment?.activeLanes?.length).toBeGreaterThan(0);
      expect(profile.deployment?.gatePolicy?.source).toBeTruthy();
      expect(profile.deployment?.requiredChecks?.length).toBeGreaterThan(0);
      expect(profile.deployment?.requiredChecks).toEqual(currentRequiredCheckContexts);
    }
  });

  it('allows custom deploy-time profiles to use the same deployment metadata contract', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(assuranceProfileSchema);
    const customProfile = structuredClone(assuranceProfileFixture) as Record<string, unknown>;

    customProfile.profileId = 'tenant-custom';
    customProfile.deployment = {
      tier: 'custom',
      mapsToReadmeProfile: 'Custom',
      artifactSchemas: [
        {
          path: 'schema/assurance-summary.schema.json',
          purpose: 'Custom profile assurance summary input.',
          required: true,
        },
      ],
      activeLanes: ['artifact-schema-validation', 'pr-review-surface'],
      gatePolicy: {
        evaluator: 'yaml',
        source: '.ae/policy.yml',
      },
      requiredChecks: ['assurance-gate'],
    };

    expect(validate(customProfile), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects claims without required evidence kinds', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(assuranceProfileSchema);
    const invalidFixture = structuredClone(assuranceProfileFixture) as {
      claims: Array<Record<string, unknown>>;
    };

    invalidFixture.claims[0] = {
      ...invalidFixture.claims[0],
      requiredEvidenceKinds: [],
    };

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/claims/0/requiredEvidenceKinds')).toBe(true);
  });

  it('accepts boundary-map as a required evidence kind', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(assuranceProfileSchema);
    const fixture = structuredClone(assuranceProfileFixture) as {
      claims: Array<Record<string, unknown>>;
    };

    fixture.claims[0] = {
      ...fixture.claims[0],
      requiredEvidenceKinds: ['schema', 'boundary-map'],
    };

    expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
  });

  it('rejects claims with non-positive minIndependentSources', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(assuranceProfileSchema);
    const invalidFixture = structuredClone(assuranceProfileFixture) as {
      claims: Array<Record<string, unknown>>;
    };

    invalidFixture.claims[0] = {
      ...invalidFixture.claims[0],
      minIndependentSources: 0,
    };

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/claims/0/minIndependentSources')).toBe(true);
  });
});
