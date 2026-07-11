import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { describe, expect, it } from 'vitest';
import { validatePublicationEvidenceSemantics } from '../../scripts/release/publication-evidence-contract.mjs';
import { validatePublicationEvidenceFiles } from '../../scripts/release/validate-publication-evidence.mjs';

type Manifest = {
  surfaces: {
    mainBranchProtection: Record<string, unknown> & { evidence: Record<string, unknown>; blockers: string[] };
    coreNpmPackage: Record<string, unknown> & { evidence: Record<string, unknown>; blockers: string[] };
    assuranceGateMarketplace: Record<string, unknown> & { evidence: Record<string, unknown>; blockers: string[] };
  };
};

const schema = JSON.parse(
  readFileSync(resolve('schema/publication-evidence-v1.schema.json'), 'utf8'),
) as Record<string, unknown>;
const manifest = JSON.parse(
  readFileSync(resolve('docs/operate/publication-evidence.json'), 'utf8'),
) as Manifest;

function buildSchemaValidator() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
}

describe('publication evidence contract', () => {
  it('wires deterministic validation into the default verify-lite pipeline', () => {
    const packageJson = JSON.parse(readFileSync(resolve('package.json'), 'utf8')) as {
      scripts: Record<string, string>;
    };
    const verifyLite = readFileSync(resolve('scripts/ci/run-verify-lite-local.sh'), 'utf8');
    const verifyLiteWorkflow = readFileSync(resolve('.github/workflows/verify-lite.yml'), 'utf8');

    expect(packageJson.scripts['publication:evidence:validate']).toBe(
      'node scripts/release/validate-publication-evidence.mjs',
    );
    expect(verifyLite).toContain('pnpm -s run publication:evidence:validate');
    expect(verifyLiteWorkflow).toContain(
      'if [[ "$file" == "docs/operate/publication-evidence.json" ]]; then',
    );
    expect(verifyLiteWorkflow).toContain(
      'tests/contracts/cli-artifacts-contracts.test.ts tests/contracts/publication-evidence-contract.test.ts',
    );
  });

  it('accepts the canonical mixed-state manifest without overclaiming unavailable surfaces', () => {
    const validateSchema = buildSchemaValidator();

    expect(validateSchema(manifest), JSON.stringify(validateSchema.errors)).toBe(true);
    expect(validatePublicationEvidenceSemantics(manifest)).toEqual([]);
    expect(manifest.surfaces.mainBranchProtection.state).toBe('live');
    expect(manifest.surfaces.coreNpmPackage.state).toBe('blocked');
    expect(manifest.surfaces.assuranceGateMarketplace.state).toBe('blocked');
    expect(validatePublicationEvidenceFiles({
      manifestPath: 'docs/operate/publication-evidence.json',
      schemaPath: 'schema/publication-evidence-v1.schema.json',
    }).valid).toBe(true);
  });

  it('rejects live npm state without registry, provenance, workflow, and smoke evidence', () => {
    const candidate = structuredClone(manifest);
    candidate.surfaces.coreNpmPackage.state = 'live';
    candidate.surfaces.coreNpmPackage.blockers = [];
    candidate.surfaces.coreNpmPackage.evidence = {};

    const errors = validatePublicationEvidenceSemantics(candidate);

    expect(errors.filter((entry) => entry.keyword === 'live_evidence_required')).toHaveLength(12);
  });

  it('rejects live Marketplace state without listing and release-note evidence', () => {
    const candidate = structuredClone(manifest);
    candidate.surfaces.assuranceGateMarketplace.state = 'live';
    candidate.surfaces.assuranceGateMarketplace.blockers = [];
    candidate.surfaces.assuranceGateMarketplace.evidence = {
      verifiedAt: candidate.surfaces.assuranceGateMarketplace.evidence.verifiedAt,
    };

    const errors = validatePublicationEvidenceSemantics(candidate);

    expect(errors.some((entry) => entry.instancePath.endsWith('/listingUrl'))).toBe(true);
    expect(errors.some((entry) => entry.instancePath.endsWith('/releaseNoteUrl'))).toBe(true);
  });

  it('rejects live branch protection unless all desired contexts and successful apply/fetch evidence are observed', () => {
    const candidate = structuredClone(manifest);
    candidate.surfaces.mainBranchProtection.state = 'live';
    candidate.surfaces.mainBranchProtection.blockers = [];
    candidate.surfaces.mainBranchProtection.evidence.applyStatus = 'failure';
    candidate.surfaces.mainBranchProtection.evidence.observedContexts = [
      'verify-lite',
      'gate',
      'policy-gate',
    ];

    const errors = validatePublicationEvidenceSemantics(candidate);

    expect(errors.some((entry) => entry.keyword === 'live_apply_must_succeed')).toBe(true);
    expect(errors.some((entry) => entry.message.includes('deploy-time-profiles'))).toBe(true);
  });

  it('allows prepared state without live-only evidence', () => {
    const candidate = structuredClone(manifest);
    candidate.surfaces.coreNpmPackage.state = 'prepared';
    candidate.surfaces.coreNpmPackage.blockers = [];
    candidate.surfaces.coreNpmPackage.evidence = {};

    expect(validatePublicationEvidenceSemantics(candidate)).toEqual([]);
  });

  it('does not accept a successful preflight as live npm publication evidence', () => {
    const candidate = structuredClone(manifest);
    candidate.surfaces.coreNpmPackage.state = 'live';
    candidate.surfaces.coreNpmPackage.blockers = [];
    candidate.surfaces.coreNpmPackage.evidence = {
      ...candidate.surfaces.coreNpmPackage.evidence,
      registryUrl: 'https://www.npmjs.com/package/@ae-framework/core',
      registryVersion: '0.1.0',
      provenanceUrl: 'https://www.npmjs.com/package/@ae-framework/core#provenance',
      cleanInstallImportEvidenceUrl: 'https://github.com/itdojp/ae-framework/actions/runs/1',
    };

    const errors = validatePublicationEvidenceSemantics(candidate);

    expect(errors.some((entry) => entry.keyword === 'live_publish_mode_invalid')).toBe(true);
  });

  it('requires blocked states to explain their blocker', () => {
    const candidate = structuredClone(manifest);
    candidate.surfaces.assuranceGateMarketplace.blockers = [];

    const errors = validatePublicationEvidenceSemantics(candidate);

    expect(errors.some((entry) => entry.keyword === 'blocked_state_requires_blocker')).toBe(true);
  });

  it('rejects evidence URLs and verifiers outside repository-controlled allowlists', () => {
    const validateSchema = buildSchemaValidator();
    const candidate = structuredClone(manifest);
    candidate.surfaces.mainBranchProtection.evidence.applyWorkflowRunUrl =
      'https://evil.example/actions/runs/1';
    candidate.surfaces.coreNpmPackage.evidence.publishWorkflowRunUrl =
      'https://user:secret@example.com/actions/runs/1?sig=secret';
    candidate.surfaces.assuranceGateMarketplace.evidence.externalPathResolutionUrl =
      'https://evil.example/action.yml';
    candidate.surfaces.assuranceGateMarketplace.evidence.verifier = 'mallory';

    expect(validateSchema(candidate)).toBe(false);
    expect(validateSchema.errors?.length).toBeGreaterThanOrEqual(4);
  });
});
