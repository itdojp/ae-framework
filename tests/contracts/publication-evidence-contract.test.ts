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

const requiredRuntimeArtifacts = [
  'gate-result.json',
  'assurance-summary.json',
  'policy-decision.json',
  'review-surface.md',
];

function buildRuntimeSmoke() {
  function buildRef(actionRef: string, jobPrefix: string) {
    return {
      actionRef,
      resolvedCommit: '0123456789abcdef0123456789abcdef01234567',
      workflowRunUrl: 'https://github.com/itdojp/ae-framework-impl-test-hub/actions/runs/123',
      verifiedAt: '2026-07-12T00:00:00Z',
      verifier: 'ootakazuhiko',
      verifierRole: 'release-owner',
      cases: {
        pass: {
          jobName: `${jobPrefix}-pass`,
          jobStatus: 'success',
          gateResult: 'pass',
          artifacts: requiredRuntimeArtifacts,
        },
        block: {
          jobName: `${jobPrefix}-block`,
          jobStatus: 'success',
          failOnBlock: false,
          gateResult: 'block',
          missingEvidenceRecorded: true,
          artifacts: requiredRuntimeArtifacts,
        },
      },
    };
  }
  return {
    consumerRepository: 'itdojp/ae-framework-impl-test-hub',
    immutableRelease: buildRef('itdojp/ae-framework@v1.0.1', 'immutable-v1.0.1'),
    movingMajor: buildRef('itdojp/ae-framework@v1', 'moving-v1'),
  };
}

function buildLiveMarketplaceCandidate() {
  const candidate = structuredClone(manifest);
  candidate.surfaces.assuranceGateMarketplace.state = 'live';
  candidate.surfaces.assuranceGateMarketplace.blockers = [];
  candidate.surfaces.assuranceGateMarketplace.evidence = {
    ...candidate.surfaces.assuranceGateMarketplace.evidence,
    listingUrl: 'https://github.com/marketplace/actions/ae-framework-assurance-gate',
    releaseNoteUrl: 'https://github.com/itdojp/ae-framework/releases/tag/v1.0.1',
    runtimeSmoke: buildRuntimeSmoke(),
  };
  return candidate;
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
    expect(errors.some((entry) => entry.keyword === 'live_runtime_smoke_required')).toBe(true);
  });

  it('accepts complete external immutable and moving-tag runtime smoke evidence', () => {
    const validateSchema = buildSchemaValidator();
    const candidate = buildLiveMarketplaceCandidate();

    expect(validateSchema(candidate), JSON.stringify(validateSchema.errors)).toBe(true);
    expect(validatePublicationEvidenceSemantics(candidate)).toEqual([]);
  });

  it('allows verified runtime smoke to be recorded while Marketplace listing remains blocked', () => {
    const validateSchema = buildSchemaValidator();
    const candidate = structuredClone(manifest);
    candidate.surfaces.assuranceGateMarketplace.evidence.runtimeSmoke = buildRuntimeSmoke();

    expect(validateSchema(candidate), JSON.stringify(validateSchema.errors)).toBe(true);
    expect(validatePublicationEvidenceSemantics(candidate)).toEqual([]);
    expect(candidate.surfaces.assuranceGateMarketplace.state).toBe('blocked');
    expect(candidate.surfaces.assuranceGateMarketplace.blockers.length).toBeGreaterThan(0);
  });

  it.each(['immutableRelease', 'movingMajor'])(
    'rejects live Marketplace state when %s runtime smoke is missing',
    (missingRef) => {
      const validateSchema = buildSchemaValidator();
      const candidate = buildLiveMarketplaceCandidate();
      delete (candidate.surfaces.assuranceGateMarketplace.evidence.runtimeSmoke as Record<string, unknown>)[missingRef];

      expect(validateSchema(candidate)).toBe(false);
      expect(validateSchema.errors?.some((entry) => entry.instancePath.endsWith('/runtimeSmoke'))).toBe(true);
    },
  );

  it('rejects immutable and moving smoke refs that resolve to different commits', () => {
    const candidate = buildLiveMarketplaceCandidate();
    const runtimeSmoke = candidate.surfaces.assuranceGateMarketplace.evidence.runtimeSmoke as {
      movingMajor: { resolvedCommit: string };
    };
    runtimeSmoke.movingMajor.resolvedCommit = 'fedcba9876543210fedcba9876543210fedcba98';

    expect(validatePublicationEvidenceSemantics(candidate)).toEqual(expect.arrayContaining([
      expect.objectContaining({ keyword: 'runtime_resolved_commit_mismatch' }),
    ]));
  });

  it('rejects runtime action refs that do not match the documented tags', () => {
    const candidate = buildLiveMarketplaceCandidate();
    const runtimeSmoke = candidate.surfaces.assuranceGateMarketplace.evidence.runtimeSmoke as {
      immutableRelease: { actionRef: string };
      movingMajor: { actionRef: string };
    };
    runtimeSmoke.immutableRelease.actionRef = 'itdojp/ae-framework@v1.0.9';
    runtimeSmoke.movingMajor.actionRef = 'itdojp/ae-framework@v2';

    const errors = validatePublicationEvidenceSemantics(candidate);
    expect(errors.some((entry) => entry.keyword === 'immutable_action_ref_mismatch')).toBe(true);
    expect(errors.some((entry) => entry.keyword === 'moving_action_ref_mismatch')).toBe(true);
  });

  it('rejects release-note and path evidence for a different immutable tag', () => {
    const candidate = buildLiveMarketplaceCandidate();
    candidate.surfaces.assuranceGateMarketplace.evidence.releaseNoteUrl =
      'https://github.com/itdojp/ae-framework/releases/tag/v9.9.9';
    candidate.surfaces.assuranceGateMarketplace.evidence.externalPathResolutionUrl =
      'https://github.com/itdojp/ae-framework/blob/v9.9.9/action.yml';

    const errors = validatePublicationEvidenceSemantics(candidate);
    expect(errors.some((entry) => entry.keyword === 'release_note_tag_mismatch')).toBe(true);
    expect(errors.some((entry) => entry.keyword === 'external_path_tag_mismatch')).toBe(true);
  });

  it('requires every matrix case to have a unique run and job locator', () => {
    const candidate = buildLiveMarketplaceCandidate();
    const runtimeSmoke = candidate.surfaces.assuranceGateMarketplace.evidence.runtimeSmoke as {
      immutableRelease: { cases: { pass: { jobName: string } } };
      movingMajor: { cases: { pass: { jobName: string } } };
    };
    runtimeSmoke.movingMajor.cases.pass.jobName =
      runtimeSmoke.immutableRelease.cases.pass.jobName;

    expect(validatePublicationEvidenceSemantics(candidate)).toEqual(expect.arrayContaining([
      expect.objectContaining({ keyword: 'runtime_case_locator_not_unique' }),
    ]));
  });

  it('rejects incomplete pass/block artifact and policy evidence', () => {
    const validateSchema = buildSchemaValidator();
    const candidate = buildLiveMarketplaceCandidate();
    const runtimeSmoke = candidate.surfaces.assuranceGateMarketplace.evidence.runtimeSmoke as {
      immutableRelease: {
        cases: {
          pass: { artifacts: string[] };
          block: { missingEvidenceRecorded: boolean };
        };
      };
    };
    runtimeSmoke.immutableRelease.cases.pass.artifacts = ['gate-result.json'];
    runtimeSmoke.immutableRelease.cases.block.missingEvidenceRecorded = false;

    expect(validateSchema(candidate)).toBe(false);
  });

  it('rejects source-repository, repository-mismatched, and token-like runtime URLs', () => {
    const validateSchema = buildSchemaValidator();
    const candidates = [
      'https://github.com/itdojp/ae-framework/actions/runs/123',
      'https://github.com/itdojp/another-consumer/actions/runs/123',
      'https://user:token@github.com/itdojp/ae-framework-impl-test-hub/actions/runs/123?token=secret',
    ].map((workflowRunUrl) => {
      const candidate = buildLiveMarketplaceCandidate();
      const runtimeSmoke = candidate.surfaces.assuranceGateMarketplace.evidence.runtimeSmoke as {
        immutableRelease: { workflowRunUrl: string };
      };
      runtimeSmoke.immutableRelease.workflowRunUrl = workflowRunUrl;
      return candidate;
    });

    for (const candidate of candidates) {
      expect(validateSchema(candidate)).toBe(false);
    }
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

  it('accepts future SemVer release lines without hard-coding 0.1.x', () => {
    const validateSchema = buildSchemaValidator();
    const candidate = structuredClone(manifest);
    candidate.surfaces.coreNpmPackage.expectedVersion = '1.2.3-rc.1+build.7';

    expect(validateSchema(candidate), JSON.stringify(validateSchema.errors)).toBe(true);
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
