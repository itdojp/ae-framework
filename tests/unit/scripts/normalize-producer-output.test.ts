import { describe, it, expect, onTestFinished } from 'vitest';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const repoRoot = resolve('.');
const scriptPath = resolve('scripts/agents/normalize-producer-output.mjs');
const codexFixturePath = resolve('fixtures/agents/evidence-adapters/codex-cli-task-output.json');
const crossAgentFixtures = [
  {
    label: 'Codex CLI',
    path: 'fixtures/agents/evidence-adapters/codex-cli-task-output.json',
    producerId: 'codex-cli',
    expectedArtifacts: ['change-package/v2', 'claim-evidence-manifest/v1', 'ae-handoff/v1', 'hook-feedback/v1'],
  },
  {
    label: 'Claude Code',
    path: 'fixtures/agents/evidence-adapters/claude-code-task-output.json',
    producerId: 'claude-code',
    expectedArtifacts: ['ae-handoff/v1', 'hook-feedback/v1', 'change-package/v2'],
  },
  {
    label: 'GitHub Copilot',
    path: 'fixtures/agents/evidence-adapters/copilot-pr-review-output.json',
    producerId: 'github-copilot-pr-reviewer',
    expectedArtifacts: ['policy-decision/v1', 'change-package/v2', 'hook-feedback/v1'],
  },
  {
    label: 'Human maintainer',
    path: 'fixtures/agents/evidence-adapters/human-waiver-review-output.json',
    producerId: 'human-maintainer',
    expectedArtifacts: ['policy-decision/v1', 'claim-evidence-manifest/v1', 'change-package/v2'],
  },
  {
    label: 'CI test runner',
    path: 'fixtures/agents/evidence-adapters/ci/test-runner-output.json',
    producerId: 'ci-test-runner',
    expectedArtifacts: ['verify-lite-run-summary', 'quality-scorecard', 'report-envelope', 'producer-normalization-summary/v1', 'claim-evidence-manifest/v1'],
    expectedSummaryPath: 'fixtures/agents/producer-normalization-summary.ci.json',
  },
  {
    label: 'Formal runner',
    path: 'fixtures/agents/evidence-adapters/formal/model-check-output.json',
    producerId: 'formal-runner',
    expectedArtifacts: ['producer-normalization-summary/v1', 'formal-summary/v2', 'claim-evidence-manifest/v1', 'assurance-summary/v1'],
    expectedSummaryPath: 'fixtures/agents/producer-normalization-summary.formal.json',
  },
];
const schemaPath = resolve('schema/producer-normalization-summary.schema.json');

function createTempDir() {
  const parent = join(repoRoot, '.codex-local', 'tmp');
  mkdirSync(parent, { recursive: true });
  const dir = mkdtempSync(join(parent, 'normalize-producer-output-'));
  onTestFinished(() => {
    rmSync(dir, { recursive: true, force: true });
  });
  return dir;
}

function runNormalizer(args: string[]) {
  return spawnSync('node', [scriptPath, ...args], {
    cwd: repoRoot,
    encoding: 'utf8',
  });
}

function validateSummary(summary: unknown) {
  const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const ok = validate(summary);
  expect(validate.errors ?? []).toEqual([]);
  expect(ok).toBe(true);
}

describe('normalize-producer-output', () => {
  it('generates a report-only summary from the Codex producer fixture', () => {
    const dir = createTempDir();
    const outJson = join(dir, 'producer-normalization-summary.json');
    const outMd = join(dir, 'producer-normalization-summary.md');

    const result = runNormalizer([
      '--input', codexFixturePath,
      '--out-json', outJson,
      '--out-md', outMd,
      '--generated-at', '2026-06-20T00:00:00.000Z',
    ]);

    expect(result.status).toBe(0);
    const summary = JSON.parse(readFileSync(outJson, 'utf8'));
    validateSummary(summary);

    expect(summary.schemaVersion).toBe('producer-normalization-summary/v1');
    expect(summary.mode).toBe('report-only');
    expect(summary.producer.id).toBe('codex-cli');
    expect(summary.controlPlaneJudgment).toMatchObject({
      emitsDecision: false,
      result: 'not-emitted',
    });
    expect(summary.controlPlaneRouting.expectedArtifacts.map((entry: { artifact: string }) => entry.artifact)).toEqual(
      expect.arrayContaining(['change-package/v2', 'claim-evidence-manifest/v1', 'ae-handoff/v1', 'hook-feedback/v1']),
    );
    expect(summary.controlPlaneRouting.missingEvidence).toEqual(
      expect.arrayContaining([
        expect.objectContaining({
          kind: 'command',
          command: 'pnpm -s run check:schemas',
        }),
      ]),
    );
    expect(summary.controlPlaneRouting.unresolvedNotes.join('\n')).toContain('ACP-GAP-002');
    expect(summary.controlPlaneRouting.reportOnlyFindings.every((finding: { severity: string }) => finding.severity === 'report-only')).toBe(true);

    const markdown = readFileSync(outMd, 'utf8');
    expect(markdown).toContain('Report-only');
    expect(markdown).toContain('change-package/v2');
    expect(markdown).toContain('Control-plane decision emitted: `false`');
  });

  it('normalizes the cross-agent fixture set without vendor-specific judgment vocabulary', () => {
    const dir = createTempDir();

    for (const fixtureCase of crossAgentFixtures) {
      const outJson = join(dir, `${fixtureCase.producerId}.json`);
      const outMd = join(dir, `${fixtureCase.producerId}.md`);
      const result = runNormalizer([
        '--input', resolve(fixtureCase.path),
        '--out-json', outJson,
        '--out-md', outMd,
        '--generated-at', '2026-06-21T00:00:00.000Z',
      ]);

      expect(result.status, `${fixtureCase.label}: ${result.stderr || result.stdout}`).toBe(0);
      const summary = JSON.parse(readFileSync(outJson, 'utf8'));
      validateSummary(summary);
      expect(summary.producer.id).toBe(fixtureCase.producerId);
      expect(summary.controlPlaneJudgment).toMatchObject({
        emitsDecision: false,
        result: 'not-emitted',
      });
      expect(summary.controlPlaneRouting.expectedArtifacts.map((entry: { artifact: string }) => entry.artifact)).toEqual(
        expect.arrayContaining(fixtureCase.expectedArtifacts),
      );
      expect(summary.controlPlaneRouting.reportOnlyFindings).not.toEqual(
        expect.arrayContaining([
          expect.objectContaining({ kind: 'unsupported-claim' }),
        ]),
      );

      const markdown = readFileSync(outMd, 'utf8');
      expect(markdown).toContain('Report-only');
      for (const artifact of fixtureCase.expectedArtifacts) {
        expect(markdown).toContain(artifact);
      }
      if ('expectedSummaryPath' in fixtureCase && fixtureCase.expectedSummaryPath) {
        expect(`${JSON.stringify(summary, null, 2)}\n`).toBe(
          readFileSync(resolve(fixtureCase.expectedSummaryPath), 'utf8'),
        );
      }
    }
  });

  it('keeps human waivers and formal scope metadata reviewable in raw fixtures', () => {
    const humanFixture = JSON.parse(readFileSync(resolve('fixtures/agents/evidence-adapters/human-waiver-review-output.json'), 'utf8'));
    const waivedClaim = humanFixture.claimsMentioned.find((claim: { expectedManifestStatus?: string }) =>
      claim.expectedManifestStatus === 'waived',
    );
    expect(waivedClaim).toBeTruthy();
    expect(waivedClaim).toMatchObject({
      claimId: expect.any(String),
      waiver: {
        owner: expect.any(String),
        reason: expect.any(String),
        expiresAt: expect.any(String),
        evidence: expect.any(String),
      },
    });

    const formalFixture = JSON.parse(readFileSync(resolve('fixtures/agents/evidence-adapters/formal/model-check-output.json'), 'utf8'));
    expect(formalFixture.formalScope.modeledClaims).toEqual(expect.arrayContaining([
      'reservation-never-drives-stock-negative',
    ]));
    expect(formalFixture.formalScope.outOfScope).toEqual(expect.arrayContaining([
      'production authorization middleware',
    ]));
    expect(formalFixture.assumptions.length).toBeGreaterThan(0);
    expect(formalFixture.counterexamples).toEqual(expect.arrayContaining([
      expect.objectContaining({ status: 'none-found' }),
    ]));
    expect(formalFixture.claimsMentioned).toEqual(expect.arrayContaining([
      expect.objectContaining({
        claimId: 'production-authorization-middleware-covered-by-model',
        expectedManifestStatus: 'partial',
      }),
    ]));
  });

  it('keeps unsupported claims and incomplete waiver metadata as report-only findings', () => {
    const dir = createTempDir();
    const input = join(dir, 'fixture.json');
    const outJson = join(dir, 'summary.json');
    const outMd = join(dir, 'summary.md');
    const fixture = JSON.parse(readFileSync(codexFixturePath, 'utf8'));
    fixture.producer = { ...fixture.producer, id: 'custom-agent' };
    fixture.claimsMentioned = [
      {
        claimId: 'bad-policy-result',
        rawAssertion: 'This should not become a policy decision.',
        targetArtifact: 'policy-decision/v1',
        expectedPolicyResult: 'tested',
        supportingEvidence: [],
      },
      {
        claimId: 'waiver-missing-expiry',
        rawAssertion: 'A manual exception exists.',
        targetArtifact: 'claim-evidence-manifest/v1',
        expectedManifestStatus: 'waived',
        supportingEvidence: ['maintainer note'],
        waiver: {
          owner: 'maintainer',
          reason: 'temporary exception',
        },
      },
      {
        claimId: 'policy-waiver-missing-metadata',
        rawAssertion: 'A policy exception exists.',
        targetArtifact: 'policy-decision/v1',
        expectedPolicyResult: 'waived',
        supportingEvidence: ['maintainer note'],
      },
    ];
    writeFileSync(input, JSON.stringify(fixture, null, 2));

    const result = runNormalizer([
      '--input', input,
      '--out-json', outJson,
      '--out-md', outMd,
      '--producer', 'override-agent',
      '--generated-at', '2026-06-20T00:00:00.000Z',
    ]);

    expect(result.status).toBe(0);
    const summary = JSON.parse(readFileSync(outJson, 'utf8'));
    validateSummary(summary);
    expect(summary.producer.id).toBe('override-agent');
    expect(summary.producer.fixtureProducerId).toBe('custom-agent');
    expect(summary.controlPlaneJudgment.result).toBe('not-emitted');
    expect(summary.controlPlaneRouting.reportOnlyFindings).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ kind: 'unsupported-claim' }),
        expect.objectContaining({ kind: 'waiver-metadata' }),
      ]),
    );
    expect(summary.controlPlaneRouting.missingEvidence).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ kind: 'claim-evidence', claimId: 'bad-policy-result' }),
        expect.objectContaining({ kind: 'waiver-metadata', claimId: 'waiver-missing-expiry' }),
        expect.objectContaining({ kind: 'waiver-metadata', claimId: 'policy-waiver-missing-metadata' }),
      ]),
    );
  });


  it('ignores a literal argument separator passed by package managers', () => {
    const dir = createTempDir();
    const outJson = join(dir, 'summary.json');
    const outMd = join(dir, 'summary.md');

    const result = runNormalizer([
      '--',
      '--input', codexFixturePath,
      '--out-json', outJson,
      '--out-md', outMd,
      '--generated-at', '2026-06-20T00:00:00.000Z',
    ]);

    expect(result.status).toBe(0);
    const summary = JSON.parse(readFileSync(outJson, 'utf8'));
    validateSummary(summary);
  });

  it('fails fast when the input fixture is missing', () => {
    const dir = createTempDir();
    const result = runNormalizer([
      '--input', join(dir, 'missing.json'),
      '--out-json', join(dir, 'summary.json'),
      '--out-md', join(dir, 'summary.md'),
    ]);

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('producer fixture not found');
  });
});
