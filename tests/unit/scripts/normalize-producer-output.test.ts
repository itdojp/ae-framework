import { describe, it, expect } from 'vitest';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const repoRoot = resolve('.');
const scriptPath = resolve('scripts/agents/normalize-producer-output.mjs');
const codexFixturePath = resolve('fixtures/agents/evidence-adapters/codex-cli-task-output.json');
const schemaPath = resolve('schema/producer-normalization-summary.schema.json');

function createTempDir() {
  const parent = join(repoRoot, '.codex-local', 'tmp');
  mkdirSync(parent, { recursive: true });
  return mkdtempSync(join(parent, 'normalize-producer-output-'));
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

    rmSync(dir, { recursive: true, force: true });
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
      ]),
    );

    rmSync(dir, { recursive: true, force: true });
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

    rmSync(dir, { recursive: true, force: true });
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

    rmSync(dir, { recursive: true, force: true });
  });
});
