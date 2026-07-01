import { describe, expect, it } from 'vitest';
import { copyFileSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { randomUUID } from 'node:crypto';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/metrics/collect-req2run-metrics.mjs');
const fixturePath = resolve(repoRoot, 'fixtures/metrics/req2run/offline-input.json');
const expectedJsonPath = resolve(repoRoot, 'fixtures/metrics/req2run/expected.req2run-metrics.json');
const expectedMarkdownPath = resolve(repoRoot, 'fixtures/metrics/req2run/expected.req2run-metrics.md');
const schemaPath = resolve(repoRoot, 'schema/req2run-metrics.schema.json');
const generatedAt = '2026-07-01T00:00:00.000Z';

const runScript = (args: string[]) => spawnSync('node', [scriptPath, ...args], {
  cwd: repoRoot,
  encoding: 'utf8',
  timeout: 120_000,
});

const readJson = (filePath: string) => JSON.parse(readFileSync(filePath, 'utf8'));

function compileSchema() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(readJson(schemaPath));
}

describe('req2run metrics collector', () => {
  it('generates deterministic offline report-only req2run metrics without live APIs', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `req2run-metrics-test-${randomUUID()}`);
    const outputJson = join(outputRoot, 'req2run-metrics.json');
    const outputMd = join(outputRoot, 'req2run-metrics.md');

    try {
      const result = runScript([
        '--fixture', fixturePath,
        '--generated-at', generatedAt,
        '--output-json', outputJson,
        '--output-md', outputMd,
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(existsSync(outputJson)).toBe(true);
      expect(existsSync(outputMd)).toBe(true);

      const payload = readJson(outputJson);
      expect(payload).toEqual(readJson(expectedJsonPath));
      expect(payload.reportOnly).toBe(true);
      expect(payload.collectionBoundaries).toMatchObject({
        externalAgentApisCalled: false,
        agentVendorComparison: false,
      });
      expect(payload.metrics).toMatchObject({
        time_to_first_runnable_verification_minutes: { value: 34, unit: 'minutes' },
        spec_task_evidence_coverage: { numerator: 3, denominator: 4, ratio: 0.75 },
        deterministic_replay_pass_rate: { numerator: 2, denominator: 2, ratio: 1 },
        manual_intervention_count: { count: 1 },
        evidence_review_completeness: { numerator: 4, denominator: 5, ratio: 0.8 },
      });

      const validate = compileSchema();
      expect(validate(payload), JSON.stringify(validate.errors)).toBe(true);

      const markdown = readFileSync(outputMd, 'utf8');
      expect(markdown).toEqual(readFileSync(expectedMarkdownPath, 'utf8'));
      expect(markdown).toContain('Metrics evaluate ae-framework workflow effectiveness, not agent vendor quality.');
      expect(markdown).toContain('report-only adoption evidence');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('supports --no-write for read-only validation and rendering', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `req2run-no-write-test-${randomUUID()}`);
    const outputJson = join(outputRoot, 'req2run-metrics.json');
    const outputMd = join(outputRoot, 'req2run-metrics.md');

    try {
      const result = runScript([
        '--fixture', fixturePath,
        '--generated-at', generatedAt,
        '--output-json', outputJson,
        '--output-md', outputMd,
        '--no-write',
      ]);

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(existsSync(outputJson)).toBe(false);
      expect(existsSync(outputMd)).toBe(false);
      expect(result.stdout).toContain('Req2run metrics validated without writing files.');
      expect(result.stdout).not.toContain('Req2run metrics written.');
      expect(result.stdout).toContain('source: offline-fixture');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('rejects invalid calendar timestamps instead of normalizing them', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `req2run-invalid-date-test-${randomUUID()}`);
    const invalidGeneratedAt = runScript([
      '--fixture', fixturePath,
      '--generated-at', '2026-02-31T00:00:00.000Z',
      '--no-write',
    ]);

    expect(invalidGeneratedAt.status).not.toBe(0);
    expect(invalidGeneratedAt.stderr).toContain('--generated-at must be a valid RFC3339 date-time');

    try {
      mkdirSync(outputRoot, { recursive: true });
      const invalidTimelineFixture = join(outputRoot, 'invalid-timeline.json');
      const invalidTimelinePayload = readJson(fixturePath);
      invalidTimelinePayload.timeline.requirementAcceptedAt = '2026-02-31T00:00:00.000Z';
      writeFileSync(invalidTimelineFixture, `${JSON.stringify(invalidTimelinePayload, null, 2)}\n`, 'utf8');

      const invalidTimeline = runScript([
        '--fixture', invalidTimelineFixture,
        '--generated-at', generatedAt,
        '--no-write',
      ]);

      expect(invalidTimeline.status).not.toBe(0);
      expect(invalidTimeline.stderr).toContain('timeline.requirementAcceptedAt must be a valid RFC3339 date-time');

      const invalidVerificationFixture = join(outputRoot, 'invalid-verification-event.json');
      const invalidVerificationPayload = readJson(fixturePath);
      delete invalidVerificationPayload.timeline.firstRunnableVerificationAt;
      invalidVerificationPayload.verificationEvents = [{
        id: 'verify-lite',
        runnable: true,
        status: 'pass',
        completedAt: '2026-02-31T00:00:00.000Z',
      }];
      writeFileSync(invalidVerificationFixture, `${JSON.stringify(invalidVerificationPayload, null, 2)}\n`, 'utf8');

      const invalidVerification = runScript([
        '--fixture', invalidVerificationFixture,
        '--generated-at', generatedAt,
        '--no-write',
      ]);

      expect(invalidVerification.status).not.toBe(0);
      expect(invalidVerification.stderr).toContain('verificationEvents.verify-lite.completedAt must be a valid RFC3339 date-time');
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('runs when the CLI script path contains URL-encoded characters such as spaces', () => {
    const outputRoot = resolve(repoRoot, 'artifacts', `req2run cli path ${randomUUID()}`);
    const copiedScript = join(outputRoot, 'collect req2run metrics.mjs');
    const outputJson = join(outputRoot, 'req2run-metrics.json');
    const outputMd = join(outputRoot, 'req2run-metrics.md');

    try {
      mkdirSync(outputRoot, { recursive: true });
      copyFileSync(scriptPath, copiedScript);
      const result = spawnSync('node', [
        copiedScript,
        '--fixture', fixturePath,
        '--generated-at', generatedAt,
        '--output-json', outputJson,
        '--output-md', outputMd,
      ], {
        cwd: repoRoot,
        encoding: 'utf8',
        timeout: 120_000,
      });

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('Req2run metrics written.');
      expect(existsSync(outputJson)).toBe(true);
      expect(existsSync(outputMd)).toBe(true);
    } finally {
      rmSync(outputRoot, { recursive: true, force: true });
    }
  });

  it('rejects fixture paths outside the project root', () => {
    const result = runScript(['--fixture', '../outside-req2run-fixture.json', '--no-write']);

    expect(result.status).not.toBe(0);
    expect(result.stderr).toContain('--fixture must stay within --project-root');
  });
});
