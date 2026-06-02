import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import yaml from 'js-yaml';

const repoRoot = process.cwd();
const scriptPath = path.join(repoRoot, 'scripts/ci/validate-runtime-self-heal-trace-bundle.mjs');
const workflowPath = path.join(repoRoot, '.github/workflows/runtime-conformance-self-heal.yml');

const makeBundle = () => ({
  schemaVersion: 'ae-trace-bundle/v1',
  generatedAt: '2026-06-02T00:00:00.000Z',
  source: {
    environment: 'test',
    service: 'runtime-self-heal',
    input: {
      path: 'samples/conformance/sample-traces.json',
      format: 'json-events',
    },
    timeWindow: {
      start: '2026-06-02T00:00:00.000Z',
      end: '2026-06-02T00:00:01.000Z',
    },
  },
  events: [
    {
      traceId: 'trace-1',
      timestamp: '2026-06-02T00:00:00.000Z',
      actor: 'tester',
      event: 'request',
    },
  ],
  grouping: {
    by: 'traceId',
    traceCount: 1,
    traces: [
      {
        traceId: 'trace-1',
        eventCount: 1,
        firstTimestamp: '2026-06-02T00:00:00.000Z',
        lastTimestamp: '2026-06-02T00:00:00.000Z',
      },
    ],
  },
  redaction: {
    rules: [],
    redactedFieldCount: 0,
  },
  summary: {
    rawEventCount: 1,
    validEventCount: 1,
    invalidEventCount: 0,
    sampledOutCount: 0,
    emittedEventCount: 1,
  },
});

const writeJson = (file: string, value: unknown) => {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
};

const toRepoRelative = (absolutePath: string) => path.relative(repoRoot, absolutePath).split(path.sep).join('/');

describe('runtime conformance self-heal trace bundle security', () => {
  let sandbox: string;
  let outputPath: string;

  beforeEach(() => {
    sandbox = path.join(repoRoot, '.codex-local', 'tmp', `runtime-self-heal-${process.pid}-${Date.now()}`);
    outputPath = path.join(repoRoot, 'artifacts', 'observability', `runtime-self-heal-test-${process.pid}-${Date.now()}.json`);
    fs.mkdirSync(sandbox, { recursive: true });
  });

  afterEach(() => {
    fs.rmSync(sandbox, { recursive: true, force: true });
    fs.rmSync(outputPath, { force: true });
  });

  const runValidator = (input: string, allowedDir: string) => spawnSync(
    process.execPath,
    [
      scriptPath,
      '--input',
      input,
      '--allowed-dir',
      allowedDir,
      '--output',
      toRepoRelative(outputPath),
    ],
    {
      cwd: repoRoot,
      encoding: 'utf8',
    },
  );

  it('copies only schema-valid trace bundles from the allowed input directory', () => {
    const allowedDir = path.join(sandbox, 'allowed');
    const bundlePath = path.join(allowedDir, 'bundle.json');
    writeJson(bundlePath, makeBundle());

    const result = runValidator(toRepoRelative(bundlePath), toRepoRelative(allowedDir));

    expect(result.status).toBe(0);
    expect(fs.existsSync(outputPath)).toBe(true);
    expect(JSON.parse(fs.readFileSync(outputPath, 'utf8')).schemaVersion).toBe('ae-trace-bundle/v1');
  });

  it('rejects absolute paths, traversal, files outside the allowlist, symlinks, and invalid schemas', () => {
    const allowedDir = path.join(sandbox, 'allowed');
    const bundlePath = path.join(allowedDir, 'bundle.json');
    writeJson(bundlePath, makeBundle());

    const absolute = runValidator(bundlePath, toRepoRelative(allowedDir));
    expect(absolute.status).not.toBe(0);
    expect(absolute.stderr).toContain('repository-relative');

    const traversal = runValidator(`${toRepoRelative(allowedDir)}/../allowed/bundle.json`, toRepoRelative(allowedDir));
    expect(traversal.status).not.toBe(0);
    expect(traversal.stderr).toContain('parent traversal');

    const windowsDrive = runValidator('C:/runner/work/secret.json', toRepoRelative(allowedDir));
    expect(windowsDrive.status).not.toBe(0);
    expect(windowsDrive.stderr).toContain('repository-relative');

    const backslash = runValidator(`${toRepoRelative(allowedDir)}\\bundle.json`, toRepoRelative(allowedDir));
    expect(backslash.status).not.toBe(0);
    expect(backslash.stderr).toContain('POSIX-style separators');

    const controlChar = runValidator(`${toRepoRelative(allowedDir)}/bad\tname.json`, toRepoRelative(allowedDir));
    expect(controlChar.status).not.toBe(0);
    expect(controlChar.stderr).toContain('control characters');

    const outsideDir = path.join(sandbox, 'outside');
    const outsidePath = path.join(outsideDir, 'bundle.json');
    writeJson(outsidePath, makeBundle());
    const outside = runValidator(toRepoRelative(outsidePath), toRepoRelative(allowedDir));
    expect(outside.status).not.toBe(0);
    expect(outside.stderr).toContain('must be under');

    const invalidPath = path.join(allowedDir, 'invalid.json');
    writeJson(invalidPath, { schemaVersion: 'not-a-trace-bundle' });
    const invalid = runValidator(toRepoRelative(invalidPath), toRepoRelative(allowedDir));
    expect(invalid.status).not.toBe(0);
    expect(invalid.stderr).toContain('ae-trace-bundle/v1 schema');

    const symlinkPath = path.join(allowedDir, 'linked.json');
    fs.symlinkSync(bundlePath, symlinkPath);
    const symlink = runValidator(toRepoRelative(symlinkPath), toRepoRelative(allowedDir));
    expect(symlink.status).not.toBe(0);
    expect(symlink.stderr).toContain('must not traverse symlinks');

    const symlinkRoot = path.join(sandbox, 'allowed-link');
    fs.symlinkSync(allowedDir, symlinkRoot, 'dir');
    const symlinkAllowlistRoot = runValidator(`${toRepoRelative(symlinkRoot)}/bundle.json`, toRepoRelative(symlinkRoot));
    expect(symlinkAllowlistRoot.status).not.toBe(0);
    expect(symlinkAllowlistRoot.stderr).toContain('allowed-dir must not traverse symlinks');
  });

  it('workflow validates trace_bundle before artifact upload and avoids persisted checkout credentials', () => {
    const workflow = yaml.load(fs.readFileSync(workflowPath, 'utf8')) as any;
    expect(workflow.permissions).toMatchObject({
      contents: 'read',
      actions: 'read',
    });
    expect(workflow.permissions).not.toHaveProperty('pull-requests');

    const selfHeal = workflow.jobs?.['self-heal'];
    expect(selfHeal?.permissions).toMatchObject({
      contents: 'read',
      actions: 'read',
    });
    expect(selfHeal?.permissions).not.toHaveProperty('pull-requests');

    const steps = Array.isArray(selfHeal?.steps) ? selfHeal.steps : [];

    const checkout = steps.find((step: any) => step?.uses === 'actions/checkout@v4');
    expect(checkout?.with).toMatchObject({
      'persist-credentials': false,
    });

    const configStep = steps.find((step: any) => step?.name === 'Resolve self-heal configuration');
    expect(configStep?.run).toContain('TRACE_BUNDLE_INPUT_DIR=');
    expect(configStep?.run).toContain('trace_bundle_input_dir=');
    expect(configStep?.run).toContain('reject_output_control_chars');

    const pipelineStep = steps.find((step: any) => step?.name === 'Run runtime conformance self-heal pipeline');
    expect(pipelineStep?.run).toContain('scripts/ci/validate-runtime-self-heal-trace-bundle.mjs');
    expect(pipelineStep?.run).toContain('--allowed-dir "${TRACE_BUNDLE_INPUT_DIR}"');
    expect(pipelineStep?.run).not.toContain('cp "${TRACE_BUNDLE_INPUT}"');

    const preparePatchStep = steps.find((step: any) => step?.name === 'Prepare auto-fix patch artifact');
    expect(preparePatchStep?.run).toContain('git add -AN -- .');
    expect(preparePatchStep?.run).toContain('git diff --binary');
    expect(preparePatchStep?.run).toContain("':(exclude)artifacts/**'");

    const uploadPatchStep = steps.find((step: any) => step?.name === 'Upload auto-fix patch artifact');
    expect(uploadPatchStep?.uses).toBe('actions/upload-artifact@v4');
    expect(uploadPatchStep?.with?.['retention-days']).toBe(1);

    const createPrJob = workflow.jobs?.['create-pr'];
    expect(createPrJob?.permissions).toMatchObject({
      contents: 'write',
      'pull-requests': 'write',
      actions: 'read',
    });

    const createPrSteps = Array.isArray(createPrJob?.steps) ? createPrJob.steps : [];
    const createPrCheckout = createPrSteps.find((step: any) => step?.uses === 'actions/checkout@v4');
    expect(createPrCheckout?.with).toMatchObject({
      'persist-credentials': false,
    });

    const downloadPatchStep = createPrSteps.find((step: any) => step?.name === 'Download auto-fix patch artifact');
    expect(downloadPatchStep?.uses).toBe('actions/download-artifact@v4');

    const createPrStep = createPrSteps.find((step: any) => step?.name === 'Create PR for auto-fix changes');
    expect(createPrStep?.run).toContain('git apply --check --binary "${PATCH_PATH}"');
    expect(createPrStep?.run).toContain('git remote set-url origin "https://x-access-token:${GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git"');

    const uploadStep = steps.find((step: any) => step?.name === 'Upload self-heal artifacts');
    expect(uploadStep?.with?.['retention-days']).toBe(7);

    const selfHealReportStep = steps.find((step: any) => step?.name === 'Emit automation report');
    expect(selfHealReportStep?.if).toContain("steps.config.outputs.apply_fixes != 'true'");

    const finalReportStep = createPrSteps.find((step: any) => step?.name === 'Emit final automation report');
    expect(finalReportStep?.env?.PIPELINE_CREATED_PR).toContain('steps.pr.outputs.created');

    const uploadFinalReportStep = createPrSteps.find((step: any) => step?.name === 'Upload final automation report');
    expect(uploadFinalReportStep?.uses).toBe('actions/upload-artifact@v4');
    expect(uploadFinalReportStep?.with?.path).toBe('artifacts/automation/runtime-conformance-self-heal-report.json');
    expect(uploadFinalReportStep?.with?.['retention-days']).toBe(7);
  });
});
