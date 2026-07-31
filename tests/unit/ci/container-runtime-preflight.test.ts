import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { describe, expect, it, vi } from 'vitest';
import {
  applyRequestedRuntimeFailure,
  CHECK_IDS,
  DIAGNOSTIC_MAX_BYTES,
  finalizeDiagnostic,
  inspectArtifact,
  isCompleteContainerSecurityEvidence,
  isAllowedSystemExecutable,
  isDigestPinnedImage,
  orderedRequestedRuntimeCandidates,
  parseToolVersion,
  readBoundedStructuredArtifact,
  renderDiagnostic,
  resolveSafeArtifactFile,
  SARIF_MAX_BYTES,
  sanitizePodmanInfo,
  selectRequestedRuntimeFailure,
  stageFailureClassification,
  stagePrerequisite,
  validateDiagnosticSemantics,
  validateSarifDocument,
} from '../../../scripts/ci/lib/container-runtime-diagnostic.mjs';
import { runCommand } from '../../../scripts/ci/container-runtime-preflight.mjs';

const repoRoot = process.cwd();
const schema = JSON.parse(fs.readFileSync(
  path.resolve(repoRoot, 'schema/container-runtime-diagnostic-v1.schema.json'),
  'utf8',
));
const fixture = (name: string) => JSON.parse(fs.readFileSync(
  path.resolve(repoRoot, 'fixtures/container-runtime', name),
  'utf8',
));

const validateSchema = (() => {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
})();

const clone = <T>(value: T): T => structuredClone(value);

const runtimeCandidate = ({
  path: candidatePath = '/usr/local/bin/runc',
  version = '1.4.3',
  available = true,
  directSmoke = { status: 'pass', exitCode: 0, durationMs: 7, detail: 'completed' },
  minimalRun = { status: 'pass', exitCode: 0, durationMs: 310, detail: 'completed' },
}: Record<string, any> = {}) => ({
  name: path.basename(candidatePath),
  path: candidatePath,
  version: available ? version : null,
  source: candidatePath.startsWith('/usr/local/') ? 'runner-bundle' : 'ubuntu-package',
  available,
  selected: false,
  directSmoke,
  minimalRun,
});

const applyFailureSelection = (candidates: any[], requestedRuntime = 'runc') => {
  const value = fixture('valid-runc.container-runtime-diagnostic.json');
  value.status = 'fail';
  value.classification = 'runtime-version-incompatible';
  value.pipelineComplete = false;
  value.configuration.requestedRuntime = requestedRuntime;
  value.runtimeCandidates = candidates.map((candidate) => ({ ...candidate, selected: false }));
  value.selectedRuntime = null;
  value.podman.effectiveRuntimePath = null;
  value.podman.effectiveRuntimeVersion = null;
  value.checks = [
    { id: 'podman-info', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' },
    { id: 'manifest-detect', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' },
    { id: 'direct-runtime-smoke', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' },
    { id: 'minimal-run', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' },
    { id: 'minimal-build', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' },
  ];
  return applyRequestedRuntimeFailure(value);
};

describe('container-runtime-diagnostic/v1', () => {
  it.each([
    'valid-runc.container-runtime-diagnostic.json',
    'valid-crun.container-runtime-diagnostic.json',
    'valid-complete-runc.container-runtime-diagnostic.json',
  ])('accepts reviewed %s evidence', (name) => {
    const value = fixture(name);
    expect(validateSchema(value), validateSchema.errors?.map((error) => error.message).join('; ')).toBe(true);
    expect(validateDiagnosticSemantics(value)).toEqual([]);
  });

  it('renders deterministic bytes for identical evidence', () => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    expect(renderDiagnostic(value)).toBe(renderDiagnostic(clone(value)));
    expect(renderDiagnostic(value).endsWith('\n')).toBe(true);
  });

  describe('requested runtime failure selection', () => {
    it('preserves a direct smoke failure when the minimal run passes', () => {
      const candidate = runtimeCandidate({
        directSmoke: { status: 'fail', exitCode: 42, durationMs: 315, detail: 'command-failed' },
        minimalRun: { status: 'pass', exitCode: 0, durationMs: 927, detail: 'completed' },
      });
      const value = applyFailureSelection([candidate]);

      expect(value).toMatchObject({
        status: 'fail',
        classification: 'runtime-version-incompatible',
        pipelineComplete: false,
        selectedRuntime: null,
      });
      expect(value.runtimeCandidates[0]).toMatchObject({
        name: 'runc', path: '/usr/local/bin/runc', version: '1.4.3', source: 'runner-bundle', available: true, selected: false,
      });
      expect(value.checks.find((check: any) => check.id === 'direct-runtime-smoke')).toEqual({
        id: 'direct-runtime-smoke', status: 'fail', classification: 'runtime-version-incompatible', exitCode: 42, durationMs: 315, detail: 'command-failed',
      });
      expect(value.checks.find((check: any) => check.id === 'minimal-run')).toEqual({
        id: 'minimal-run', status: 'pass', classification: null, exitCode: 0, durationMs: 927, detail: 'completed',
      });
      expect(validateSchema(value), validateSchema.errors?.map((error) => error.message).join('; ')).toBe(true);
      expect(validateDiagnosticSemantics(value)).toEqual([]);
      expect(renderDiagnostic(value)).toBe(renderDiagnostic(applyFailureSelection([clone(candidate)])));
    });

    it.each([
      ['timeout', { status: 'fail', exitCode: null, durationMs: 300_000, detail: 'timeout' }],
      ['nonzero exit', { status: 'fail', exitCode: 125, durationMs: 444, detail: 'command-failed' }],
    ])('preserves a minimal run %s after direct smoke passed', (_case, minimalRun) => {
      const value = applyFailureSelection([runtimeCandidate({ minimalRun })]);
      expect(value.checks.find((check: any) => check.id === 'direct-runtime-smoke')).toMatchObject({
        status: 'pass', exitCode: 0, durationMs: 7, detail: 'completed', classification: null,
      });
      expect(value.checks.find((check: any) => check.id === 'minimal-run')).toEqual({
        id: 'minimal-run', classification: 'runtime-version-incompatible', ...minimalRun,
      });
      expect(value.pipelineComplete).toBe(false);
      expect(validateSchema(value), validateSchema.errors?.map((error) => error.message).join('; ')).toBe(true);
      expect(validateDiagnosticSemantics(value)).toEqual([]);
    });

    it('preserves invalid version invocation evidence as direct smoke failure', () => {
      const value = applyFailureSelection([runtimeCandidate({
        available: false,
        directSmoke: { status: 'fail', exitCode: 9, durationMs: 211, detail: 'version-invalid' },
        minimalRun: { status: 'not-run', exitCode: null, durationMs: 0, detail: 'runtime-unavailable' },
      })]);
      expect(value.runtimeCandidates[0]).toMatchObject({ available: false, version: null, selected: false });
      expect(value.checks.find((check: any) => check.id === 'direct-runtime-smoke')).toMatchObject({
        status: 'fail', exitCode: 9, durationMs: 211, detail: 'version-invalid', classification: 'runtime-version-incompatible',
      });
      expect(value.checks.find((check: any) => check.id === 'minimal-run')).toMatchObject({
        status: 'not-run', exitCode: null, durationMs: 0, detail: 'runtime-unavailable', classification: null,
      });
      expect(validateSchema(value), validateSchema.errors?.map((error) => error.message).join('; ')).toBe(true);
      expect(validateDiagnosticSemantics(value)).toEqual([]);
    });

    it('selects the farthest-progressed failure, then applies stable path preference', () => {
      const localDirectFailure = runtimeCandidate({
        path: '/usr/local/bin/runc',
        directSmoke: { status: 'fail', exitCode: 42, durationMs: 315, detail: 'command-failed' },
        minimalRun: { status: 'pass', exitCode: 0, durationMs: 927, detail: 'completed' },
      });
      const packageMinimalFailure = runtimeCandidate({
        path: '/usr/bin/runc',
        version: '1.3.6',
        directSmoke: { status: 'pass', exitCode: 0, durationMs: 12, detail: 'completed' },
        minimalRun: { status: 'fail', exitCode: null, durationMs: 800, detail: 'timeout' },
      });
      const farther = selectRequestedRuntimeFailure([localDirectFailure, packageMinimalFailure], 'runc');
      expect(farther.candidate?.path).toBe('/usr/bin/runc');
      expect(farther.checks.find((check) => check.id === 'minimal-run')).toMatchObject({ durationMs: 800, detail: 'timeout' });

      const localMinimalFailure = runtimeCandidate({
        path: '/usr/local/bin/runc',
        minimalRun: { status: 'fail', exitCode: 126, durationMs: 600, detail: 'command-failed' },
      });
      const preferred = selectRequestedRuntimeFailure([packageMinimalFailure, localMinimalFailure], 'runc');
      expect(preferred.candidate?.path).toBe('/usr/local/bin/runc');
      expect(orderedRequestedRuntimeCandidates([packageMinimalFailure, localMinimalFailure], 'runc').map((entry) => entry.path))
        .toEqual(['/usr/local/bin/runc', '/usr/bin/runc']);
      expect(selectRequestedRuntimeFailure([packageMinimalFailure, localMinimalFailure], 'runc'))
        .toEqual(selectRequestedRuntimeFailure([packageMinimalFailure, localMinimalFailure], 'runc'));
    });

    it('records a missing requested runtime without fabricated execution evidence', () => {
      const value = applyFailureSelection([runtimeCandidate({ path: '/usr/bin/crun', version: '1.14.1' })], 'runc');
      expect(value).toMatchObject({
        status: 'fail', classification: 'runtime-missing', pipelineComplete: false, selectedRuntime: null,
      });
      expect(value.checks.find((check: any) => check.id === 'direct-runtime-smoke')).toEqual({
        id: 'direct-runtime-smoke', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'runtime-unavailable',
      });
      expect(value.checks.find((check: any) => check.id === 'minimal-run')).toEqual({
        id: 'minimal-run', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected',
      });
      expect(validateSchema(value), validateSchema.errors?.map((error) => error.message).join('; ')).toBe(true);
      expect(validateDiagnosticSemantics(value)).toEqual([]);
    });

    it('preserves both actual failures for the deterministically chosen candidate', () => {
      const value = applyFailureSelection([runtimeCandidate({
        directSmoke: { status: 'fail', exitCode: 17, durationMs: 218, detail: 'malformed-output' },
        minimalRun: { status: 'fail', exitCode: 125, durationMs: 731, detail: 'command-failed' },
      })]);
      expect(value.checks.find((check: any) => check.id === 'direct-runtime-smoke')).toMatchObject({
        status: 'fail', exitCode: 17, durationMs: 218, detail: 'malformed-output',
      });
      expect(value.checks.find((check: any) => check.id === 'minimal-run')).toMatchObject({
        status: 'fail', exitCode: 125, durationMs: 731, detail: 'command-failed',
      });
      expect(validateDiagnosticSemantics(value)).toEqual([]);
    });

    it('detects substituted check identity and zeroed candidate duration', () => {
      const value = applyFailureSelection([runtimeCandidate({
        directSmoke: { status: 'fail', exitCode: 42, durationMs: 315, detail: 'command-failed' },
        minimalRun: { status: 'pass', exitCode: 0, durationMs: 927, detail: 'completed' },
      })]);
      const substituted = clone(value);
      Object.assign(substituted.checks.find((check: any) => check.id === 'direct-runtime-smoke'), {
        status: 'pass', classification: null, exitCode: 0, durationMs: 927, detail: 'completed',
      });
      Object.assign(substituted.checks.find((check: any) => check.id === 'minimal-run'), {
        status: 'fail', classification: 'runtime-version-incompatible', exitCode: null, durationMs: 0, detail: 'command-failed',
      });
      expect(validateDiagnosticSemantics(substituted)).toContain('check direct-runtime-smoke must preserve the selected runtime candidate result');
      expect(validateDiagnosticSemantics(substituted)).toContain('check minimal-run must preserve the selected runtime candidate result');

      const zeroed = clone(value);
      zeroed.checks.find((check: any) => check.id === 'direct-runtime-smoke').durationMs = 0;
      expect(validateDiagnosticSemantics(zeroed)).toContain('check direct-runtime-smoke must preserve the selected runtime candidate result');
    });
  });

  it('rejects unknown fields and malformed generation time at the runtime trust boundary', () => {
    const unknown = fixture('valid-runc.container-runtime-diagnostic.json');
    unknown.injected = true;
    expect(validateSchema(unknown)).toBe(false);
    expect(validateDiagnosticSemantics(unknown)).toContain('diagnostic contains unknown field injected');

    const malformedTime = fixture('valid-runc.container-runtime-diagnostic.json');
    malformedTime.generatedAt = 'today';
    expect(validateDiagnosticSemantics(malformedTime)).toContain('generatedAt must be an explicit UTC date-time');
  });

  it('accepts the reviewed Docker fallback and represents a missing manifest explicitly', () => {
    const dockerFallback = fixture('valid-runc.container-runtime-diagnostic.json');
    dockerFallback.inputs.repositoryDockerfile = 'docker/Dockerfile';
    expect(validateSchema(dockerFallback)).toBe(true);
    expect(validateDiagnosticSemantics(dockerFallback)).toEqual([]);

    const missing = fixture('valid-runc.container-runtime-diagnostic.json');
    missing.status = 'fail';
    missing.classification = 'manifest-missing';
    missing.inputs.repositoryDockerfile = null;
    missing.checks.push({
      id: 'manifest-detect',
      status: 'fail',
      classification: 'manifest-missing',
      exitCode: null,
      durationMs: 0,
      detail: 'manifest-missing',
    });
    expect(validateSchema(missing)).toBe(true);
    expect(validateDiagnosticSemantics(missing)).toEqual([]);
  });

  it('declares stage prerequisites for fail-closed execution ordering', () => {
    expect(stagePrerequisite('repository-build')).toBe('manifest-detect');
    expect(stagePrerequisite('image-user')).toBe('repository-build');
    expect(stagePrerequisite('archive-export')).toBe('image-user');
    expect(stagePrerequisite('trivy-pull')).toBe('archive-export');
    expect(stagePrerequisite('trivy-scan')).toBe('trivy-pull');
    expect(stagePrerequisite('podman-info')).toBeNull();
  });

  it('keeps a missing runtime as an explicit failing classification', () => {
    const value = applyFailureSelection([]);
    Object.assign(value.tools.find((tool: any) => tool.name === 'podman'), {
      path: null, version: null, source: 'unknown', available: false,
    });
    Object.assign(value.podman, {
      path: null,
      version: null,
      defaultRuntimePath: null,
      defaultRuntimeVersion: null,
      effectiveRuntimePath: null,
      effectiveRuntimeVersion: null,
    });
    value.checks[0] = {
      id: 'podman-info',
      status: 'fail',
      classification: 'runtime-missing',
      exitCode: null,
      durationMs: 0,
      detail: 'runtime-unavailable',
    };
    expect(validateSchema(value)).toBe(true);
    expect(validateDiagnosticSemantics(value)).toEqual([]);
  });

  it('rejects selected runtime path substitution', () => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    value.selectedRuntime.path = '/usr/bin/runc';
    expect(validateDiagnosticSemantics(value)).toContain('selectedRuntime path does not match candidate');
  });

  it('rejects runtime source, requested kind, and effective-version mutations', () => {
    const source = fixture('valid-runc.container-runtime-diagnostic.json');
    source.selectedRuntime.source = 'ubuntu-package';
    expect(validateDiagnosticSemantics(source)).toContain('selectedRuntime source does not match candidate');

    const requested = fixture('valid-runc.container-runtime-diagnostic.json');
    requested.configuration.requestedRuntime = 'crun';
    expect(validateDiagnosticSemantics(requested)).toContain('requestedRuntime does not match selected candidate');

    const effective = fixture('valid-runc.container-runtime-diagnostic.json');
    effective.podman.effectiveRuntimeVersion = '1.3.3';
    expect(validateDiagnosticSemantics(effective)).toContain('effective runtime version does not match selected candidate');
  });

  it('requires closed default runtime path/version provenance', () => {
    const missingVersion = fixture('valid-runc.container-runtime-diagnostic.json');
    missingVersion.podman.defaultRuntimeVersion = null;
    expect(validateDiagnosticSemantics(missingVersion)).toContain('defaultRuntime path/version must be both present or both null');

    const substituted = fixture('valid-runc.container-runtime-diagnostic.json');
    substituted.podman.defaultRuntimePath = '/workspace/crun';
    expect(validateSchema(substituted)).toBe(false);
    expect(validateDiagnosticSemantics(substituted)).toContain('defaultRuntime path is invalid');
  });

  it('rejects malformed and unavailable selected runtime inventory', () => {
    const malformed = fixture('valid-runc.container-runtime-diagnostic.json');
    malformed.tools.find((tool: any) => tool.name === 'runc').version = 'unknown';
    expect(validateDiagnosticSemantics(malformed)).toContain('tool runc version is malformed');

    const unavailable = fixture('valid-runc.container-runtime-diagnostic.json');
    const selected = unavailable.runtimeCandidates.find((candidate: any) => candidate.selected);
    selected.available = false;
    expect(validateDiagnosticSemantics(unavailable)).toContain('selected candidate must be available');
  });

  it('rejects duplicate runtime paths and stage identities', () => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    value.runtimeCandidates.push(clone(value.runtimeCandidates[0]));
    value.checks.push(clone(value.checks[0]));
    const errors = validateDiagnosticSemantics(value);
    expect(errors.some((error) => error.startsWith('duplicate runtime candidate:'))).toBe(true);
    expect(errors).toContain('duplicate check id: podman-info');
  });

  it('rejects a pass classification containing a failing downstream check', () => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    value.checks.push({
      id: 'repository-build',
      status: 'fail',
      classification: 'repository-build-failed',
      exitCode: 125,
      durationMs: 10,
      detail: 'command-failed',
    });
    expect(validateDiagnosticSemantics(value)).toContain('passing diagnostic must not contain a failing check');
  });

  it.each([
    ['manifest-detect', 'manifest-missing', 'manifest-missing'],
    ['minimal-run', 'minimal-run-failed', 'command-failed'],
    ['minimal-run', 'minimal-run-failed', 'timeout'],
    ['minimal-build', 'minimal-build-failed', 'command-failed'],
    ['repository-build', 'repository-build-failed', 'command-failed'],
    ['image-user', 'repository-build-failed', 'unexpected-image-user'],
    ['archive-export', 'archive-export-failed', 'missing-output'],
    ['trivy-pull', 'scan-failed', 'command-failed'],
    ['trivy-scan', 'scan-failed', 'command-failed'],
    ['sarif-validate', 'sarif-missing', 'missing-output'],
    ['sarif-validate', 'sarif-malformed', 'malformed-output'],
    ['sarif-validate', 'sarif-malformed', 'oversized-output'],
    ['sarif-upload', 'sarif-upload-failed', 'upload-skipped'],
  ])('accepts exact %s failure evidence without converting its reason', (id, classification, detail) => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    value.status = 'fail';
    value.classification = classification;
    const failedCheck = { id, status: 'fail', classification, exitCode: null, durationMs: 0, detail };
    const existing = value.checks.findIndex((check: any) => check.id === id);
    if (existing >= 0) value.checks[existing] = failedCheck;
    else value.checks.push(failedCheck);
    expect(validateSchema(value), validateSchema.errors?.map((error) => error.message).join('; ')).toBe(true);
    expect(validateDiagnosticSemantics(value)).toEqual([]);
  });

  it('rejects failure-class conversion and a fabricated primary classification', () => {
    const converted = fixture('valid-runc.container-runtime-diagnostic.json');
    converted.status = 'fail';
    converted.classification = 'repository-build-failed';
    converted.checks.push({
      id: 'trivy-scan',
      status: 'fail',
      classification: 'repository-build-failed',
      exitCode: 1,
      durationMs: 10,
      detail: 'command-failed',
    });
    const errors = validateDiagnosticSemantics(converted);
    expect(errors).toContain('failing check trivy-scan classification must be scan-failed');

    const fabricated = fixture('valid-runc.container-runtime-diagnostic.json');
    fabricated.status = 'fail';
    fabricated.classification = 'scan-failed';
    expect(validateDiagnosticSemantics(fabricated)).toContain('failing diagnostic requires a check with the same primary classification');
  });

  it('rejects successful downstream evidence when its prerequisite was not observed', () => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    value.checks.push({
      id: 'sarif-upload',
      status: 'pass',
      classification: null,
      exitCode: 0,
      durationMs: 1,
      detail: 'completed',
    });
    expect(validateDiagnosticSemantics(value)).toContain('passing check sarif-upload requires sarif-validate=pass');
  });

  it.each([
    [{ status: 'pass', exitCode: 0, durationMs: 1, detail: 'timeout', classification: null }, 'pass requires detail=completed'],
    [{ status: 'pass', exitCode: null, durationMs: 1, detail: 'completed', classification: null }, 'pass requires exitCode=0'],
    [{ status: 'pass', exitCode: 0, durationMs: 1, detail: 'completed', classification: 'runtime-selection-invalid' }, 'pass requires classification=null'],
    [{ status: 'not-run', exitCode: null, durationMs: 0, detail: 'not-selected', classification: 'runtime-selection-invalid' }, 'not-run requires classification=null'],
    [{ status: 'not-run', exitCode: 0, durationMs: 0, detail: 'not-selected', classification: null }, 'not-run requires exitCode=null'],
    [{ status: 'not-run', exitCode: null, durationMs: 1, detail: 'not-selected', classification: null }, 'not-run requires durationMs=0'],
    [{ status: 'not-run', exitCode: null, durationMs: 0, detail: 'completed', classification: null }, 'not-run detail is invalid'],
    [{ status: 'fail', exitCode: 1, durationMs: 1, detail: 'completed', classification: 'runtime-selection-invalid' }, 'fail detail is invalid'],
    [{ status: 'fail', exitCode: 1, durationMs: 1, detail: 'not-selected', classification: 'runtime-selection-invalid' }, 'fail detail is invalid'],
    [{ status: 'fail', exitCode: 1, durationMs: 1, detail: 'command-failed', classification: null }, 'fail requires closed classification'],
  ])('rejects illegal top-level check status combination %#', (mutation, expected) => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    value.checks[0] = { id: 'podman-info', ...mutation };
    expect(validateDiagnosticSemantics(value).some((error) => error.includes(expected))).toBe(true);
  });

  it.each([
    [{ available: false, selected: false, directSmoke: { status: 'pass', exitCode: 0, durationMs: 1, detail: 'completed' } }, 'must not pass'],
    [{ available: false, selected: true }, 'must be available'],
    [{ directSmoke: { status: 'pass', exitCode: null, durationMs: 1, detail: 'completed' } }, 'pass requires exitCode=0'],
    [{ minimalRun: { status: 'not-run', exitCode: 0, durationMs: 0, detail: 'runtime-unavailable' } }, 'not-run requires exitCode=null'],
    [{ minimalRun: { status: 'not-run', exitCode: null, durationMs: 1, detail: 'runtime-unavailable' } }, 'not-run requires durationMs=0'],
    [{ minimalRun: { status: 'not-run', exitCode: null, durationMs: 0, detail: 'completed' } }, 'not-run detail is invalid'],
  ])('rejects illegal runtime candidate status combination %#', (mutation, expected) => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    const candidate = value.runtimeCandidates.find((entry: any) => entry.selected);
    Object.assign(candidate, mutation);
    expect(validateDiagnosticSemantics(value).some((error) => error.includes(expected))).toBe(true);
  });

  it.each([
    ['missing', (value: any) => { value.checks = value.checks.filter((check: any) => check.id !== 'image-user'); }],
    ['not-run', (value: any) => { value.checks.find((check: any) => check.id === 'image-user').status = 'not-run'; value.checks.find((check: any) => check.id === 'image-user').exitCode = null; value.checks.find((check: any) => check.id === 'image-user').durationMs = 0; value.checks.find((check: any) => check.id === 'image-user').detail = 'not-selected'; }],
    ['fail', (value: any) => { const check = value.checks.find((entry: any) => entry.id === 'image-user'); Object.assign(check, { status: 'fail', classification: 'repository-build-failed', exitCode: 1, detail: 'unexpected-image-user' }); }],
  ])('rejects archive-export=pass when image-user is %s', (_state, mutate) => {
    const value = fixture('valid-complete-runc.container-runtime-diagnostic.json');
    value.pipelineComplete = false;
    mutate(value);
    expect(validateDiagnosticSemantics(value)).toContain('passing check archive-export requires image-user=pass');
  });

  it('separates runtime readiness from explicit pipeline completion', () => {
    const preflightOnly = fixture('valid-runc.container-runtime-diagnostic.json');
    expect(preflightOnly.pipelineComplete).toBe(false);
    expect(validateDiagnosticSemantics(preflightOnly)).toEqual([]);
    expect(isCompleteContainerSecurityEvidence(preflightOnly)).toBe(false);

    const pending = fixture('valid-complete-runc.container-runtime-diagnostic.json');
    pending.pipelineComplete = false;
    const finalized = finalizeDiagnostic(pending);
    expect(finalized.pipelineComplete).toBe(true);
    expect(finalized.checks).toHaveLength(CHECK_IDS.length);
    expect(validateDiagnosticSemantics(finalized)).toEqual([]);
    expect(isCompleteContainerSecurityEvidence(finalized)).toBe(true);
  });

  it('finalizes a persisted diagnostic through the closed CLI boundary', () => {
    fs.mkdirSync(path.join(repoRoot, 'artifacts/container-security'), { recursive: true });
    const sandbox = fs.mkdtempSync(path.join(repoRoot, 'artifacts/container-security/finalize-'));
    try {
      const report = path.join(sandbox, 'diagnostic.json');
      const relativeReport = path.relative(repoRoot, report).split(path.sep).join('/');
      const pending = fixture('valid-complete-runc.container-runtime-diagnostic.json');
      pending.pipelineComplete = false;
      fs.writeFileSync(report, renderDiagnostic(pending));
      execFileSync(process.execPath, [
        'scripts/ci/container-runtime-preflight.mjs',
        'finalize',
        '--report',
        relativeReport,
      ], { cwd: repoRoot, stdio: 'pipe' });
      const persisted = JSON.parse(fs.readFileSync(report, 'utf8'));
      expect(persisted.pipelineComplete).toBe(true);
      expect(isCompleteContainerSecurityEvidence(persisted)).toBe(true);
    } finally {
      fs.rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects duplicate persisted checks at the CLI read boundary', () => {
    fs.mkdirSync(path.join(repoRoot, 'artifacts/container-security'), { recursive: true });
    const sandbox = fs.mkdtempSync(path.join(repoRoot, 'artifacts/container-security/duplicate-'));
    try {
      const report = path.join(sandbox, 'diagnostic.json');
      const relativeReport = path.relative(repoRoot, report).split(path.sep).join('/');
      const tampered = fixture('valid-complete-runc.container-runtime-diagnostic.json');
      tampered.pipelineComplete = false;
      tampered.checks.push(clone(tampered.checks[0]));
      fs.writeFileSync(report, renderDiagnostic(tampered));
      expect(() => execFileSync(process.execPath, [
        'scripts/ci/container-runtime-preflight.mjs',
        'validate',
        '--report',
        relativeReport,
      ], { cwd: repoRoot, stdio: 'pipe' })).toThrow();
    } finally {
      fs.rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it.each([
    ['missing image-user', (value: any) => { value.checks = value.checks.filter((check: any) => check.id !== 'image-user'); }],
    ['missing sarif-upload', (value: any) => { value.checks = value.checks.filter((check: any) => check.id !== 'sarif-upload'); }],
    ['not-run stage', (value: any) => { Object.assign(value.checks.find((check: any) => check.id === 'image-user'), { status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' }); }],
    ['duplicate stage', (value: any) => { value.checks.push(clone(value.checks[0])); }],
    ['failed stage', (value: any) => { Object.assign(value.checks.find((check: any) => check.id === 'trivy-scan'), { status: 'fail', classification: 'scan-failed', exitCode: 1, detail: 'command-failed' }); value.status = 'fail'; value.classification = 'scan-failed'; }],
  ])('fails closed while finalizing a diagnostic with %s', (_case, mutate) => {
    const value = fixture('valid-complete-runc.container-runtime-diagnostic.json');
    value.pipelineComplete = false;
    mutate(value);
    expect(() => finalizeDiagnostic(value)).toThrow(/contract-invalid/u);
  });

  it('keeps failure diagnostics valid and non-finalized', () => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    value.status = 'fail';
    value.classification = 'scan-failed';
    value.pipelineComplete = false;
    value.checks.push({
      id: 'trivy-scan', status: 'fail', classification: 'scan-failed', exitCode: 1, durationMs: 10, detail: 'command-failed',
    });
    expect(validateDiagnosticSemantics(value)).toEqual([]);
    expect(isCompleteContainerSecurityEvidence(value)).toBe(false);
  });

  it.each([
    ['manifest-detect', {}, 'manifest-missing'],
    ['minimal-run', {}, 'minimal-run-failed'],
    ['minimal-build', {}, 'minimal-build-failed'],
    ['repository-build', {}, 'repository-build-failed'],
    ['archive-export', {}, 'archive-export-failed'],
    ['trivy-pull', {}, 'scan-failed'],
    ['trivy-scan', {}, 'scan-failed'],
    ['sarif-validate', { outputState: 'missing' }, 'sarif-missing'],
    ['sarif-validate', { outputState: 'malformed' }, 'sarif-malformed'],
    ['sarif-upload', {}, 'sarif-upload-failed'],
  ])('maps %s failures without status conversion', (stage, details, expected) => {
    expect(stageFailureClassification(stage, details)).toBe(expected);
  });

  it('sanitizes podman info without retaining graph-root paths', () => {
    const sanitized = sanitizePodmanInfo({
      host: {
        cgroupManager: 'cgroupfs',
        ociRuntime: {
          path: '/usr/local/bin/runc',
          version: 'runc version 1.4.3\nspec: 1.3.0',
        },
      },
      store: {
        graphDriverName: 'overlay',
        graphRoot: '/home/runner/.local/share/containers/storage',
      },
    }, 1001);
    expect(sanitized).toEqual({
      effectiveRuntimePath: '/usr/local/bin/runc',
      effectiveRuntimeVersion: '1.4.3',
      storageDriver: 'overlay',
      graphRootScope: 'user-storage',
      cgroupManager: 'cgroupfs',
    });
    expect(JSON.stringify(sanitized)).not.toContain('/home/runner');
  });

  it('records default and selected runtime bindings separately', () => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    expect(value.podman.defaultRuntimePath).toBe('/usr/bin/crun');
    expect(value.podman.defaultRuntimeVersion).toBe('1.14.1');
    expect(value.podman.effectiveRuntimePath).toBe('/usr/local/bin/runc');
    expect(value.selectedRuntime.path).toBe(value.podman.effectiveRuntimePath);
  });

  it('requires digest-pinned images and allowlisted system executable paths', () => {
    expect(isDigestPinnedImage('docker.io/library/alpine:3.22.1@sha256:4bcff63911fcb4448bd4fdacec207030997caf25e9bea4045fa6c8c44de311d1')).toBe(true);
    expect(isDigestPinnedImage('docker.io/library/alpine:latest')).toBe(false);
    expect(isAllowedSystemExecutable('/usr/local/bin/runc')).toBe(true);
    expect(isAllowedSystemExecutable('/workspace/bin/runc')).toBe(false);
    expect(parseToolVersion('runc version 1.4.3')).toBe('1.4.3');
    expect(parseToolVersion('unknown')).toBeNull();
  });

  it('rejects path traversal, symlink components, and non-file artifacts', () => {
    fs.mkdirSync(path.join(repoRoot, 'artifacts/container-security'), { recursive: true });
    const sandbox = fs.mkdtempSync(path.join(repoRoot, 'artifacts/container-security/test-'));
    const external = fs.mkdtempSync(path.join(path.dirname(repoRoot), 'container-artifact-external-'));
    try {
      const relativeRoot = path.relative(repoRoot, sandbox).split(path.sep).join('/');
      const archive = `${relativeRoot}/image.tar`;
      const sarif = `${relativeRoot}/results.sarif`;
      const malformed = `${relativeRoot}/malformed.sarif`;
      const finalSymlink = `${relativeRoot}/linked.sarif`;
      const externalLink = `${relativeRoot}/external-link`;
      const internalDirectory = path.resolve(sandbox, 'internal-directory');
      const internalLink = `${relativeRoot}/internal-link`;
      const empty = `${relativeRoot}/empty.sarif`;
      fs.writeFileSync(path.resolve(repoRoot, archive), 'archive');
      fs.writeFileSync(path.resolve(repoRoot, sarif), JSON.stringify({
        version: '2.1.0',
        runs: [{ tool: { driver: { name: 'Trivy' } }, results: [] }],
      }));
      fs.writeFileSync(path.resolve(repoRoot, malformed), '{"version":"2.1.0","runs":[]}');
      fs.writeFileSync(path.resolve(repoRoot, empty), '');
      fs.writeFileSync(path.join(external, 'outside.sarif'), fs.readFileSync(path.resolve(repoRoot, sarif)));
      fs.symlinkSync(path.resolve(repoRoot, sarif), path.resolve(repoRoot, finalSymlink));
      fs.symlinkSync(external, path.resolve(repoRoot, externalLink));
      fs.mkdirSync(internalDirectory);
      fs.writeFileSync(path.join(internalDirectory, 'inside.sarif'), fs.readFileSync(path.resolve(repoRoot, sarif)));
      fs.symlinkSync(internalDirectory, path.resolve(repoRoot, internalLink));

      expect(inspectArtifact(repoRoot, archive, 'archive').ok).toBe(true);
      expect(inspectArtifact(repoRoot, sarif, 'sarif').ok).toBe(true);
      expect(inspectArtifact(repoRoot, malformed, 'sarif')).toMatchObject({ ok: false, state: 'malformed' });
      expect(inspectArtifact(repoRoot, finalSymlink, 'sarif')).toMatchObject({ ok: false, detail: 'path-invalid' });
      expect(inspectArtifact(repoRoot, `${externalLink}/outside.sarif`, 'sarif')).toMatchObject({ ok: false, detail: 'path-invalid' });
      expect(inspectArtifact(repoRoot, `${internalLink}/inside.sarif`, 'sarif')).toMatchObject({ ok: false, detail: 'path-invalid' });
      expect(inspectArtifact(repoRoot, `${relativeRoot}/../escape.sarif`, 'sarif')).toMatchObject({ ok: false, detail: 'path-invalid' });
      expect(inspectArtifact(repoRoot, path.resolve(repoRoot, sarif), 'sarif')).toMatchObject({ ok: false, detail: 'path-invalid' });
      expect(inspectArtifact(repoRoot, sarif.replaceAll('/', '\\'), 'sarif')).toMatchObject({ ok: false, detail: 'path-invalid' });
      expect(inspectArtifact(repoRoot, `${relativeRoot}/missing.sarif`, 'sarif')).toMatchObject({ ok: false, detail: 'missing-output' });
      expect(inspectArtifact(repoRoot, relativeRoot, 'archive')).toMatchObject({ ok: false, detail: 'missing-output' });
      expect(inspectArtifact(repoRoot, empty, 'sarif')).toMatchObject({ ok: false, detail: 'missing-output' });
      expect(resolveSafeArtifactFile(repoRoot, archive, { maxBytes: 7 }).ok).toBe(true);
    } finally {
      fs.rmSync(sandbox, { recursive: true, force: true });
      fs.rmSync(external, { recursive: true, force: true });
    }
  });

  it('bounds structured artifact reads before parsing without truncation', () => {
    fs.mkdirSync(path.join(repoRoot, 'artifacts/container-security'), { recursive: true });
    const sandbox = fs.mkdtempSync(path.join(repoRoot, 'artifacts/container-security/size-'));
    try {
      const relativeRoot = path.relative(repoRoot, sandbox).split(path.sep).join('/');
      const exactPath = path.join(sandbox, 'exact.sarif');
      const oversizedPath = path.join(sandbox, 'oversized.sarif');
      const exactDiagnosticPath = path.join(sandbox, 'exact-diagnostic.json');
      const oversizedDiagnosticPath = path.join(sandbox, 'oversized-diagnostic.json');
      const prefix = '{"version":"2.1.0","runs":[{"tool":{"driver":{"name":"';
      const suffix = '"}},"results":[]}]}';
      const padding = SARIF_MAX_BYTES - Buffer.byteLength(prefix + suffix, 'utf8');
      fs.writeFileSync(exactPath, `${prefix}${'x'.repeat(padding)}${suffix}`);
      fs.writeFileSync(oversizedPath, Buffer.alloc(SARIF_MAX_BYTES + 1, 0x7b));
      const diagnosticPrefix = '{"padding":"';
      const diagnosticSuffix = '"}';
      const diagnosticPadding = DIAGNOSTIC_MAX_BYTES - Buffer.byteLength(diagnosticPrefix + diagnosticSuffix, 'utf8');
      fs.writeFileSync(exactDiagnosticPath, `${diagnosticPrefix}${'x'.repeat(diagnosticPadding)}${diagnosticSuffix}`);
      fs.writeFileSync(oversizedDiagnosticPath, Buffer.alloc(DIAGNOSTIC_MAX_BYTES + 1, 0x7b));

      expect(fs.statSync(exactPath).size).toBe(SARIF_MAX_BYTES);
      expect(inspectArtifact(repoRoot, `${relativeRoot}/exact.sarif`, 'sarif').ok).toBe(true);
      expect(fs.statSync(exactDiagnosticPath).size).toBe(DIAGNOSTIC_MAX_BYTES);
      expect(readBoundedStructuredArtifact(repoRoot, `${relativeRoot}/exact-diagnostic.json`, 'diagnostic').ok).toBe(true);

      const readSpy = vi.spyOn(fs, 'readFileSync');
      try {
        expect(inspectArtifact(repoRoot, `${relativeRoot}/oversized.sarif`, 'sarif')).toMatchObject({
          ok: false,
          state: 'malformed',
          detail: 'oversized-output',
        });
        expect(readBoundedStructuredArtifact(repoRoot, `${relativeRoot}/oversized-diagnostic.json`, 'diagnostic')).toMatchObject({
          ok: false,
          state: 'malformed',
          detail: 'oversized-output',
        });
        expect(readSpy).not.toHaveBeenCalled();
      } finally {
        readSpy.mockRestore();
      }
      expect(resolveSafeArtifactFile(repoRoot, `${relativeRoot}/exact.sarif`, { maxBytes: SARIF_MAX_BYTES }).ok).toBe(true);
      expect(resolveSafeArtifactFile(repoRoot, `${relativeRoot}/oversized.sarif`, { maxBytes: SARIF_MAX_BYTES }))
        .toMatchObject({ ok: false, detail: 'oversized-output' });
      expect(DIAGNOSTIC_MAX_BYTES).toBe(256 * 1024);

      const reportPath = path.join(sandbox, 'oversized-failure-diagnostic.json');
      const relativeReport = path.relative(repoRoot, reportPath).split(path.sep).join('/');
      const pending = fixture('valid-complete-runc.container-runtime-diagnostic.json');
      pending.pipelineComplete = false;
      pending.checks = pending.checks.filter((check: any) => check.id !== 'sarif-upload');
      fs.writeFileSync(reportPath, renderDiagnostic(pending));
      expect(() => execFileSync(process.execPath, [
        'scripts/ci/container-runtime-preflight.mjs',
        'validate-artifact',
        '--report',
        relativeReport,
        '--stage',
        'sarif-validate',
        '--path',
        `${relativeRoot}/oversized.sarif`,
        '--kind',
        'sarif',
      ], { cwd: repoRoot, stdio: 'pipe' })).toThrow();
      const failure = JSON.parse(fs.readFileSync(reportPath, 'utf8'));
      expect(failure).toMatchObject({ status: 'fail', classification: 'sarif-malformed', pipelineComplete: false });
      expect(failure.checks.find((check: any) => check.id === 'sarif-validate')).toMatchObject({
        status: 'fail', classification: 'sarif-malformed', detail: 'oversized-output',
      });
      expect(validateDiagnosticSemantics(failure)).toEqual([]);
    } finally {
      fs.rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects malformed SARIF and accepts a closed Trivy-compatible surface', () => {
    expect(validateSarifDocument({ version: '2.1.0', runs: [] })).toContain('SARIF runs must contain at least one run');
    expect(validateSarifDocument({
      version: '2.1.0',
      runs: [{ tool: { driver: { name: 'Trivy' } }, results: [] }],
    })).toEqual([]);
  });

  it('bounds command execution time and preserves timeout classification', async () => {
    const result = await runCommand(process.execPath, ['-e', 'setTimeout(() => {}, 10000)'], {
      cwd: repoRoot,
      timeoutMs: 50,
      outputLimitBytes: 1024,
    });
    expect(result.timedOut).toBe(true);
    expect(result.durationMs).toBeLessThan(3000);
  });
});
