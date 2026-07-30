import fs from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { describe, expect, it } from 'vitest';
import {
  inspectArtifact,
  isAllowedSystemExecutable,
  isDigestPinnedImage,
  parseToolVersion,
  renderDiagnostic,
  sanitizePodmanInfo,
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

describe('container-runtime-diagnostic/v1', () => {
  it.each([
    'valid-runc.container-runtime-diagnostic.json',
    'valid-crun.container-runtime-diagnostic.json',
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
    expect(stagePrerequisite('archive-export')).toBe('repository-build');
    expect(stagePrerequisite('trivy-pull')).toBe('archive-export');
    expect(stagePrerequisite('trivy-scan')).toBe('trivy-pull');
    expect(stagePrerequisite('podman-info')).toBeNull();
  });

  it('keeps a missing runtime as an explicit failing classification', () => {
    const value = fixture('valid-runc.container-runtime-diagnostic.json');
    value.status = 'fail';
    value.classification = 'runtime-missing';
    value.selectedRuntime = null;
    for (const candidate of value.runtimeCandidates) candidate.selected = false;
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
    ['minimal-build', 'minimal-build-failed', 'command-failed'],
    ['repository-build', 'repository-build-failed', 'command-failed'],
    ['image-user', 'repository-build-failed', 'unexpected-image-user'],
    ['archive-export', 'archive-export-failed', 'missing-output'],
    ['trivy-pull', 'scan-failed', 'command-failed'],
    ['trivy-scan', 'scan-failed', 'command-failed'],
    ['sarif-validate', 'sarif-missing', 'missing-output'],
    ['sarif-validate', 'sarif-malformed', 'malformed-output'],
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

  it('distinguishes missing, malformed, symlinked, and valid artifacts', () => {
    fs.mkdirSync(path.join(repoRoot, 'artifacts/container-security'), { recursive: true });
    const sandbox = fs.mkdtempSync(path.join(repoRoot, 'artifacts/container-security/test-'));
    try {
      const relativeRoot = path.relative(repoRoot, sandbox).split(path.sep).join('/');
      const archive = `${relativeRoot}/image.tar`;
      const sarif = `${relativeRoot}/results.sarif`;
      const malformed = `${relativeRoot}/malformed.sarif`;
      const symlink = `${relativeRoot}/linked.sarif`;
      fs.writeFileSync(path.resolve(repoRoot, archive), 'archive');
      fs.writeFileSync(path.resolve(repoRoot, sarif), JSON.stringify({
        version: '2.1.0',
        runs: [{ tool: { driver: { name: 'Trivy' } }, results: [] }],
      }));
      fs.writeFileSync(path.resolve(repoRoot, malformed), '{"version":"2.1.0","runs":[]}');
      fs.symlinkSync(path.resolve(repoRoot, sarif), path.resolve(repoRoot, symlink));

      expect(inspectArtifact(repoRoot, archive, 'archive').ok).toBe(true);
      expect(inspectArtifact(repoRoot, sarif, 'sarif').ok).toBe(true);
      expect(inspectArtifact(repoRoot, malformed, 'sarif')).toMatchObject({ ok: false, state: 'malformed' });
      expect(inspectArtifact(repoRoot, symlink, 'sarif')).toMatchObject({ ok: false, state: 'missing' });
      expect(inspectArtifact(repoRoot, `${relativeRoot}/missing.sarif`, 'sarif')).toMatchObject({ ok: false, state: 'missing' });
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
