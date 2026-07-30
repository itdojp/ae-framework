import fs from 'node:fs';
import path from 'node:path';

export const SCHEMA_VERSION = 'container-runtime-diagnostic/v1';

export const CLASSIFICATIONS = Object.freeze([
  'runtime-ready',
  'manifest-missing',
  'runtime-missing',
  'runtime-version-incompatible',
  'runtime-selection-invalid',
  'minimal-run-failed',
  'minimal-build-failed',
  'repository-build-failed',
  'archive-export-failed',
  'scan-failed',
  'sarif-missing',
  'sarif-malformed',
  'sarif-upload-failed',
]);

export const CHECK_IDS = Object.freeze([
  'podman-info',
  'manifest-detect',
  'direct-runtime-smoke',
  'minimal-run',
  'minimal-build',
  'repository-build',
  'image-user',
  'archive-export',
  'trivy-pull',
  'trivy-scan',
  'sarif-validate',
  'sarif-upload',
]);

const CHECK_PREREQUISITES = Object.freeze({
  'repository-build': 'manifest-detect',
  'image-user': 'repository-build',
  'archive-export': 'repository-build',
  'trivy-pull': 'archive-export',
  'trivy-scan': 'trivy-pull',
  'sarif-validate': 'trivy-scan',
  'sarif-upload': 'sarif-validate',
});

export const stagePrerequisite = (stage) => CHECK_PREREQUISITES[stage] ?? null;

const DIGEST_PINNED_IMAGE = /^[a-z0-9.-]+(?::[0-9]+)?\/[a-z0-9._/-]+(?::[A-Za-z0-9._-]+)?@sha256:[a-f0-9]{64}$/u;
const SYSTEM_EXECUTABLE = /^\/usr\/(?:local\/)?(?:bin|lib\/podman)\/[A-Za-z0-9._+-]+$/u;
const SEMVER = /\b(\d+\.\d+(?:\.\d+)?(?:[-+][0-9A-Za-z.-]+)?)\b/u;
const UTC_DATE_TIME = /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d{3})?Z$/u;

const closedKeys = (errors, value, allowed, label) => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) return;
  for (const key of Object.keys(value)) {
    if (!allowed.includes(key)) errors.push(`${label} contains unknown field ${key}`);
  }
};

export const renderDiagnostic = (diagnostic) => `${JSON.stringify(diagnostic, null, 2)}\n`;

export const parseToolVersion = (output) => {
  const match = String(output ?? '').match(SEMVER);
  return match?.[1] ?? null;
};

export const toolSourceForPath = (toolPath) => {
  if (typeof toolPath !== 'string') return 'unknown';
  if (toolPath.startsWith('/usr/local/')) return 'runner-bundle';
  if (toolPath.startsWith('/usr/')) return 'ubuntu-package';
  return 'unknown';
};

export const isAllowedSystemExecutable = (toolPath) => (
  typeof toolPath === 'string' && SYSTEM_EXECUTABLE.test(toolPath)
);

export const isDigestPinnedImage = (image) => (
  typeof image === 'string' && DIGEST_PINNED_IMAGE.test(image)
);

export const graphRootScope = (graphRoot, userId) => {
  if (typeof graphRoot !== 'string' || graphRoot.length === 0) return 'unknown';
  if (userId === 0 && graphRoot.startsWith('/var/')) return 'system-storage';
  if (userId !== 0 && (
    graphRoot.startsWith('/home/')
    || graphRoot.startsWith('/run/user/')
    || graphRoot.includes('/.local/share/containers/')
  )) return 'user-storage';
  return 'unknown';
};

export const sanitizePodmanInfo = (info, userId) => {
  const host = info?.host ?? info?.Host ?? {};
  const store = info?.store ?? info?.Store ?? {};
  const runtime = host?.ociRuntime ?? host?.OCIRuntime ?? {};
  return {
    effectiveRuntimePath: typeof runtime?.path === 'string' && isAllowedSystemExecutable(runtime.path)
      ? runtime.path
      : null,
    effectiveRuntimeVersion: parseToolVersion(runtime?.version),
    storageDriver: typeof store?.graphDriverName === 'string'
      ? store.graphDriverName.slice(0, 80)
      : null,
    graphRootScope: graphRootScope(store?.graphRoot, userId),
    cgroupManager: typeof host?.cgroupManager === 'string'
      ? host.cgroupManager.slice(0, 80)
      : null,
  };
};

export const stageFailureClassification = (stage, { outputState = null } = {}) => {
  if (stage === 'manifest-detect') return 'manifest-missing';
  if (stage === 'minimal-run') return 'minimal-run-failed';
  if (stage === 'minimal-build') return 'minimal-build-failed';
  if (stage === 'repository-build' || stage === 'image-user') return 'repository-build-failed';
  if (stage === 'archive-export') return 'archive-export-failed';
  if (stage === 'trivy-pull' || stage === 'trivy-scan') return 'scan-failed';
  if (stage === 'sarif-validate') {
    return outputState === 'malformed' ? 'sarif-malformed' : 'sarif-missing';
  }
  if (stage === 'sarif-upload') return 'sarif-upload-failed';
  return 'runtime-selection-invalid';
};

export const validateSarifDocument = (value) => {
  const errors = [];
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    return ['SARIF root must be an object'];
  }
  if (value.version !== '2.1.0') errors.push('SARIF version must be 2.1.0');
  if (!Array.isArray(value.runs) || value.runs.length === 0) {
    errors.push('SARIF runs must contain at least one run');
    return errors;
  }
  for (const [index, run] of value.runs.entries()) {
    if (!run || typeof run !== 'object' || Array.isArray(run)) {
      errors.push(`SARIF run ${index} must be an object`);
      continue;
    }
    if (!run.tool?.driver?.name || typeof run.tool.driver.name !== 'string') {
      errors.push(`SARIF run ${index} must bind tool.driver.name`);
    }
    if (!Array.isArray(run.results)) {
      errors.push(`SARIF run ${index} results must be an array`);
    }
  }
  return errors;
};

export const inspectArtifact = (repoRoot, relativePath, kind) => {
  if (typeof relativePath !== 'string' || relativePath.length === 0 || path.isAbsolute(relativePath)) {
    return { ok: false, state: 'missing', detail: 'missing-output' };
  }
  if (relativePath.includes('\\') || relativePath.split('/').includes('..')) {
    return { ok: false, state: 'missing', detail: 'missing-output' };
  }
  const artifactRoot = path.resolve(repoRoot, 'artifacts', 'container-security');
  const absolute = path.resolve(repoRoot, relativePath);
  const relative = path.relative(artifactRoot, absolute);
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    return { ok: false, state: 'missing', detail: 'missing-output' };
  }
  if (!fs.existsSync(absolute)) {
    return { ok: false, state: 'missing', detail: 'missing-output' };
  }
  const stat = fs.lstatSync(absolute);
  if (!stat.isFile() || stat.isSymbolicLink() || stat.size === 0) {
    return { ok: false, state: 'missing', detail: 'missing-output' };
  }
  if (kind !== 'sarif') return { ok: true, state: 'valid', detail: 'completed' };
  try {
    const parsed = JSON.parse(fs.readFileSync(absolute, 'utf8'));
    const errors = validateSarifDocument(parsed);
    if (errors.length > 0) return { ok: false, state: 'malformed', detail: 'malformed-output' };
  } catch {
    return { ok: false, state: 'malformed', detail: 'malformed-output' };
  }
  return { ok: true, state: 'valid', detail: 'completed' };
};

const duplicateValues = (values) => {
  const seen = new Set();
  const duplicates = new Set();
  for (const value of values) {
    if (seen.has(value)) duplicates.add(value);
    seen.add(value);
  }
  return [...duplicates];
};

export const validateDiagnosticSemantics = (diagnostic) => {
  const errors = [];
  if (!diagnostic || typeof diagnostic !== 'object' || Array.isArray(diagnostic)) {
    return ['diagnostic must be an object'];
  }
  closedKeys(errors, diagnostic, [
    'schemaVersion', 'generatedAt', 'status', 'classification', 'runner', 'packages', 'tools',
    'runtimeCandidates', 'selectedRuntime', 'podman', 'inputs', 'configuration', 'checks', 'limitations',
  ], 'diagnostic');
  if (!UTC_DATE_TIME.test(diagnostic.generatedAt ?? '') || Number.isNaN(Date.parse(diagnostic.generatedAt))) {
    errors.push('generatedAt must be an explicit UTC date-time');
  }
  if (diagnostic.schemaVersion !== SCHEMA_VERSION) errors.push(`schemaVersion must be ${SCHEMA_VERSION}`);
  if (!CLASSIFICATIONS.includes(diagnostic.classification)) errors.push('classification is not closed');
  if (!['pass', 'fail'].includes(diagnostic.status)) errors.push('status must be pass or fail');
  if (diagnostic.classification === 'runtime-ready' && diagnostic.status !== 'pass') {
    errors.push('runtime-ready requires status=pass');
  }
  if (diagnostic.classification !== 'runtime-ready' && diagnostic.status !== 'fail') {
    errors.push('failure classifications require status=fail');
  }
  if (!isDigestPinnedImage(diagnostic.inputs?.minimalImage)) errors.push('minimalImage must be digest pinned');
  if (!isDigestPinnedImage(diagnostic.inputs?.trivyImage)) errors.push('trivyImage must be digest pinned');
  if (![null, 'podman/Dockerfile', 'docker/Dockerfile'].includes(diagnostic.inputs?.repositoryDockerfile)) {
    errors.push('repositoryDockerfile must be a reviewed repository manifest path or null');
  }
  closedKeys(errors, diagnostic.runner, [
    'image', 'imageVersion', 'osRelease', 'kernel', 'architecture', 'userId', 'rootless', 'cgroupVersion',
  ], 'runner');
  closedKeys(errors, diagnostic.inputs, ['minimalImage', 'trivyImage', 'repositoryDockerfile'], 'inputs');
  closedKeys(errors, diagnostic.configuration, ['requestedRuntime', 'commandTimeoutMs', 'outputLimitBytes'], 'configuration');
  closedKeys(errors, diagnostic.podman, [
    'path', 'version', 'defaultRuntimePath', 'defaultRuntimeVersion', 'effectiveRuntimePath',
    'effectiveRuntimeVersion', 'storageDriver', 'graphRootScope', 'cgroupManager', 'runtimeConfig',
  ], 'podman');
  for (const entry of Array.isArray(diagnostic.podman?.runtimeConfig) ? diagnostic.podman.runtimeConfig : []) {
    closedKeys(errors, entry, ['source', 'entry'], 'runtimeConfig entry');
  }

  const packages = Array.isArray(diagnostic.packages) ? diagnostic.packages : [];
  if (packages.length !== 5) errors.push('package inventory must contain exactly five reviewed entries');
  const packageNames = packages.map((entry) => entry?.name);
  for (const name of packageNames) {
    if (!['podman', 'buildah', 'conmon', 'crun', 'runc'].includes(name)) errors.push(`unknown package inventory name: ${name ?? 'missing'}`);
  }
  for (const entry of packages) closedKeys(errors, entry, ['name', 'installedVersion', 'candidateVersion'], 'package entry');
  for (const duplicate of duplicateValues(packageNames)) errors.push(`duplicate package inventory: ${duplicate}`);

  const tools = Array.isArray(diagnostic.tools) ? diagnostic.tools : [];
  if (tools.length !== 5) errors.push('tool inventory must contain exactly five reviewed entries');
  const toolNames = tools.map((entry) => entry?.name);
  for (const name of toolNames) {
    if (!['podman', 'buildah', 'conmon', 'crun', 'runc'].includes(name)) errors.push(`unknown tool inventory name: ${name ?? 'missing'}`);
  }
  for (const entry of tools) closedKeys(errors, entry, ['name', 'path', 'version', 'source', 'available'], 'tool entry');
  for (const duplicate of duplicateValues(toolNames)) errors.push(`duplicate tool inventory: ${duplicate}`);
  for (const tool of tools) {
    if (tool?.available) {
      if (!isAllowedSystemExecutable(tool.path)) errors.push(`tool ${tool.name} path is not an allowed system executable`);
      if (!parseToolVersion(tool.version)) errors.push(`tool ${tool.name} version is malformed`);
      if (toolSourceForPath(tool.path) !== tool.source) errors.push(`tool ${tool.name} source does not match path`);
    } else if (tool?.path !== null || tool?.version !== null) {
      errors.push(`unavailable tool ${tool?.name ?? 'unknown'} must not claim path/version`);
    }
  }

  const candidates = Array.isArray(diagnostic.runtimeCandidates) ? diagnostic.runtimeCandidates : [];
  for (const duplicate of duplicateValues(candidates.map((entry) => entry?.path))) {
    errors.push(`duplicate runtime candidate: ${duplicate}`);
  }
  for (const candidate of candidates) {
    closedKeys(errors, candidate, [
      'name', 'path', 'version', 'source', 'available', 'selected', 'directSmoke', 'minimalRun',
    ], 'runtime candidate');
    closedKeys(errors, candidate?.directSmoke, ['status', 'exitCode', 'durationMs', 'detail'], 'direct runtime smoke');
    closedKeys(errors, candidate?.minimalRun, ['status', 'exitCode', 'durationMs', 'detail'], 'minimal runtime run');
    if (!isAllowedSystemExecutable(candidate?.path)) errors.push(`runtime candidate ${candidate?.name ?? 'unknown'} path is invalid`);
    if (candidate?.name !== path.basename(candidate?.path ?? '')) errors.push(`runtime candidate ${candidate?.name ?? 'unknown'} name does not match path`);
    if (candidate?.available && !parseToolVersion(candidate?.version)) errors.push(`runtime candidate ${candidate?.name ?? 'unknown'} version is malformed`);
    if (toolSourceForPath(candidate?.path) !== candidate?.source) errors.push(`runtime candidate ${candidate?.name ?? 'unknown'} source does not match path`);
  }
  const selectedCandidates = candidates.filter((entry) => entry?.selected === true);
  closedKeys(errors, diagnostic.selectedRuntime, ['name', 'path', 'version', 'source'], 'selectedRuntime');
  if (diagnostic.status === 'pass') {
    if (!diagnostic.selectedRuntime) errors.push('passing diagnostic requires selectedRuntime');
    if (selectedCandidates.length !== 1) errors.push('passing diagnostic requires exactly one selected candidate');
    const selected = selectedCandidates[0];
    if (selected) {
      if (!selected.available) errors.push('selected candidate must be available');
      if (selected.directSmoke?.status !== 'pass') errors.push('selected candidate direct smoke must pass');
      if (selected.minimalRun?.status !== 'pass') errors.push('selected candidate minimal run must pass');
      if (selected.path !== diagnostic.selectedRuntime?.path) errors.push('selectedRuntime path does not match candidate');
      if (selected.name !== diagnostic.selectedRuntime?.name) errors.push('selectedRuntime name does not match candidate');
      if (selected.version !== diagnostic.selectedRuntime?.version) errors.push('selectedRuntime version does not match candidate');
      if (selected.source !== diagnostic.selectedRuntime?.source) errors.push('selectedRuntime source does not match candidate');
      if (diagnostic.configuration?.requestedRuntime !== selected.name) errors.push('requestedRuntime does not match selected candidate');
      if (diagnostic.podman?.effectiveRuntimePath !== selected.path) errors.push('effective runtime path does not match selected candidate');
      if (diagnostic.podman?.effectiveRuntimeVersion !== selected.version) errors.push('effective runtime version does not match selected candidate');
    }
  } else if (selectedCandidates.length > 1) {
    errors.push('failing diagnostic must not select multiple candidates');
  }

  const podman = diagnostic.podman ?? {};
  if (podman.path !== null && !isAllowedSystemExecutable(podman.path)) errors.push('podman path is invalid');
  if (podman.path !== null && !parseToolVersion(podman.version)) errors.push('podman version is malformed');
  if ((podman.path === null) !== (podman.version === null)) errors.push('podman path/version must be both present or both null');
  for (const binding of ['defaultRuntime', 'effectiveRuntime']) {
    const runtimePath = podman[`${binding}Path`];
    const runtimeVersion = podman[`${binding}Version`];
    if ((runtimePath === null) !== (runtimeVersion === null)) errors.push(`${binding} path/version must be both present or both null`);
    if (runtimePath !== null && !isAllowedSystemExecutable(runtimePath)) errors.push(`${binding} path is invalid`);
    if (runtimeVersion !== null && !parseToolVersion(runtimeVersion)) errors.push(`${binding} version is malformed`);
  }

  const checks = Array.isArray(diagnostic.checks) ? diagnostic.checks : [];
  for (const check of checks) {
    closedKeys(errors, check, ['id', 'status', 'classification', 'exitCode', 'durationMs', 'detail'], 'check');
  }
  for (const duplicate of duplicateValues(checks.map((entry) => entry?.id))) {
    errors.push(`duplicate check id: ${duplicate}`);
  }
  for (const check of checks) {
    if (!CHECK_IDS.includes(check?.id)) errors.push(`unknown check id: ${check?.id ?? 'missing'}`);
    if (check?.status === 'pass' && (check.exitCode !== 0 || check.classification !== null)) {
      errors.push(`passing check ${check.id} must have exitCode=0 and no classification`);
    }
    if (check?.status === 'fail' && !CLASSIFICATIONS.includes(check.classification)) {
      errors.push(`failing check ${check.id} requires closed classification`);
    }
    if (check?.status === 'not-run' && check.exitCode !== null) {
      errors.push(`not-run check ${check.id} must not claim an exit code`);
    }
    if (check?.status === 'fail' && [
      'repository-build',
      'manifest-detect',
      'image-user',
      'archive-export',
      'trivy-pull',
      'trivy-scan',
      'sarif-validate',
      'sarif-upload',
    ].includes(check.id)) {
      const expected = stageFailureClassification(check.id, {
        outputState: check.detail === 'malformed-output' ? 'malformed' : 'missing',
      });
      if (check.classification !== expected) errors.push(`failing check ${check.id} classification must be ${expected}`);
    }
    const prerequisite = stagePrerequisite(check?.id);
    if (check?.status === 'pass' && prerequisite && !checks.some((entry) => (
      entry?.id === prerequisite && entry.status === 'pass'
    ))) {
      errors.push(`passing check ${check.id} requires ${prerequisite}=pass`);
    }
  }
  if (diagnostic.status === 'pass' && checks.some((check) => check?.status === 'fail')) {
    errors.push('passing diagnostic must not contain a failing check');
  }
  if (diagnostic.status === 'fail' && !checks.some((check) => (
    check?.status === 'fail' && check.classification === diagnostic.classification
  ))) {
    errors.push('failing diagnostic requires a check with the same primary classification');
  }

  if (diagnostic.status === 'pass') {
    const required = ['podman-info', 'direct-runtime-smoke', 'minimal-run', 'minimal-build'];
    for (const id of required) {
      if (!checks.some((check) => check.id === id && check.status === 'pass')) {
        errors.push(`passing diagnostic requires ${id}=pass`);
      }
    }
  }
  return errors;
};

export const upsertCheck = (diagnostic, check) => {
  const checks = Array.isArray(diagnostic.checks) ? [...diagnostic.checks] : [];
  const index = checks.findIndex((entry) => entry.id === check.id);
  if (index >= 0) checks[index] = check;
  else checks.push(check);
  return { ...diagnostic, checks };
};
