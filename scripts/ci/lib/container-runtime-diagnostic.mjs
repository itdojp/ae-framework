import fs from 'node:fs';
import path from 'node:path';

export const SCHEMA_VERSION = 'container-runtime-diagnostic/v1';
export const CONTAINER_ARTIFACT_ROOT = 'artifacts/container-security';
export const DIAGNOSTIC_MAX_BYTES = 256 * 1024;
export const SARIF_MAX_BYTES = 16 * 1024 * 1024;

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
  'archive-export': 'image-user',
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

const artifactFailure = (state, detail) => ({ ok: false, state, detail });

const insideCanonicalRoot = (root, candidate) => {
  const relative = path.relative(root, candidate);
  return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
};

/**
 * Resolve an existing artifact without following any symlink component.
 *
 * This is a bounded pre-read validation, not an atomic open operation. Callers
 * must not claim protection from a concurrent filesystem mutation after this
 * function returns.
 */
export const resolveSafeArtifactFile = (repoRoot, relativePath, {
  maxBytes = null,
  requireNonEmpty = true,
} = {}) => {
  if (typeof relativePath !== 'string' || relativePath.length === 0 || path.isAbsolute(relativePath)) {
    return artifactFailure('missing', 'path-invalid');
  }
  const segments = relativePath.split('/');
  if (relativePath.includes('\\') || segments.some((segment) => segment === '' || segment === '.' || segment === '..')) {
    return artifactFailure('missing', 'path-invalid');
  }

  const root = path.resolve(repoRoot, CONTAINER_ARTIFACT_ROOT);
  const absolute = path.resolve(repoRoot, ...segments);
  const textualRelative = path.relative(root, absolute);
  if (textualRelative === '' || textualRelative.startsWith('..') || path.isAbsolute(textualRelative)) {
    return artifactFailure('missing', 'path-invalid');
  }

  try {
    const rootStat = fs.lstatSync(root);
    if (!rootStat.isDirectory() || rootStat.isSymbolicLink()) {
      return artifactFailure('missing', 'path-invalid');
    }
    const canonicalRoot = fs.realpathSync(root);
    if (!insideCanonicalRoot(fs.realpathSync(path.resolve(repoRoot)), canonicalRoot)) {
      return artifactFailure('missing', 'path-invalid');
    }

    let current = root;
    const artifactSegments = textualRelative.split(path.sep).filter(Boolean);
    for (const segment of artifactSegments) {
      current = path.join(current, segment);
      const component = fs.lstatSync(current);
      if (component.isSymbolicLink()) return artifactFailure('missing', 'path-invalid');
    }

    const stat = fs.lstatSync(absolute);
    if (!stat.isFile() || stat.isSymbolicLink()) return artifactFailure('missing', 'missing-output');
    if (requireNonEmpty && stat.size === 0) return artifactFailure('missing', 'missing-output');
    if (maxBytes !== null && stat.size > maxBytes) return artifactFailure('malformed', 'oversized-output');

    const canonicalParent = fs.realpathSync(path.dirname(absolute));
    const canonicalFile = fs.realpathSync(absolute);
    if (!insideCanonicalRoot(canonicalRoot, canonicalParent) || !insideCanonicalRoot(canonicalRoot, canonicalFile)) {
      return artifactFailure('missing', 'path-invalid');
    }
    return { ok: true, state: 'valid', detail: 'completed', absolute, stat };
  } catch {
    return artifactFailure('missing', 'missing-output');
  }
};

export const readBoundedStructuredArtifact = (repoRoot, relativePath, kind) => {
  if (!['diagnostic', 'sarif'].includes(kind)) return artifactFailure('malformed', 'malformed-output');
  const maxBytes = kind === 'diagnostic' ? DIAGNOSTIC_MAX_BYTES : SARIF_MAX_BYTES;
  const resolved = resolveSafeArtifactFile(repoRoot, relativePath, { maxBytes });
  if (!resolved.ok) return resolved;
  try {
    const value = JSON.parse(fs.readFileSync(resolved.absolute, 'utf8'));
    if (kind === 'sarif') {
      const errors = validateSarifDocument(value);
      if (errors.length > 0) return artifactFailure('malformed', 'malformed-output');
    }
    return { ...resolved, value };
  } catch {
    return artifactFailure('malformed', 'malformed-output');
  }
};

export const inspectArtifact = (repoRoot, relativePath, kind) => {
  if (kind === 'sarif') return readBoundedStructuredArtifact(repoRoot, relativePath, 'sarif');
  if (kind === 'archive') return resolveSafeArtifactFile(repoRoot, relativePath);
  return artifactFailure('malformed', 'malformed-output');
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

const compareRuntimeCandidatePreference = (left, right) => {
  const leftLocal = String(left?.path ?? '').startsWith('/usr/local/') ? 0 : 1;
  const rightLocal = String(right?.path ?? '').startsWith('/usr/local/') ? 0 : 1;
  if (leftLocal !== rightLocal) return leftLocal - rightLocal;
  const leftPath = String(left?.path ?? '');
  const rightPath = String(right?.path ?? '');
  if (leftPath === rightPath) return 0;
  return leftPath < rightPath ? -1 : 1;
};

export const orderedRequestedRuntimeCandidates = (candidates, requestedRuntime) => (
  (Array.isArray(candidates) ? candidates : [])
    .filter((candidate) => candidate?.name === requestedRuntime)
    .sort(compareRuntimeCandidatePreference)
);

const runtimeFailureCheck = (id, result, classification) => ({
  id,
  status: result?.status,
  classification: result?.status === 'fail' ? classification : null,
  exitCode: result?.exitCode,
  durationMs: result?.durationMs,
  detail: result?.detail,
});

/**
 * Select the authoritative requested-runtime failure evidence.
 *
 * Candidates that passed direct smoke but failed minimal run take precedence,
 * because they reached the later reviewed stage. Within a stage, the same
 * /usr/local-before-/usr path preference used for success selection applies.
 */
export const selectRequestedRuntimeFailure = (candidates, requestedRuntime) => {
  const requested = orderedRequestedRuntimeCandidates(candidates, requestedRuntime);
  if (requested.length === 0) {
    return {
      classification: 'runtime-missing',
      candidate: null,
      checks: [
        {
          id: 'direct-runtime-smoke',
          status: 'not-run',
          classification: null,
          exitCode: null,
          durationMs: 0,
          detail: 'runtime-unavailable',
        },
        {
          id: 'minimal-run',
          status: 'not-run',
          classification: null,
          exitCode: null,
          durationMs: 0,
          detail: 'not-selected',
        },
      ],
    };
  }

  const candidate = requested.find((entry) => (
    entry?.directSmoke?.status === 'pass' && entry?.minimalRun?.status === 'fail'
  )) ?? requested.find((entry) => entry?.directSmoke?.status === 'fail') ?? requested[0];
  const classification = 'runtime-version-incompatible';
  return {
    classification,
    candidate,
    checks: [
      runtimeFailureCheck('direct-runtime-smoke', candidate?.directSmoke, classification),
      runtimeFailureCheck('minimal-run', candidate?.minimalRun, classification),
    ],
  };
};

export const applyRequestedRuntimeFailure = (diagnostic) => {
  const selection = selectRequestedRuntimeFailure(
    diagnostic?.runtimeCandidates,
    diagnostic?.configuration?.requestedRuntime,
  );
  let updated = {
    ...diagnostic,
    status: 'fail',
    classification: selection.classification,
    pipelineComplete: false,
    selectedRuntime: null,
    runtimeCandidates: (Array.isArray(diagnostic?.runtimeCandidates) ? diagnostic.runtimeCandidates : [])
      .map((candidate) => ({ ...candidate, selected: false })),
  };
  for (const check of selection.checks) updated = upsertCheck(updated, check);
  return updated;
};

const resultBindingMatches = (check, expected) => (
  check?.status === expected?.status
  && check?.classification === expected?.classification
  && check?.exitCode === expected?.exitCode
  && check?.durationMs === expected?.durationMs
  && check?.detail === expected?.detail
);

const validateResultSemantics = (errors, result, label, {
  classification = false,
  allowRuntimeUnavailableNotRun = false,
} = {}) => {
  if (!result || typeof result !== 'object' || Array.isArray(result)) {
    errors.push(`${label} must be an object`);
    return;
  }
  if (!['pass', 'fail', 'not-run'].includes(result.status)) {
    errors.push(`${label} status is not closed`);
    return;
  }
  if (!Number.isInteger(result.durationMs) || result.durationMs < 0 || result.durationMs > 3_600_000) {
    errors.push(`${label} durationMs is invalid`);
  }
  if (result.status === 'pass') {
    if (result.exitCode !== 0) errors.push(`${label} pass requires exitCode=0`);
    if (result.detail !== 'completed') errors.push(`${label} pass requires detail=completed`);
    if (classification && result.classification !== null) errors.push(`${label} pass requires classification=null`);
  } else if (result.status === 'not-run') {
    if (result.exitCode !== null) errors.push(`${label} not-run requires exitCode=null`);
    if (result.durationMs !== 0) errors.push(`${label} not-run requires durationMs=0`);
    const allowedDetails = allowRuntimeUnavailableNotRun
      ? ['not-selected', 'runtime-unavailable']
      : ['not-selected'];
    if (!allowedDetails.includes(result.detail)) errors.push(`${label} not-run detail is invalid`);
    if (classification && result.classification !== null) errors.push(`${label} not-run requires classification=null`);
  } else {
    if (result.detail === 'completed' || result.detail === 'not-selected') {
      errors.push(`${label} fail detail is invalid`);
    }
    if (classification && !CLASSIFICATIONS.includes(result.classification)) {
      errors.push(`${label} fail requires closed classification`);
    }
  }
};

export const validateDiagnosticSemantics = (diagnostic) => {
  const errors = [];
  if (!diagnostic || typeof diagnostic !== 'object' || Array.isArray(diagnostic)) {
    return ['diagnostic must be an object'];
  }
  closedKeys(errors, diagnostic, [
    'schemaVersion', 'generatedAt', 'status', 'classification', 'pipelineComplete', 'runner', 'packages', 'tools',
    'runtimeCandidates', 'selectedRuntime', 'podman', 'inputs', 'configuration', 'checks', 'limitations',
  ], 'diagnostic');
  if (!UTC_DATE_TIME.test(diagnostic.generatedAt ?? '') || Number.isNaN(Date.parse(diagnostic.generatedAt))) {
    errors.push('generatedAt must be an explicit UTC date-time');
  }
  if (diagnostic.schemaVersion !== SCHEMA_VERSION) errors.push(`schemaVersion must be ${SCHEMA_VERSION}`);
  if (!CLASSIFICATIONS.includes(diagnostic.classification)) errors.push('classification is not closed');
  if (!['pass', 'fail'].includes(diagnostic.status)) errors.push('status must be pass or fail');
  if (typeof diagnostic.pipelineComplete !== 'boolean') errors.push('pipelineComplete must be boolean');
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
    validateResultSemantics(errors, candidate?.directSmoke, `runtime candidate ${candidate?.name ?? 'unknown'} directSmoke`, {
      allowRuntimeUnavailableNotRun: true,
    });
    validateResultSemantics(errors, candidate?.minimalRun, `runtime candidate ${candidate?.name ?? 'unknown'} minimalRun`, {
      allowRuntimeUnavailableNotRun: true,
    });
    if (!isAllowedSystemExecutable(candidate?.path)) errors.push(`runtime candidate ${candidate?.name ?? 'unknown'} path is invalid`);
    if (candidate?.name !== path.basename(candidate?.path ?? '')) errors.push(`runtime candidate ${candidate?.name ?? 'unknown'} name does not match path`);
    if (candidate?.available && !parseToolVersion(candidate?.version)) errors.push(`runtime candidate ${candidate?.name ?? 'unknown'} version is malformed`);
    if (!candidate?.available && candidate?.version !== null) errors.push(`unavailable runtime candidate ${candidate?.name ?? 'unknown'} must not claim version`);
    if (!candidate?.available && (candidate?.directSmoke?.status === 'pass' || candidate?.minimalRun?.status === 'pass')) {
      errors.push(`unavailable runtime candidate ${candidate?.name ?? 'unknown'} must not pass`);
    }
    if (candidate?.selected && !candidate?.available) errors.push(`selected runtime candidate ${candidate?.name ?? 'unknown'} must be available`);
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
  if (['runtime-missing', 'runtime-version-incompatible'].includes(diagnostic.classification)) {
    if (selectedCandidates.length !== 0) errors.push('runtime discovery failure must not select a candidate');
    if (diagnostic.selectedRuntime !== null) errors.push('runtime discovery failure requires selectedRuntime=null');
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
    validateResultSemantics(errors, check, `check ${check?.id ?? 'unknown'}`, {
      classification: true,
      allowRuntimeUnavailableNotRun: (
        ['runtime-missing', 'runtime-version-incompatible'].includes(diagnostic.classification)
        && ['direct-runtime-smoke', 'minimal-run'].includes(check?.id)
      ),
    });
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
        outputState: ['malformed-output', 'oversized-output'].includes(check.detail) ? 'malformed' : 'missing',
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
  )) && diagnostic.classification !== 'runtime-missing') {
    errors.push('failing diagnostic requires a check with the same primary classification');
  }

  if (['runtime-missing', 'runtime-version-incompatible'].includes(diagnostic.classification)) {
    const selection = selectRequestedRuntimeFailure(candidates, diagnostic.configuration?.requestedRuntime);
    if (selection.classification !== diagnostic.classification) {
      errors.push(`runtime failure classification must be ${selection.classification}`);
    }
    for (const expected of selection.checks) {
      const actual = checks.find((check) => check?.id === expected.id);
      if (!resultBindingMatches(actual, expected)) {
        errors.push(`check ${expected.id} must preserve the selected runtime candidate result`);
      }
    }
  }

  if (diagnostic.status === 'pass') {
    const required = ['podman-info', 'direct-runtime-smoke', 'minimal-run', 'minimal-build'];
    for (const id of required) {
      if (!checks.some((check) => check.id === id && check.status === 'pass')) {
        errors.push(`passing diagnostic requires ${id}=pass`);
      }
    }
  }
  if (diagnostic.pipelineComplete) {
    if (diagnostic.status !== 'pass' || diagnostic.classification !== 'runtime-ready') {
      errors.push('pipelineComplete requires a passing runtime-ready diagnostic');
    }
    if (checks.length !== CHECK_IDS.length) errors.push('pipelineComplete requires exactly all reviewed checks');
    for (const id of CHECK_IDS) {
      if (checks.filter((check) => check?.id === id && check.status === 'pass').length !== 1) {
        errors.push(`pipelineComplete requires ${id}=pass exactly once`);
      }
    }
  }
  return errors;
};

export const finalizeDiagnostic = (diagnostic) => {
  if (diagnostic?.pipelineComplete === true) throw new Error('contract-invalid: diagnostic is already finalized');
  const finalized = { ...diagnostic, pipelineComplete: true };
  const errors = validateDiagnosticSemantics(finalized);
  if (errors.length > 0) throw new Error(`contract-invalid: ${errors.slice(0, 5).join('; ')}`);
  return finalized;
};

export const isCompleteContainerSecurityEvidence = (diagnostic) => (
  diagnostic?.pipelineComplete === true
  && diagnostic.status === 'pass'
  && diagnostic.classification === 'runtime-ready'
  && validateDiagnosticSemantics(diagnostic).length === 0
);

export const upsertCheck = (diagnostic, check) => {
  const checks = Array.isArray(diagnostic.checks) ? [...diagnostic.checks] : [];
  const index = checks.findIndex((entry) => entry.id === check.id);
  if (index >= 0) checks[index] = check;
  else checks.push(check);
  return { ...diagnostic, checks };
};
