#!/usr/bin/env node
import { spawn } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';
import {
  DIAGNOSTIC_MAX_BYTES,
  finalizeDiagnostic,
  inspectArtifact,
  isAllowedSystemExecutable,
  isDigestPinnedImage,
  parseToolVersion,
  readBoundedStructuredArtifact,
  renderDiagnostic,
  sanitizePodmanInfo,
  SCHEMA_VERSION,
  stageFailureClassification,
  stagePrerequisite,
  toolSourceForPath,
  upsertCheck,
  validateDiagnosticSemantics,
} from './lib/container-runtime-diagnostic.mjs';

const DEFAULT_REPORT = 'artifacts/container-security/container-runtime-diagnostic.json';
const DEFAULT_MINIMAL_IMAGE = 'docker.io/library/alpine:3.22.1@sha256:4bcff63911fcb4448bd4fdacec207030997caf25e9bea4045fa6c8c44de311d1';
const DEFAULT_TRIVY_IMAGE = 'ghcr.io/aquasecurity/trivy:0.72.0@sha256:cffe3f5161a47a6823fbd23d985795b3ed72a4c806da4c4df16266c02accdd6f';
const DEFAULT_TIMEOUT_MS = 300_000;
const DEFAULT_OUTPUT_LIMIT = 65_536;
const PACKAGE_NAMES = ['podman', 'buildah', 'conmon', 'crun', 'runc'];
const TOOL_NAMES = ['podman', 'buildah', 'conmon', 'crun', 'runc'];
const RUN_STAGE_IDS = new Set([
  'repository-build',
  'image-user',
  'archive-export',
  'trivy-pull',
  'trivy-scan',
]);
const RUNTIME_PATHS = [
  '/usr/local/bin/crun',
  '/usr/bin/crun',
  '/usr/local/bin/runc',
  '/usr/bin/runc',
];

const usage = () => {
  process.stderr.write(`Usage:
  node scripts/ci/container-runtime-preflight.mjs preflight [--runtime runc] [--minimal-image IMAGE@sha256:DIGEST] [--trivy-image IMAGE@sha256:DIGEST] [--repository-dockerfile PATH] [--report PATH]
  node scripts/ci/container-runtime-preflight.mjs validate --report PATH
  node scripts/ci/container-runtime-preflight.mjs run-stage --report PATH --stage STAGE [--timeout-ms N] [--expect-stdout VALUE] -- /absolute/command [args...]
  node scripts/ci/container-runtime-preflight.mjs validate-artifact --report PATH --stage archive-export|sarif-validate --path PATH --kind archive|sarif
  node scripts/ci/container-runtime-preflight.mjs record-stage --report PATH --stage sarif-upload --outcome success|failure|cancelled|skipped
  node scripts/ci/container-runtime-preflight.mjs finalize --report PATH
`);
};

const parseOptions = (argv) => {
  const [command = 'preflight', ...rest] = argv;
  const options = {
    command,
    report: DEFAULT_REPORT,
    runtime: 'runc',
    minimalImage: DEFAULT_MINIMAL_IMAGE,
    trivyImage: DEFAULT_TRIVY_IMAGE,
    repositoryDockerfile: 'podman/Dockerfile',
    timeoutMs: DEFAULT_TIMEOUT_MS,
    outputLimitBytes: DEFAULT_OUTPUT_LIMIT,
  };
  const separator = rest.indexOf('--');
  const optionArgs = separator >= 0 ? rest.slice(0, separator) : rest;
  options.externalCommand = separator >= 0 ? rest.slice(separator + 1) : [];
  for (let index = 0; index < optionArgs.length; index += 1) {
    const arg = optionArgs[index];
    const next = optionArgs[index + 1];
    if (arg === '--help') {
      usage();
      process.exit(0);
    }
    const valueOptions = new Set([
      '--report', '--runtime', '--minimal-image', '--trivy-image', '--timeout-ms',
      '--output-limit-bytes', '--stage', '--path', '--kind', '--outcome', '--expect-stdout',
      '--generated-at',
      '--repository-dockerfile',
    ]);
    if (!valueOptions.has(arg) || next === undefined) throw new Error(`unknown or incomplete argument: ${arg}`);
    if (arg === '--report') options.report = next;
    else if (arg === '--runtime') options.runtime = next;
    else if (arg === '--minimal-image') options.minimalImage = next;
    else if (arg === '--trivy-image') options.trivyImage = next;
    else if (arg === '--timeout-ms') options.timeoutMs = Number(next);
    else if (arg === '--output-limit-bytes') options.outputLimitBytes = Number(next);
    else if (arg === '--stage') options.stage = next;
    else if (arg === '--path') options.artifactPath = next;
    else if (arg === '--kind') options.kind = next;
    else if (arg === '--outcome') options.outcome = next;
    else if (arg === '--expect-stdout') options.expectStdout = next;
    else if (arg === '--generated-at') options.generatedAt = next;
    else if (arg === '--repository-dockerfile') options.repositoryDockerfile = next || null;
    index += 1;
  }
  return options;
};

const ensureBoundedInteger = (name, value, minimum, maximum) => {
  if (!Number.isInteger(value) || value < minimum || value > maximum) {
    throw new Error(`${name} must be an integer between ${minimum} and ${maximum}`);
  }
};

const repoRelativePath = (repoRoot, name, value, requiredRoot) => {
  if (typeof value !== 'string' || value.length === 0 || path.isAbsolute(value)) {
    throw new Error(`${name} must be repository-relative`);
  }
  if (value.includes('\\') || value.split('/').some((segment) => segment === '.' || segment === '..' || segment === '.git')) {
    throw new Error(`${name} is outside the repository artifact boundary`);
  }
  const absolute = path.resolve(repoRoot, value);
  const boundary = path.resolve(repoRoot, requiredRoot);
  const relative = path.relative(boundary, absolute);
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`${name} must be under ${requiredRoot}`);
  }
  let current = boundary;
  if (fs.existsSync(current) && fs.lstatSync(current).isSymbolicLink()) {
    throw new Error(`${name} boundary must not be a symlink`);
  }
  for (const segment of path.relative(boundary, path.dirname(absolute)).split(path.sep).filter(Boolean)) {
    current = path.join(current, segment);
    if (fs.existsSync(current) && fs.lstatSync(current).isSymbolicLink()) {
      throw new Error(`${name} must not traverse symlinks`);
    }
  }
  return absolute;
};

const appendBounded = (current, chunk, limit) => {
  const combined = Buffer.concat([current, Buffer.from(chunk)]);
  return combined.length <= limit ? combined : combined.subarray(combined.length - limit);
};

export const runCommand = (command, args, {
  cwd,
  timeoutMs = DEFAULT_TIMEOUT_MS,
  outputLimitBytes = DEFAULT_OUTPUT_LIMIT,
  stream = false,
  env = process.env,
} = {}) => new Promise((resolve) => {
  const started = Date.now();
  let stdout = Buffer.alloc(0);
  let stderr = Buffer.alloc(0);
  let timedOut = false;
  let settled = false;
  const child = spawn(command, args, {
    cwd,
    env,
    shell: false,
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  const timer = setTimeout(() => {
    timedOut = true;
    child.kill('SIGTERM');
    setTimeout(() => child.kill('SIGKILL'), 2_000).unref();
  }, timeoutMs);
  const complete = (exitCode, spawnError = null) => {
    if (settled) return;
    settled = true;
    clearTimeout(timer);
    resolve({
      exitCode,
      timedOut,
      durationMs: Math.min(Date.now() - started, 3_600_000),
      stdout: stdout.toString('utf8'),
      stderr: stderr.toString('utf8'),
      spawnError,
    });
  };
  child.stdout.on('data', (chunk) => {
    stdout = appendBounded(stdout, chunk, outputLimitBytes);
    if (stream) process.stdout.write(chunk);
  });
  child.stderr.on('data', (chunk) => {
    stderr = appendBounded(stderr, chunk, outputLimitBytes);
    if (stream) process.stderr.write(chunk);
  });
  child.once('error', (error) => complete(null, error));
  child.once('close', (code) => complete(code));
});

const commandResult = (result, { notRun = false } = {}) => {
  if (notRun) return { status: 'not-run', exitCode: null, durationMs: 0, detail: 'not-selected' };
  if (result?.spawnError) return { status: 'fail', exitCode: null, durationMs: result.durationMs, detail: 'command-failed' };
  if (result?.timedOut) return { status: 'fail', exitCode: result.exitCode, durationMs: result.durationMs, detail: 'timeout' };
  return result?.exitCode === 0
    ? { status: 'pass', exitCode: 0, durationMs: result.durationMs, detail: 'completed' }
    : { status: 'fail', exitCode: result?.exitCode ?? null, durationMs: result?.durationMs ?? 0, detail: 'command-failed' };
};

const resolveExecutable = (name) => {
  const specialCandidates = name === 'conmon'
    ? ['/usr/local/lib/podman/conmon', '/usr/bin/conmon']
    : [];
  const pathCandidates = String(process.env.PATH ?? '')
    .split(path.delimiter)
    .filter(Boolean)
    .map((directory) => path.resolve(directory, name));
  for (const candidate of [...specialCandidates, ...pathCandidates]) {
    try {
      const canonical = fs.realpathSync(candidate);
      const stat = fs.statSync(canonical);
      if (stat.isFile() && (stat.mode & 0o111) !== 0 && isAllowedSystemExecutable(canonical)) return canonical;
    } catch {
      // Missing and rejected candidates remain unavailable evidence.
    }
  }
  return null;
};

const executableAt = (candidate) => {
  try {
    const canonical = fs.realpathSync(candidate);
    const stat = fs.statSync(canonical);
    if (!stat.isFile() || (stat.mode & 0o111) === 0 || !isAllowedSystemExecutable(canonical)) return null;
    return canonical;
  } catch {
    return null;
  }
};

const inventoryTool = async (name, repoRoot, options) => {
  const toolPath = resolveExecutable(name);
  if (!toolPath) return { name, path: null, version: null, source: 'unknown', available: false };
  const result = await runCommand(toolPath, ['--version'], { cwd: repoRoot, ...options });
  const version = parseToolVersion(`${result.stdout}\n${result.stderr}`);
  if (result.exitCode !== 0 || !version) {
    return { name, path: null, version: null, source: 'unknown', available: false };
  }
  return { name, path: toolPath, version, source: toolSourceForPath(toolPath), available: true };
};

const parseAptPolicy = (name, output) => {
  const installed = output.match(/^\s*Installed:\s*(\S+)/mu)?.[1];
  const candidate = output.match(/^\s*Candidate:\s*(\S+)/mu)?.[1];
  return {
    name,
    installedVersion: installed && installed !== '(none)' ? installed.slice(0, 120) : null,
    candidateVersion: candidate && candidate !== '(none)' ? candidate.slice(0, 120) : null,
  };
};

const inventoryPackage = async (name, repoRoot, options) => {
  const result = await runCommand('/usr/bin/apt-cache', ['policy', name], { cwd: repoRoot, ...options });
  if (result.exitCode !== 0) return { name, installedVersion: null, candidateVersion: null };
  return parseAptPolicy(name, result.stdout);
};

const runtimeConfigEntries = () => {
  const files = ['/etc/containers/containers.conf'];
  try {
    const fragments = fs.readdirSync('/etc/containers/containers.conf.d')
      .filter((name) => /^[A-Za-z0-9._-]+\.conf$/u.test(name))
      .sort()
      .map((name) => `/etc/containers/containers.conf.d/${name}`);
    files.push(...fragments);
  } catch {
    // An absent fragment directory is valid.
  }
  const entries = [];
  for (const file of files) {
    try {
      const stat = fs.lstatSync(file);
      if (!stat.isFile() || stat.isSymbolicLink()) continue;
      for (const rawLine of fs.readFileSync(file, 'utf8').split(/\r?\n/u)) {
        const line = rawLine.trim();
        if (!/^(?:runtime|runtimes|runtime_supports_json|runtime_supports_nocgroups)\s*=/u.test(line)) continue;
        if (/\/(?:home|tmp)\/|\/run\/user\//u.test(line)) continue;
        entries.push({ source: file, entry: line.slice(0, 240) });
        if (entries.length >= 24) return entries;
      }
    } catch {
      // Unreadable system config remains absent from bounded evidence.
    }
  }
  return entries;
};

const osRelease = () => {
  try {
    const text = fs.readFileSync('/etc/os-release', 'utf8');
    const value = text.match(/^PRETTY_NAME=(?:"([^"]+)"|(\S+))$/mu);
    return (value?.[1] ?? value?.[2] ?? os.type()).slice(0, 160);
  } catch {
    return os.type().slice(0, 160);
  }
};

const cgroupVersion = () => {
  if (fs.existsSync('/sys/fs/cgroup/cgroup.controllers')) return 'v2';
  if (fs.existsSync('/sys/fs/cgroup')) return 'v1';
  return 'unknown';
};

const writeReport = (reportPath, diagnostic) => {
  const errors = validateDiagnosticSemantics(diagnostic);
  if (errors.length > 0) throw new Error(`contract-invalid: ${errors.slice(0, 5).join('; ')}`);
  const rendered = renderDiagnostic(diagnostic);
  if (Buffer.byteLength(rendered, 'utf8') > DIAGNOSTIC_MAX_BYTES) {
    throw new Error('contract-invalid: diagnostic exceeds reviewed size limit');
  }
  fs.mkdirSync(path.dirname(reportPath), { recursive: true });
  const temp = `${reportPath}.tmp-${process.pid}`;
  fs.writeFileSync(temp, rendered, { mode: 0o600 });
  fs.renameSync(temp, reportPath);
};

const readReport = (repoRoot, relativePath) => {
  const result = readBoundedStructuredArtifact(repoRoot, relativePath, 'diagnostic');
  if (!result.ok) throw new Error(`contract-invalid: diagnostic artifact ${result.detail}`);
  const { absolute, value: diagnostic } = result;
  const errors = validateDiagnosticSemantics(diagnostic);
  if (errors.length > 0) throw new Error(`contract-invalid: ${errors.slice(0, 5).join('; ')}`);
  return { absolute, diagnostic };
};

const writeGithubOutputs = (values) => {
  const target = process.env.GITHUB_OUTPUT;
  if (!target) return;
  const lines = Object.entries(values).map(([key, value]) => `${key}=${String(value)}\n`).join('');
  fs.appendFileSync(target, lines, 'utf8');
};

const failDiagnostic = (diagnostic, classification, check) => {
  let updated = { ...diagnostic, status: 'fail', classification, pipelineComplete: false };
  if (check) updated = upsertCheck(updated, check);
  return updated;
};

const directRuntimeSmoke = async (runtimePath, repoRoot, options) => {
  const result = await runCommand(runtimePath, ['features'], { cwd: repoRoot, ...options });
  const base = commandResult(result);
  if (base.status !== 'pass') return base;
  try {
    const features = JSON.parse(result.stdout);
    const max = features?.ociVersionMax ?? features?.ociVersion?.max;
    if (typeof max !== 'string' || !parseToolVersion(max)) {
      return { ...base, status: 'fail', detail: 'malformed-output' };
    }
  } catch {
    return { ...base, status: 'fail', detail: 'malformed-output' };
  }
  return base;
};

const minimalRuntimeRun = async (podmanPath, runtimePath, image, repoRoot, options) => (
  commandResult(await runCommand(
    podmanPath,
    ['--runtime', runtimePath, 'run', '--rm', '--pull=missing', image, '/bin/true'],
    { cwd: repoRoot, ...options },
  ))
);

const minimalBuild = async (podmanPath, runtimePath, image, repoRoot, options) => {
  const context = path.join(repoRoot, 'artifacts', 'container-security', 'minimal-build');
  fs.mkdirSync(context, { recursive: true });
  fs.writeFileSync(path.join(context, 'Containerfile'), `FROM ${image}\nRUN true\n`, { mode: 0o600 });
  return commandResult(await runCommand(
    podmanPath,
    ['--runtime', runtimePath, 'build', '--pull=never', '--file', path.join(context, 'Containerfile'), '--tag', 'ae-runtime-preflight:issue-3672', context],
    { cwd: repoRoot, ...options },
  ));
};

const preflight = async (repoRoot, options) => {
  if (!['crun', 'runc'].includes(options.runtime)) throw new Error('runtime must be crun or runc');
  if (!isDigestPinnedImage(options.minimalImage)) throw new Error('minimal-image must be digest pinned');
  if (!isDigestPinnedImage(options.trivyImage)) throw new Error('trivy-image must be digest pinned');
  ensureBoundedInteger('timeout-ms', options.timeoutMs, 1_000, 3_600_000);
  ensureBoundedInteger('output-limit-bytes', options.outputLimitBytes, 1_024, 262_144);
  const reportPath = repoRelativePath(repoRoot, 'report', options.report, 'artifacts/container-security');
  const commandOptions = { timeoutMs: options.timeoutMs, outputLimitBytes: options.outputLimitBytes };
  const [packages, tools] = await Promise.all([
    Promise.all(PACKAGE_NAMES.map((name) => inventoryPackage(name, repoRoot, commandOptions))),
    Promise.all(TOOL_NAMES.map((name) => inventoryTool(name, repoRoot, commandOptions))),
  ]);
  const userId = typeof process.getuid === 'function' ? process.getuid() : 0;
  const podmanTool = tools.find((tool) => tool.name === 'podman');
  const base = {
    schemaVersion: SCHEMA_VERSION,
    generatedAt: options.generatedAt ?? new Date().toISOString(),
    status: 'fail',
    classification: 'runtime-missing',
    pipelineComplete: false,
    runner: {
      image: process.env.ImageOS?.slice(0, 80) ?? null,
      imageVersion: process.env.ImageVersion?.slice(0, 80) ?? null,
      osRelease: osRelease(),
      kernel: os.release().slice(0, 160),
      architecture: os.machine().slice(0, 40),
      userId,
      rootless: userId !== 0,
      cgroupVersion: cgroupVersion(),
    },
    packages,
    tools,
    runtimeCandidates: [],
    selectedRuntime: null,
    podman: {
      path: podmanTool?.path ?? null,
      version: podmanTool?.version ?? null,
      defaultRuntimePath: null,
      defaultRuntimeVersion: null,
      effectiveRuntimePath: null,
      effectiveRuntimeVersion: null,
      storageDriver: null,
      graphRootScope: 'unknown',
      cgroupManager: null,
      runtimeConfig: runtimeConfigEntries(),
    },
    inputs: {
      minimalImage: options.minimalImage,
      trivyImage: options.trivyImage,
      repositoryDockerfile: options.repositoryDockerfile,
    },
    configuration: {
      requestedRuntime: options.runtime,
      commandTimeoutMs: options.timeoutMs,
      outputLimitBytes: options.outputLimitBytes,
    },
    checks: [
      { id: 'podman-info', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' },
      { id: 'manifest-detect', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' },
      { id: 'direct-runtime-smoke', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' },
      { id: 'minimal-run', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' },
      { id: 'minimal-build', status: 'not-run', classification: null, exitCode: null, durationMs: 0, detail: 'not-selected' },
    ],
    limitations: [],
  };

  if (!podmanTool?.available || !podmanTool.path || !podmanTool.version) {
    const missing = failDiagnostic(base, 'runtime-missing', {
      id: 'podman-info',
      status: 'fail',
      classification: 'runtime-missing',
      exitCode: null,
      durationMs: 0,
      detail: 'runtime-unavailable',
    });
    writeReport(reportPath, missing);
    throw new Error('runtime-missing: podman inventory is unavailable');
  }

  const defaultInfoResult = await runCommand(
    podmanTool.path,
    ['info', '--debug', '--format', 'json'],
    { cwd: repoRoot, ...commandOptions },
  );
  if (defaultInfoResult.exitCode === 0 && !defaultInfoResult.timedOut && !defaultInfoResult.spawnError) {
    try {
      const defaultInfo = sanitizePodmanInfo(JSON.parse(defaultInfoResult.stdout), userId);
      base.podman.defaultRuntimePath = defaultInfo.effectiveRuntimePath;
      base.podman.defaultRuntimeVersion = defaultInfo.effectiveRuntimeVersion;
    } catch {
      base.limitations.push('Podman default-runtime inventory was malformed; selected-runtime validation remains authoritative.');
    }
  } else {
    base.limitations.push('Podman default-runtime inventory was unavailable; selected-runtime validation remains authoritative.');
  }

  const runtimeCandidates = [];
  const canonicalSeen = new Set();
  for (const candidatePath of RUNTIME_PATHS) {
    const runtimePath = executableAt(candidatePath);
    if (!runtimePath || canonicalSeen.has(runtimePath)) continue;
    canonicalSeen.add(runtimePath);
    const name = path.basename(runtimePath);
    const versionResult = await runCommand(runtimePath, ['--version'], { cwd: repoRoot, ...commandOptions });
    const version = parseToolVersion(`${versionResult.stdout}\n${versionResult.stderr}`);
    const available = versionResult.exitCode === 0 && Boolean(version);
    const directSmoke = available
      ? await directRuntimeSmoke(runtimePath, repoRoot, commandOptions)
      : { status: 'fail', exitCode: versionResult.exitCode, durationMs: versionResult.durationMs, detail: 'version-invalid' };
    const minimalRun = available
      ? await minimalRuntimeRun(podmanTool.path, runtimePath, options.minimalImage, repoRoot, commandOptions)
      : { status: 'not-run', exitCode: null, durationMs: 0, detail: 'runtime-unavailable' };
    runtimeCandidates.push({
      name,
      path: runtimePath,
      version: available ? version : null,
      source: toolSourceForPath(runtimePath),
      available,
      selected: false,
      directSmoke,
      minimalRun,
    });
  }

  let diagnostic = { ...base, runtimeCandidates };
  const preferred = runtimeCandidates
    .filter((candidate) => candidate.name === options.runtime)
    .sort((left, right) => Number(right.path.startsWith('/usr/local/')) - Number(left.path.startsWith('/usr/local/')))
    .find((candidate) => candidate.available && candidate.directSmoke.status === 'pass' && candidate.minimalRun.status === 'pass');
  if (!preferred || !preferred.version) {
    const requestedExists = runtimeCandidates.some((candidate) => candidate.name === options.runtime);
    const classification = requestedExists ? 'runtime-version-incompatible' : 'runtime-missing';
    diagnostic = failDiagnostic(diagnostic, classification, {
      id: 'minimal-run',
      status: 'fail',
      classification,
      exitCode: null,
      durationMs: 0,
      detail: requestedExists ? 'command-failed' : 'runtime-unavailable',
    });
    writeReport(reportPath, diagnostic);
    throw new Error(`${classification}: requested runtime did not pass direct and minimal smoke checks`);
  }
  diagnostic.runtimeCandidates = runtimeCandidates.map((candidate) => ({
    ...candidate,
    selected: candidate.path === preferred.path,
  }));
  diagnostic.selectedRuntime = {
    name: preferred.name,
    path: preferred.path,
    version: preferred.version,
    source: preferred.source,
  };
  diagnostic = upsertCheck(diagnostic, {
    id: 'direct-runtime-smoke',
    status: 'pass',
    classification: null,
    exitCode: 0,
    durationMs: preferred.directSmoke.durationMs,
    detail: 'completed',
  });
  diagnostic = upsertCheck(diagnostic, {
    id: 'minimal-run',
    status: 'pass',
    classification: null,
    exitCode: 0,
    durationMs: preferred.minimalRun.durationMs,
    detail: 'completed',
  });

  const infoResult = await runCommand(
    podmanTool.path,
    ['--runtime', preferred.path, 'info', '--debug', '--format', 'json'],
    { cwd: repoRoot, ...commandOptions },
  );
  const infoCheck = commandResult(infoResult);
  if (infoCheck.status !== 'pass') {
    diagnostic = failDiagnostic(diagnostic, 'runtime-selection-invalid', {
      id: 'podman-info',
      ...infoCheck,
      classification: 'runtime-selection-invalid',
    });
    writeReport(reportPath, diagnostic);
    throw new Error('runtime-selection-invalid: podman info failed for selected runtime');
  }
  try {
    diagnostic.podman = {
      ...diagnostic.podman,
      ...sanitizePodmanInfo(JSON.parse(infoResult.stdout), userId),
    };
  } catch {
    diagnostic = failDiagnostic(diagnostic, 'runtime-selection-invalid', {
      id: 'podman-info',
      status: 'fail',
      classification: 'runtime-selection-invalid',
      exitCode: 0,
      durationMs: infoResult.durationMs,
      detail: 'malformed-output',
    });
    writeReport(reportPath, diagnostic);
    throw new Error('runtime-selection-invalid: podman info was malformed');
  }
  if (diagnostic.podman.effectiveRuntimePath !== preferred.path) {
    diagnostic = failDiagnostic(diagnostic, 'runtime-selection-invalid', {
      id: 'podman-info',
      status: 'fail',
      classification: 'runtime-selection-invalid',
      exitCode: 0,
      durationMs: infoResult.durationMs,
      detail: 'path-invalid',
    });
    writeReport(reportPath, diagnostic);
    throw new Error('runtime-selection-invalid: effective runtime does not match selected runtime');
  }
  diagnostic = upsertCheck(diagnostic, {
    id: 'podman-info',
    status: 'pass',
    classification: null,
    exitCode: 0,
    durationMs: infoResult.durationMs,
    detail: 'completed',
  });

  const build = await minimalBuild(podmanTool.path, preferred.path, options.minimalImage, repoRoot, commandOptions);
  if (build.status !== 'pass') {
    diagnostic = failDiagnostic(diagnostic, 'minimal-build-failed', {
      id: 'minimal-build',
      ...build,
      classification: 'minimal-build-failed',
    });
    writeReport(reportPath, diagnostic);
    throw new Error('minimal-build-failed: selected runtime could not execute a minimal Containerfile RUN');
  }
  diagnostic = upsertCheck(diagnostic, {
    id: 'minimal-build',
    status: 'pass',
    classification: null,
    exitCode: 0,
    durationMs: build.durationMs,
    detail: 'completed',
  });
  diagnostic.status = 'pass';
  diagnostic.classification = 'runtime-ready';
  diagnostic.limitations = runtimeCandidates
    .filter((candidate) => candidate.path !== preferred.path && candidate.minimalRun.status === 'fail')
    .map((candidate) => `Non-selected ${candidate.name} candidate from ${candidate.source} did not pass the minimal run.`)
    .concat(base.limitations)
    .slice(0, 12);
  const semanticErrors = validateDiagnosticSemantics(diagnostic);
  if (semanticErrors.length > 0) {
    diagnostic = failDiagnostic(diagnostic, 'runtime-selection-invalid', {
      id: 'podman-info',
      status: 'fail',
      classification: 'runtime-selection-invalid',
      exitCode: null,
      durationMs: 0,
      detail: 'malformed-output',
    });
    writeReport(reportPath, diagnostic);
    throw new Error(`runtime-selection-invalid: ${semanticErrors.slice(0, 3).join('; ')}`);
  }
  writeReport(reportPath, diagnostic);
  writeGithubOutputs({
    classification: diagnostic.classification,
    podman_path: podmanTool.path,
    runtime_name: preferred.name,
    runtime_path: preferred.path,
    runtime_version: preferred.version,
    report_path: options.report,
  });
  process.stdout.write(`container-runtime classification=${diagnostic.classification} podman=${podmanTool.version} runtime=${preferred.name}@${preferred.version} source=${preferred.source}\n`);
};

const runStage = async (repoRoot, options) => {
  if (!options.stage || !options.externalCommand?.length) throw new Error('run-stage requires --stage and a command after --');
  if (!RUN_STAGE_IDS.has(options.stage)) throw new Error('run-stage stage is invalid');
  ensureBoundedInteger('timeout-ms', options.timeoutMs, 1_000, 3_600_000);
  ensureBoundedInteger('output-limit-bytes', options.outputLimitBytes, 1_024, 262_144);
  const { absolute, diagnostic } = readReport(repoRoot, options.report);
  if (diagnostic.pipelineComplete) throw new Error('run-stage cannot mutate finalized evidence');
  if (diagnostic.status !== 'pass' || diagnostic.classification !== 'runtime-ready') {
    throw new Error('run-stage requires a runtime-ready diagnostic');
  }
  const prerequisite = stagePrerequisite(options.stage);
  if (prerequisite && !diagnostic.checks.some((check) => check.id === prerequisite && check.status === 'pass')) {
    throw new Error(`run-stage requires ${prerequisite}=pass before ${options.stage}`);
  }
  const [command, ...args] = options.externalCommand;
  if (!isAllowedSystemExecutable(command)) throw new Error('run-stage command must be an allowlisted absolute system executable');
  const canonical = executableAt(command);
  if (canonical !== command) throw new Error('run-stage command path is unavailable or substituted');
  const result = await runCommand(command, args, {
    cwd: repoRoot,
    timeoutMs: options.timeoutMs,
    outputLimitBytes: options.outputLimitBytes,
    stream: true,
  });
  let stageResult = commandResult(result);
  if (stageResult.status === 'pass' && options.expectStdout !== undefined && result.stdout.trim() !== options.expectStdout) {
    stageResult = { ...stageResult, status: 'fail', detail: 'unexpected-image-user' };
  }
  const classification = stageFailureClassification(options.stage);
  const check = {
    id: options.stage,
    ...stageResult,
    classification: stageResult.status === 'pass' ? null : classification,
  };
  let updated = upsertCheck({ ...diagnostic, pipelineComplete: false }, check);
  if (stageResult.status !== 'pass') updated = { ...updated, status: 'fail', classification };
  writeReport(absolute, updated);
  if (stageResult.status !== 'pass') throw new Error(`${classification}: ${options.stage} ${stageResult.detail}`);
};

const validateArtifact = (repoRoot, options) => {
  if (!['archive-export', 'sarif-validate'].includes(options.stage)) throw new Error('validate-artifact stage is invalid');
  if (!['archive', 'sarif'].includes(options.kind)) throw new Error('validate-artifact kind is invalid');
  const { absolute, diagnostic } = readReport(repoRoot, options.report);
  if (diagnostic.pipelineComplete) throw new Error('validate-artifact cannot mutate finalized evidence');
  const existing = diagnostic.checks.find((check) => check.id === options.stage);
  const prerequisite = options.stage === 'archive-export' ? 'archive-export' : 'trivy-scan';
  const prerequisiteCheck = diagnostic.checks.find((check) => check.id === prerequisite);
  const result = inspectArtifact(repoRoot, options.artifactPath, options.kind);
  if (!prerequisiteCheck || prerequisiteCheck.status !== 'pass') {
    result.ok = false;
    result.state = 'missing';
    result.detail = 'missing-output';
  }
  const classification = options.kind === 'sarif'
    ? stageFailureClassification('sarif-validate', { outputState: result.state })
    : 'archive-export-failed';
  const check = {
    id: options.stage,
    status: result.ok ? 'pass' : 'fail',
    classification: result.ok ? null : classification,
    exitCode: result.ok ? (existing?.exitCode ?? 0) : null,
    durationMs: existing?.durationMs ?? 0,
    detail: result.detail,
  };
  let updated = upsertCheck({ ...diagnostic, pipelineComplete: false }, check);
  if (!result.ok) updated = { ...updated, status: 'fail', classification };
  writeReport(absolute, updated);
  if (!result.ok) throw new Error(`${classification}: artifact ${result.detail}`);
};

const recordStage = (repoRoot, options) => {
  if (!['manifest-detect', 'sarif-upload'].includes(options.stage)) throw new Error('record-stage stage is invalid');
  if (!['success', 'failure', 'cancelled', 'skipped'].includes(options.outcome)) throw new Error('record-stage outcome is invalid');
  const { absolute, diagnostic } = readReport(repoRoot, options.report);
  if (diagnostic.pipelineComplete) throw new Error('record-stage cannot mutate finalized evidence');
  let passed = options.outcome === 'success';
  const classification = stageFailureClassification(options.stage);
  if (options.stage === 'manifest-detect' && passed) {
    const manifest = diagnostic.inputs.repositoryDockerfile;
    if (!manifest) passed = false;
    else {
      try {
        const candidate = repoRelativePath(repoRoot, 'repositoryDockerfile', manifest, '.');
        const stat = fs.lstatSync(candidate);
        if (!stat.isFile() || stat.isSymbolicLink()) passed = false;
      } catch {
        passed = false;
      }
    }
  }
  const check = {
    id: options.stage,
    status: passed ? 'pass' : 'fail',
    classification: passed ? null : classification,
    exitCode: passed ? 0 : null,
    durationMs: 0,
    detail: passed
      ? 'completed'
      : (options.stage === 'manifest-detect'
        ? 'manifest-missing'
        : (options.outcome === 'skipped' ? 'upload-skipped' : 'command-failed')),
  };
  let updated = upsertCheck({ ...diagnostic, pipelineComplete: false }, check);
  if (!passed && diagnostic.status === 'pass') updated = { ...updated, status: 'fail', classification };
  writeReport(absolute, updated);
  if (!passed) throw new Error(`${classification}: ${options.stage} outcome=${options.outcome}`);
};

const finalizeReport = (repoRoot, options) => {
  const { absolute, diagnostic } = readReport(repoRoot, options.report);
  const finalized = finalizeDiagnostic(diagnostic);
  writeReport(absolute, finalized);
  writeGithubOutputs({
    pipeline_complete: finalized.pipelineComplete,
    report_path: options.report,
  });
  process.stdout.write(`Finalized ${SCHEMA_VERSION}: pipelineComplete=true\n`);
};

const main = async () => {
  const options = parseOptions(process.argv.slice(2));
  const repoRoot = process.cwd();
  if (options.command === 'preflight') await preflight(repoRoot, options);
  else if (options.command === 'validate') {
    readReport(repoRoot, options.report);
    process.stdout.write(`Validated ${SCHEMA_VERSION}: ${options.report}\n`);
  } else if (options.command === 'run-stage') await runStage(repoRoot, options);
  else if (options.command === 'validate-artifact') validateArtifact(repoRoot, options);
  else if (options.command === 'record-stage') recordStage(repoRoot, options);
  else if (options.command === 'finalize') finalizeReport(repoRoot, options);
  else throw new Error(`unknown command: ${options.command}`);
};

if (import.meta.url === pathToFileURL(process.argv[1] ?? '').href) {
  main().catch((error) => {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`::error title=container-security::${message.slice(0, 500)}\n`);
    process.exitCode = 1;
  });
}
