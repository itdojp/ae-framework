import fs from 'node:fs';
import path from 'node:path';

export const MODEL_CHECK_LOGICAL_ARTIFACT_ROOT = 'artifacts/codex';

const isWithin = (root, candidate) => {
  const relative = path.relative(root, candidate);
  return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
};

const normalizeRepositoryRelativePath = (value) => {
  if (typeof value !== 'string' || !value.trim() || path.isAbsolute(value)) return null;
  const normalized = value.trim().replaceAll('\\', '/');
  const segments = normalized.split('/');
  if (segments.includes('..') || segments.includes('') || segments.includes('.')) return null;
  return normalized;
};

export function assertModelCheckArtifactRoot(artifactRoot, { containmentRoot } = {}) {
  const resolvedRoot = path.resolve(artifactRoot);
  const stat = fs.lstatSync(resolvedRoot);
  if (stat.isSymbolicLink() || !stat.isDirectory()) {
    throw new Error('model-check artifact root must be a non-symlink directory');
  }
  const realRoot = fs.realpathSync(resolvedRoot);
  if (containmentRoot) {
    const realContainmentRoot = fs.realpathSync(path.resolve(containmentRoot));
    if (!isWithin(realContainmentRoot, realRoot)) {
      throw new Error('model-check artifact root resolves outside the repository');
    }
  }
  return { resolvedRoot, realRoot };
}

export function assertSafeModelCheckArtifactTarget(targetPath, artifactRoot, { containmentRoot } = {}) {
  const { resolvedRoot, realRoot } = assertModelCheckArtifactRoot(artifactRoot, { containmentRoot });
  const resolvedTarget = path.resolve(targetPath);
  if (!isWithin(resolvedRoot, resolvedTarget) || resolvedTarget === resolvedRoot) {
    throw new Error('model-check artifact target must remain inside the expected artifact root');
  }
  const parentReal = fs.realpathSync(path.dirname(resolvedTarget));
  if (!isWithin(realRoot, parentReal)) {
    throw new Error('model-check artifact target parent resolves outside the expected artifact root');
  }
  if (fs.existsSync(resolvedTarget)) {
    const stat = fs.lstatSync(resolvedTarget);
    if (stat.isSymbolicLink() || !stat.isFile()) {
      throw new Error('model-check artifact target must be a regular non-symlink file');
    }
  }
  return resolvedTarget;
}

export function resolveModelCheckLogReference(logPath, artifactRoot, {
  logicalRoot = MODEL_CHECK_LOGICAL_ARTIFACT_ROOT,
} = {}) {
  const normalized = normalizeRepositoryRelativePath(logPath);
  const normalizedRoot = normalizeRepositoryRelativePath(logicalRoot);
  if (!normalized || !normalizedRoot || !normalized.startsWith(`${normalizedRoot}/`)) {
    throw new Error(`log reference must be repository-relative under ${logicalRoot}`);
  }
  const suffix = normalized.slice(normalizedRoot.length + 1);
  const { resolvedRoot, realRoot } = assertModelCheckArtifactRoot(artifactRoot);
  const candidate = path.resolve(resolvedRoot, ...suffix.split('/'));
  if (!isWithin(resolvedRoot, candidate) || candidate === resolvedRoot) {
    throw new Error('log reference escapes the expected artifact root');
  }
  const stat = fs.lstatSync(candidate);
  if (stat.isSymbolicLink() || !stat.isFile()) {
    throw new Error('log reference must resolve to a regular non-symlink file');
  }
  const realCandidate = fs.realpathSync(candidate);
  if (!isWithin(realRoot, realCandidate)) {
    throw new Error('log reference resolves outside the expected artifact root');
  }
  return candidate;
}

export function validateModelCheckReferencedLogs(report, {
  artifactRoot,
  logicalRoot = MODEL_CHECK_LOGICAL_ARTIFACT_ROOT,
} = {}) {
  const errors = [];
  if (!artifactRoot) return ['artifactRoot is required to validate referenced logs'];
  for (const backendName of ['tlc', 'alloy']) {
    const results = Array.isArray(report?.[backendName]?.results) ? report[backendName].results : [];
    for (const [index, result] of results.entries()) {
      const resultLog = result?.log;
      const evidenceLog = result?.evidence?.result?.logPath;
      if (resultLog !== evidenceLog) {
        errors.push(`${backendName}.results[${index}] log reference does not match execution evidence`);
        continue;
      }
      try {
        resolveModelCheckLogReference(resultLog, artifactRoot, { logicalRoot });
      } catch (error) {
        errors.push(
          `${backendName}.results[${index}] referenced log is invalid: ${error instanceof Error ? error.message : String(error)}`,
        );
      }
    }
  }
  return errors;
}
