import path from 'node:path';
import { existsSync, realpathSync } from 'node:fs';

export interface WorkspaceRootOptions {
  envVar?: string;
  defaultRoot?: string;
}

export interface WorkspacePathOptions {
  workspaceRoot?: string;
  label?: string;
}

export interface ArtifactPathOptions extends WorkspacePathOptions {
  artifactRoot?: string;
  allowAbsolute?: boolean;
}

export class WorkspacePathPolicyError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'WorkspacePathPolicyError';
  }
}

const hasWindowsAbsolutePrefix = (value: string): boolean =>
  /^[A-Za-z]:[\\/]/.test(value);

const isPathWithin = (baseDir: string, candidatePath: string): boolean => {
  const relative = path.relative(baseDir, candidatePath);
  return relative === '' || (!!relative && !relative.startsWith('..') && !path.isAbsolute(relative));
};

const pathPolicyLabel = (label: string | undefined): string => label ?? 'workspace path';

const splitInputPath = (value: string): string[] => value.replace(/\\/g, '/').split('/');

const hasDotSegment = (segments: string[]): boolean =>
  segments.some((segment) => segment === '.' || segment === '..');

const hasGitMetadataSegment = (segments: string[]): boolean =>
  segments.some((segment) => segment.toLowerCase() === '.git');

const assertNoUnsafeSegments = (segments: string[], label: string): void => {
  if (hasDotSegment(segments)) {
    throw new WorkspacePathPolicyError(`${label} must not contain dot-segment path components`);
  }
  if (hasGitMetadataSegment(segments)) {
    throw new WorkspacePathPolicyError(`${label} must not target Git metadata directories`);
  }
};

const normalizeWorkspaceRelativeInput = (input: string, label: string): string => {
  const raw = String(input).trim();
  if (!raw) {
    throw new WorkspacePathPolicyError(`${label} must be a non-empty workspace-relative path`);
  }
  if (raw.includes('\0')) {
    throw new WorkspacePathPolicyError(`${label} must not contain NUL bytes`);
  }
  if (raw.includes('\\')) {
    throw new WorkspacePathPolicyError(`${label} must use POSIX-style '/' separators`);
  }
  if (raw.startsWith('//') || path.isAbsolute(raw) || hasWindowsAbsolutePrefix(raw)) {
    throw new WorkspacePathPolicyError(`${label} must be relative to the approved workspace`);
  }

  const segments = splitInputPath(raw);
  assertNoUnsafeSegments(segments, label);
  return raw;
};

const nearestExistingAncestor = (resolvedPath: string): string | null => {
  let current = path.resolve(resolvedPath);
  while (!existsSync(current)) {
    const parent = path.dirname(current);
    if (parent === current) return null;
    current = parent;
  }
  return current;
};

const safeRealpathSync = (value: string, label: string): string => {
  try {
    return realpathSync(value);
  } catch {
    throw new WorkspacePathPolicyError(`${label} could not be resolved safely`);
  }
};

const assertExistingAncestorWithin = (workspaceRoot: string, resolvedPath: string, label: string): void => {
  if (!existsSync(workspaceRoot)) return;
  const ancestor = nearestExistingAncestor(resolvedPath);
  if (!ancestor) return;

  const realRoot = safeRealpathSync(workspaceRoot, label);
  const realAncestor = safeRealpathSync(ancestor, label);
  if (!isPathWithin(realRoot, realAncestor)) {
    throw new WorkspacePathPolicyError(`${label} resolves through a filesystem entry outside the approved workspace`);
  }
};

export function resolveWorkspaceRoot(options: WorkspaceRootOptions = {}): string {
  const envVar = options.envVar ?? 'AE_WORKSPACE_ROOT';
  const fromEnv = process.env[envVar]?.trim();
  return path.resolve(fromEnv && fromEnv.length > 0 ? fromEnv : (options.defaultRoot ?? process.cwd()));
}

export function assertWithinWorkspace(resolvedPath: string, options: WorkspacePathOptions = {}): string {
  const label = pathPolicyLabel(options.label);
  const raw = String(resolvedPath).trim();
  if (!raw) {
    throw new WorkspacePathPolicyError(`${label} must be a non-empty path`);
  }
  if (raw.includes('\0')) {
    throw new WorkspacePathPolicyError(`${label} must not contain NUL bytes`);
  }
  if (raw.includes('\\')) {
    throw new WorkspacePathPolicyError(`${label} must use POSIX-style '/' separators`);
  }
  if (hasWindowsAbsolutePrefix(raw)) {
    throw new WorkspacePathPolicyError(`${label} must not use Windows absolute paths`);
  }
  const workspaceRoot = path.resolve(options.workspaceRoot ?? resolveWorkspaceRoot());
  const resolved = path.isAbsolute(raw)
    ? path.resolve(raw)
    : path.resolve(workspaceRoot, raw);

  if (!isPathWithin(workspaceRoot, resolved)) {
    throw new WorkspacePathPolicyError(`${label} is outside the approved workspace`);
  }
  assertExistingAncestorWithin(workspaceRoot, resolved, label);
  return resolved;
}

export function resolveWorkspacePath(input: string, options: WorkspacePathOptions = {}): string {
  const label = pathPolicyLabel(options.label);
  const raw = normalizeWorkspaceRelativeInput(input, label);
  const workspaceRoot = path.resolve(options.workspaceRoot ?? resolveWorkspaceRoot());
  const resolved = path.resolve(workspaceRoot, raw);
  return assertWithinWorkspace(resolved, { workspaceRoot, label });
}

export function resolveContainedWorkspacePath(baseDir: string, relativePath: string, label?: string): string {
  const base = path.resolve(baseDir);
  const resolved = resolveWorkspacePath(relativePath, {
    workspaceRoot: base,
    label: label ?? 'contained path',
  });
  if (!isPathWithin(base, resolved)) {
    throw new WorkspacePathPolicyError(`${pathPolicyLabel(label)} escaped the approved base directory`);
  }
  return resolved;
}

export function resolveArtifactPath(input: string, options: ArtifactPathOptions = {}): string {
  const label = pathPolicyLabel(options.label);
  const workspaceRoot = path.resolve(options.workspaceRoot ?? resolveWorkspaceRoot());
  const artifactRootInput = String(options.artifactRoot ?? 'artifacts').trim();
  if (!artifactRootInput) {
    throw new WorkspacePathPolicyError(`${label} artifact root must be a non-empty path`);
  }
  if (artifactRootInput.includes('\0')) {
    throw new WorkspacePathPolicyError(`${label} artifact root must not contain NUL bytes`);
  }

  const artifactRoot = path.isAbsolute(artifactRootInput) || hasWindowsAbsolutePrefix(artifactRootInput)
    ? assertWithinWorkspace(artifactRootInput, { workspaceRoot, label: `${label} artifact root` })
    : resolveWorkspacePath(artifactRootInput, {
        workspaceRoot,
        label: `${label} artifact root`,
      });
  const artifactRootRelative = toWorkspaceRelativePath(artifactRoot, {
    workspaceRoot,
    label: `${label} artifact root`,
  });

  const raw = String(input).trim();
  if (!raw) {
    throw new WorkspacePathPolicyError(`${label} must be a non-empty artifact path`);
  }
  if (raw.includes('\0')) {
    throw new WorkspacePathPolicyError(`${label} must not contain NUL bytes`);
  }
  if (raw.includes('\\')) {
    throw new WorkspacePathPolicyError(`${label} must use POSIX-style '/' separators`);
  }

  let resolved: string;
  if (path.isAbsolute(raw) || hasWindowsAbsolutePrefix(raw) || raw.startsWith('//')) {
    if (!options.allowAbsolute) {
      throw new WorkspacePathPolicyError(`${label} must be relative to the approved artifact root`);
    }
    resolved = assertWithinWorkspace(raw, { workspaceRoot, label });
  } else {
    const segments = splitInputPath(raw);
    assertNoUnsafeSegments(segments, label);
    const normalized = segments.join('/');
    const isWorkspaceRelativeArtifact =
      normalized === artifactRootRelative || normalized.startsWith(`${artifactRootRelative}/`);
    resolved = isWorkspaceRelativeArtifact
      ? path.resolve(workspaceRoot, normalized)
      : path.resolve(artifactRoot, normalized);
    resolved = assertWithinWorkspace(resolved, { workspaceRoot, label });
  }

  if (!isPathWithin(artifactRoot, resolved)) {
    throw new WorkspacePathPolicyError(`${label} must stay under the approved artifact root`);
  }
  assertExistingAncestorWithin(artifactRoot, resolved, label);
  return resolved;
}

export function toWorkspaceRelativePath(resolvedPath: string, options: WorkspacePathOptions = {}): string {
  const label = pathPolicyLabel(options.label);
  const workspaceRoot = path.resolve(options.workspaceRoot ?? resolveWorkspaceRoot());
  const absolutePath = assertWithinWorkspace(resolvedPath, { workspaceRoot, label });
  const relative = path.relative(workspaceRoot, absolutePath);
  return relative === '' ? '.' : relative.replace(/\\/g, '/');
}
