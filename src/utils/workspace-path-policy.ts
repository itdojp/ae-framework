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

export class WorkspacePathPolicyError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'WorkspacePathPolicyError';
  }
}

const hasWindowsAbsolutePrefix = (value: string): boolean =>
  path.win32.isAbsolute(value) || /^[A-Za-z]:[\\/]/.test(value);

const isPathWithin = (baseDir: string, candidatePath: string): boolean => {
  const relative = path.relative(baseDir, candidatePath);
  return relative === '' || (!!relative && !relative.startsWith('..') && !path.isAbsolute(relative));
};

const pathPolicyLabel = (label: string | undefined): string => label ?? 'workspace path';

const splitInputPath = (value: string): string[] => value.replace(/\\/g, '/').split('/');

const nearestExistingAncestor = (resolvedPath: string): string | null => {
  let current = path.resolve(resolvedPath);
  while (!existsSync(current)) {
    const parent = path.dirname(current);
    if (parent === current) return null;
    current = parent;
  }
  return current;
};

const assertExistingAncestorWithin = (workspaceRoot: string, resolvedPath: string, label: string): void => {
  if (!existsSync(workspaceRoot)) return;
  const ancestor = nearestExistingAncestor(resolvedPath);
  if (!ancestor) return;

  const realRoot = realpathSync(workspaceRoot);
  const realAncestor = realpathSync(ancestor);
  if (!isPathWithin(realRoot, realAncestor)) {
    throw new WorkspacePathPolicyError(`${label} resolves through a filesystem entry outside the approved workspace`);
  }
};

export function resolveWorkspaceRoot(options: WorkspaceRootOptions = {}): string {
  const envVar = options.envVar ?? 'AE_WORKSPACE_ROOT';
  const fromEnv = process.env[envVar]?.trim();
  return path.resolve(fromEnv && fromEnv.length > 0 ? fromEnv : (options.defaultRoot ?? process.cwd()));
}

export function resolveWorkspacePath(input: string, options: WorkspacePathOptions = {}): string {
  const label = pathPolicyLabel(options.label);
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
  if (segments.some((segment) => segment === '.' || segment === '..')) {
    throw new WorkspacePathPolicyError(`${label} must not contain dot-segment path components`);
  }

  const workspaceRoot = path.resolve(options.workspaceRoot ?? resolveWorkspaceRoot());
  const resolved = path.resolve(workspaceRoot, raw);
  if (!isPathWithin(workspaceRoot, resolved)) {
    throw new WorkspacePathPolicyError(`${label} escaped the approved workspace`);
  }
  assertExistingAncestorWithin(workspaceRoot, resolved, label);
  return resolved;
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

export function toWorkspaceRelativePath(resolvedPath: string, options: WorkspacePathOptions = {}): string {
  const label = pathPolicyLabel(options.label);
  const workspaceRoot = path.resolve(options.workspaceRoot ?? resolveWorkspaceRoot());
  const absolutePath = path.resolve(resolvedPath);
  if (!isPathWithin(workspaceRoot, absolutePath)) {
    throw new WorkspacePathPolicyError(`${label} is outside the approved workspace`);
  }
  const relative = path.relative(workspaceRoot, absolutePath);
  return relative === '' ? '.' : relative.replace(/\\/g, '/');
}
