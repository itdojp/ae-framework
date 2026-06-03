import path from 'node:path';
import {
  resolveContainedWorkspacePath,
  resolveWorkspacePath,
  resolveWorkspaceRoot,
  toWorkspaceRelativePath,
  WorkspacePathPolicyError,
} from '../utils/workspace-path-policy.js';

export const INTEGRATION_WRITE_APPROVAL_SCOPE = 'integration-cli-write' as const;
export const DEFAULT_INTEGRATION_ARTIFACT_ROOT = 'artifacts/integration' as const;
export const DEFAULT_INTEGRATION_OUTPUT_DIR = 'artifacts/integration/test-results' as const;

export interface IntegrationPathContext {
  workspaceRoot: string;
  artifactRoot: string;
}

export interface ResolvedIntegrationPath {
  resolvedPath: string;
  workspaceRelativePath: string;
}

export interface IntegrationPathContextOptions {
  workspaceRoot?: string;
  artifactRoot?: string;
}

const hasWindowsAbsolutePrefix = (value: string): boolean =>
  path.win32.isAbsolute(value) || /^[A-Za-z]:[\\/]/.test(value);

const isPathWithin = (baseDir: string, candidatePath: string): boolean => {
  const relative = path.relative(baseDir, candidatePath);
  return relative === '' || (!!relative && !relative.startsWith('..') && !path.isAbsolute(relative));
};

const normalizeWorkspaceRelativePath = (input: string, label: string): string => {
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
  if (raw.startsWith('//') || path.posix.isAbsolute(raw) || path.isAbsolute(raw) || hasWindowsAbsolutePrefix(raw)) {
    throw new WorkspacePathPolicyError(`${label} must be relative to the approved workspace`);
  }

  const segments = raw.split('/').filter(segment => segment !== '' && segment !== '.');
  if (segments.length === 0) {
    throw new WorkspacePathPolicyError(`${label} must be a non-empty workspace-relative path`);
  }
  if (segments.some(segment => segment === '..')) {
    throw new WorkspacePathPolicyError(`${label} must not contain parent-directory path components`);
  }

  return segments.join('/');
};

export function createIntegrationPathContext(
  options: IntegrationPathContextOptions = {},
): IntegrationPathContext {
  const workspaceRoot = resolveWorkspaceRoot({ defaultRoot: options.workspaceRoot ?? process.cwd() });
  const artifactRootInput = options.artifactRoot ?? process.env['AE_INTEGRATION_ARTIFACT_ROOT'] ?? DEFAULT_INTEGRATION_ARTIFACT_ROOT;
  const artifactRoot = resolveWorkspacePath(
    normalizeWorkspaceRelativePath(artifactRootInput, 'integration artifact root'),
    { workspaceRoot, label: 'integration artifact root' },
  );
  return { workspaceRoot, artifactRoot };
}

export function getDefaultIntegrationOutputDir(context: IntegrationPathContext): string {
  const artifactRoot = toWorkspaceRelativePath(context.artifactRoot, {
    workspaceRoot: context.workspaceRoot,
    label: 'integration artifact root',
  });
  return path.posix.join(artifactRoot, 'test-results');
}

export function resolveIntegrationInputPath(
  input: string,
  context: IntegrationPathContext,
  label = 'integration input path',
): ResolvedIntegrationPath {
  const workspaceRelative = normalizeWorkspaceRelativePath(input, label);
  const resolvedPath = resolveWorkspacePath(workspaceRelative, {
    workspaceRoot: context.workspaceRoot,
    label,
  });
  return {
    resolvedPath,
    workspaceRelativePath: toWorkspaceRelativePath(resolvedPath, {
      workspaceRoot: context.workspaceRoot,
      label,
    }),
  };
}

export function resolveIntegrationOutputPath(
  input: string,
  context: IntegrationPathContext,
  label = 'integration output path',
): ResolvedIntegrationPath {
  let resolvedPath: string;

  if (path.isAbsolute(input) || hasWindowsAbsolutePrefix(input)) {
    throw new WorkspacePathPolicyError(`${label} must be relative to the approved integration artifact root`);
  } else {
    const workspaceRelative = normalizeWorkspaceRelativePath(input, label);
    resolvedPath = resolveWorkspacePath(workspaceRelative, {
      workspaceRoot: context.workspaceRoot,
      label,
    });
  }

  if (!isPathWithin(context.artifactRoot, resolvedPath)) {
    throw new WorkspacePathPolicyError(`${label} must stay under the approved integration artifact root`);
  }

  const artifactRelative = path.relative(context.artifactRoot, resolvedPath).replace(/\\/g, '/');
  if (artifactRelative !== '') {
    resolvedPath = resolveContainedWorkspacePath(context.artifactRoot, artifactRelative, label);
  }

  return {
    resolvedPath,
    workspaceRelativePath: toWorkspaceRelativePath(resolvedPath, {
      workspaceRoot: context.workspaceRoot,
      label,
    }),
  };
}

export function isIntegrationAgentContext(): boolean {
  const raw = process.env['AE_INTEGRATION_AGENT_CONTEXT'] ?? process.env['AE_AGENT_CONTEXT'];
  if (!raw) return false;
  return ['1', 'true', 'yes', 'y'].includes(raw.trim().toLowerCase());
}
