import * as fs from 'fs/promises';
import * as path from 'path';
import type { ImageBuildContext } from './container-engine.js';

export const AE_CONTAINER_MANAGED_LABEL = 'ae-framework.managed';
export const AE_CONTAINER_MANAGED_LABEL_VALUE = 'true';
export const AE_CONTAINER_LABEL_FILTER = `label=${AE_CONTAINER_MANAGED_LABEL}=${AE_CONTAINER_MANAGED_LABEL_VALUE}`;

export const CONTAINER_PUSH_APPROVAL = 'approved-container-image-push' as const;
export const CONTAINER_CLEANUP_CONFIRM = 'delete-ae-framework-resources' as const;
export const CONTAINER_FORCE_CLEANUP_CONFIRM = 'force-delete-ae-framework-resources' as const;

const MAX_BUILD_ARG_VALUE_LENGTH = 2048;
const MAX_TOOL_NAME_LENGTH = 64;
const MAX_IMAGE_REFERENCE_LENGTH = 255;

const toolNamePattern = /^[A-Za-z0-9][A-Za-z0-9._+@-]{0,63}$/;
const buildArgKeyPattern = /^[A-Za-z_][A-Za-z0-9_]{0,63}$/;
const buildArgValuePattern = /^[A-Za-z0-9._+@:/,=-]*$/;
const registryComponentPattern = /^(?:localhost|[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?(?:\.[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?)*)(?::[0-9]{1,5})?$/;
const repositoryComponentPattern = /^[a-z0-9]+(?:[._-][a-z0-9]+)*$/;
const tagPattern = /^[A-Za-z0-9_][A-Za-z0-9_.-]{0,127}$/;
const tagPrefixBoundaryPattern = /[._-]/;

export interface ContainerImagePolicy {
  /** Prefixes of fully-qualified image references that may be pushed after request approval. */
  allowedPushPrefixes?: string[];
}

export interface ValidatedImageReference {
  reference: string;
  name: string;
  tag: string;
  registry?: string;
}

export interface PushPolicyRequest {
  imageRef: ValidatedImageReference;
  push?: boolean;
  pushApproval?: string;
  policy?: ContainerImagePolicy;
}

export interface CleanupConfirmationOptions {
  dryRun?: boolean;
  force?: boolean;
  confirm?: string;
}

export interface WorkspaceResolutionOptions {
  projectPath: string;
  workspaceRoot?: string;
}

export interface WorkspaceResolutionResult {
  workspaceRoot: string;
  projectPath: string;
}

const allowedToolsByLanguage: Record<'rust' | 'elixir' | 'multi', Set<string>> = {
  rust: new Set(['cargo', 'rustc', 'prusti', 'kani', 'miri']),
  elixir: new Set(['elixir', 'mix', 'exunit']),
  multi: new Set(['cargo', 'rustc', 'prusti', 'kani', 'miri', 'elixir', 'mix', 'exunit']),
};

export const validateContainerTools = (tools: string[]): string[] => {
  if (!Array.isArray(tools) || tools.length === 0) {
    throw new Error('At least one verification tool is required');
  }

  return tools.map((tool) => {
    if (typeof tool !== 'string' || tool.length === 0 || tool.length > MAX_TOOL_NAME_LENGTH || !toolNamePattern.test(tool)) {
      throw new Error(`Invalid verification tool name: ${JSON.stringify(tool)}`);
    }
    return tool;
  });
};

export const validateContainerToolsForLanguage = (language: 'rust' | 'elixir' | 'multi', tools: string[]): string[] => {
  const sanitized = validateContainerTools(tools);
  const allowedTools = allowedToolsByLanguage[language];
  const unsupported = sanitized.filter((tool) => !allowedTools.has(tool));
  if (unsupported.length > 0) {
    throw new Error(`Unsupported verification tools for ${language}: ${unsupported.join(', ')}`);
  }
  return sanitized;
};

export const validateBuildArgs = (buildArgs: Record<string, string> = {}): Record<string, string> => {
  const sanitized: Record<string, string> = {};
  for (const [key, value] of Object.entries(buildArgs)) {
    if (!buildArgKeyPattern.test(key)) {
      throw new Error(`Invalid build argument key: ${JSON.stringify(key)}`);
    }
    if (typeof value !== 'string') {
      throw new Error(`Build argument ${key} must be a string`);
    }
    if (value.length > MAX_BUILD_ARG_VALUE_LENGTH || !buildArgValuePattern.test(value)) {
      throw new Error(`Invalid build argument value for ${key}`);
    }
    sanitized[key] = value;
  }
  return sanitized;
};

const imageReferenceHasUnsupportedCharacters = (reference: string): boolean => [...reference].some((char) => {
  const code = char.charCodeAt(0);
  return code <= 32 || code === 127 || ';$`|&<>\\'.includes(char);
});

const getImageTagSeparatorIndex = (reference: string): number => {
  const lastSlash = reference.lastIndexOf('/');
  const lastColon = reference.lastIndexOf(':');
  return lastColon > lastSlash ? lastColon : -1;
};

const validateImageRepositoryName = (name: string, reference: string): { registry?: string } => {
  const components = name.split('/');
  let registry: string | undefined;
  const first = components[0];
  const hasRegistry = components.length > 1 && first !== undefined && (
    first.includes('.') || first.includes(':') || first === 'localhost'
  );
  const repositoryComponents = hasRegistry ? components.slice(1) : components;
  if (hasRegistry) {
    if (!first || !registryComponentPattern.test(first)) {
      throw new Error(`Invalid image registry in reference: ${reference}`);
    }
    registry = first;
  }

  if (repositoryComponents.length === 0 || repositoryComponents.some((component) => !repositoryComponentPattern.test(component))) {
    throw new Error(`Invalid image repository in reference: ${reference}`);
  }

  return registry !== undefined ? { registry } : {};
};

const validateAllowedPushPrefix = (prefix: string): string => {
  if (typeof prefix !== 'string' || prefix.length === 0 || prefix.length > MAX_IMAGE_REFERENCE_LENGTH) {
    throw new Error('Allowed image push prefixes must be non-empty strings within length limits');
  }
  if (imageReferenceHasUnsupportedCharacters(prefix)) {
    throw new Error(`Allowed image push prefix contains unsupported characters: ${JSON.stringify(prefix)}`);
  }
  if (prefix.includes('@')) {
    throw new Error('Allowed image push prefix must use repository or tag prefixes, not digests');
  }

  const tagSeparator = getImageTagSeparatorIndex(prefix);
  if (tagSeparator >= 0) {
    const name = prefix.slice(0, tagSeparator);
    const tagPrefix = prefix.slice(tagSeparator + 1);
    if (!tagPrefix || !tagPattern.test(tagPrefix)) {
      throw new Error(`Invalid image tag prefix in allowed push policy: ${prefix}`);
    }
    validateImageRepositoryName(name, prefix);
    return prefix;
  }

  const namePrefix = prefix.endsWith('/') ? prefix.slice(0, -1) : prefix;
  if (!namePrefix) {
    throw new Error(`Invalid image repository prefix in allowed push policy: ${prefix}`);
  }
  validateImageRepositoryName(namePrefix, prefix);
  return prefix;
};

const isTagPrefixBoundary = (tagPrefix: string, nextChar: string): boolean => {
  const lastPrefixChar = tagPrefix.charAt(tagPrefix.length - 1);
  return tagPrefixBoundaryPattern.test(lastPrefixChar) || tagPrefixBoundaryPattern.test(nextChar);
};

const matchesAllowedPushPrefix = (reference: string, rawPrefix: string): boolean => {
  const prefix = validateAllowedPushPrefix(rawPrefix);
  if (!reference.startsWith(prefix)) {
    return false;
  }
  if (reference.length === prefix.length) {
    return true;
  }

  const nextChar = reference.charAt(prefix.length);
  const prefixTagSeparator = getImageTagSeparatorIndex(prefix);
  if (prefixTagSeparator >= 0) {
    return isTagPrefixBoundary(prefix.slice(prefixTagSeparator + 1), nextChar);
  }

  if (prefix.endsWith('/')) {
    return true;
  }
  return nextChar === '/' || nextChar === ':';
};

export const validateImageReference = (reference: string): ValidatedImageReference => {
  if (typeof reference !== 'string' || reference.length === 0 || reference.length > MAX_IMAGE_REFERENCE_LENGTH) {
    throw new Error('Image reference must be a non-empty string within length limits');
  }
  if (imageReferenceHasUnsupportedCharacters(reference)) {
    throw new Error(`Image reference contains unsupported characters: ${JSON.stringify(reference)}`);
  }
  if (reference.includes('@')) {
    throw new Error('Build image reference must use a tag, not a digest');
  }

  const lastColon = getImageTagSeparatorIndex(reference);
  if (lastColon < 0) {
    throw new Error(`Image reference must include an explicit tag: ${reference}`);
  }

  const name = reference.slice(0, lastColon);
  const tag = reference.slice(lastColon + 1);
  if (!name || !tagPattern.test(tag)) {
    throw new Error(`Invalid image tag in reference: ${reference}`);
  }

  const { registry } = validateImageRepositoryName(name, reference);

  return {
    reference,
    name,
    tag,
    ...(registry !== undefined ? { registry } : {}),
  };
};

export const assertPushPolicy = ({ imageRef, push, pushApproval, policy }: PushPolicyRequest): void => {
  if (!push) return;
  if (pushApproval !== CONTAINER_PUSH_APPROVAL) {
    throw new Error(`Pushing verification images requires pushApproval=${CONTAINER_PUSH_APPROVAL}`);
  }

  const allowedPrefixes = policy?.allowedPushPrefixes ?? [];
  if (allowedPrefixes.length === 0) {
    throw new Error('Pushing verification images is disabled until allowedPushPrefixes is configured');
  }
  if (!allowedPrefixes.some((prefix) => matchesAllowedPushPrefix(imageRef.reference, prefix))) {
    throw new Error(`Image reference is not allowed by container image push policy: ${imageRef.reference}`);
  }
};

export const assertCleanupConfirmation = (options: CleanupConfirmationOptions = {}): { dryRun: boolean } => {
  const dryRun = options.dryRun !== false;
  if (dryRun) {
    return { dryRun: true };
  }

  const expected = options.force ? CONTAINER_FORCE_CLEANUP_CONFIRM : CONTAINER_CLEANUP_CONFIRM;
  if (options.confirm !== expected) {
    throw new Error(`Container cleanup requires confirm=${expected}`);
  }
  return { dryRun: false };
};

export const redactBuildArgsInMessage = (message: string): string => message
  .replace(/(--build-arg(?:=|\s+))([^\s]+=[^\s]+)/g, '$1<redacted>')
  .replace(/(VERIFICATION_TOOLS=)[^\s]+/g, '$1<redacted>');

export const redactImageBuildContext = (buildContext: ImageBuildContext): ImageBuildContext => {
  const redacted: ImageBuildContext = { ...buildContext };
  if (redacted.buildArgs) {
    redacted.buildArgs = Object.fromEntries(
      Object.keys(redacted.buildArgs).map((key) => [key, '<redacted>']),
    );
  }
  return redacted;
};

const isPathInside = (candidate: string, root: string): boolean => {
  const relative = path.relative(root, candidate);
  return relative === '' || (!!relative && !relative.startsWith('..') && !path.isAbsolute(relative));
};

const isSensitiveHostPath = (candidate: string): boolean => {
  const normalized = path.resolve(candidate);
  if (normalized === path.parse(normalized).root) return true;
  const sensitiveRoots = [
    '/bin',
    '/boot',
    '/dev',
    '/etc',
    '/proc',
    '/root',
    '/run',
    '/sys',
    '/var/lib/containers',
    '/var/lib/docker',
    '/var/run',
  ];
  return sensitiveRoots.some((sensitive) => normalized === sensitive || normalized.startsWith(`${sensitive}${path.sep}`));
};

export const resolveApprovedWorkspacePath = async ({
  projectPath,
  workspaceRoot = process.env['AE_CONTAINER_WORKSPACE_ROOT'] || process.cwd(),
}: WorkspaceResolutionOptions): Promise<WorkspaceResolutionResult> => {
  if (typeof projectPath !== 'string' || projectPath.length === 0) {
    throw new Error('projectPath is required');
  }

  let resolvedRoot: string;
  try {
    resolvedRoot = await fs.realpath(path.resolve(workspaceRoot));
  } catch {
    throw new Error('Approved workspace root does not exist');
  }

  if (isSensitiveHostPath(resolvedRoot)) {
    throw new Error('Approved workspace root is too broad or sensitive');
  }

  const candidate = path.isAbsolute(projectPath)
    ? path.resolve(projectPath)
    : path.resolve(resolvedRoot, projectPath);

  let resolvedProject: string;
  try {
    resolvedProject = await fs.realpath(candidate);
  } catch {
    throw new Error('Project path does not exist');
  }

  if (!isPathInside(resolvedProject, resolvedRoot)) {
    throw new Error('Project path is outside approved workspace root');
  }
  if (isSensitiveHostPath(resolvedProject)) {
    throw new Error('Project path points to a sensitive host directory');
  }

  return {
    workspaceRoot: resolvedRoot,
    projectPath: resolvedProject,
  };
};
