import path from 'node:path';
import type { CommandContext } from '../slash-command-manager.js';
import {
  resolveContainedWorkspacePath,
  resolveWorkspacePath,
  toWorkspaceRelativePath,
} from '../../utils/workspace-path-policy.js';

const commandWorkspaceRoot = (context: CommandContext): string => path.resolve(context.projectRoot);

export function resolveExtendedCommandPath(
  context: CommandContext,
  inputPath: string,
  label: string,
): string {
  return resolveWorkspacePath(inputPath, {
    workspaceRoot: commandWorkspaceRoot(context),
    label,
  });
}

export function resolveExtendedCommandContainedPath(
  baseDir: string,
  relativePath: string,
  label: string,
): string {
  return resolveContainedWorkspacePath(baseDir, relativePath, label);
}

export function toExtendedCommandRelativePath(context: CommandContext, resolvedPath: string): string {
  return toWorkspaceRelativePath(resolvedPath, {
    workspaceRoot: commandWorkspaceRoot(context),
    label: 'extended command path',
  });
}
