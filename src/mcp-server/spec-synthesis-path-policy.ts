import {
  resolveContainedWorkspacePath,
  resolveWorkspacePath,
  resolveWorkspaceRoot,
  toWorkspaceRelativePath,
} from '../utils/workspace-path-policy.js';
import { DEFAULT_HIGH_IMPACT_APPROVAL_SCOPES } from '../utils/high-impact-action-policy.js';
import type { SpawnSyncOptions } from 'node:child_process';

export type SpecCodegenTarget = 'typescript' | 'api' | 'database' | 'react';
export const SPEC_CODEGEN_MATERIALIZE_APPROVAL_SCOPE = DEFAULT_HIGH_IMPACT_APPROVAL_SCOPES['codegen-materialize'];

export interface ResolvedSpecCompilePaths {
  workspaceRoot: string;
  inputPath: string;
  outputPath?: string;
}

export interface ResolvedSpecCodegenPaths {
  workspaceRoot: string;
  irPath: string;
  irPathArg: string;
  outBase: string;
  outBaseArg: string;
  targetOutDirs: Record<SpecCodegenTarget, string>;
  targetOutDirArgs: Record<SpecCodegenTarget, string>;
}

export function createSpecCodegenChildProcessOptions(workspaceRoot: string): SpawnSyncOptions {
  return {
    stdio: 'inherit',
    cwd: workspaceRoot,
    env: {
      ...process.env,
      AE_CODEGEN_WORKSPACE_ROOT: workspaceRoot,
    },
  };
}

export function buildSpecCodegenCliArgs(
  irPathArg: string,
  targetOutDirArg: string,
  target: SpecCodegenTarget,
  approvalScope = SPEC_CODEGEN_MATERIALIZE_APPROVAL_SCOPE,
): string[] {
  return [
    'dist/src/cli/index.js',
    'codegen',
    'generate',
    '-i',
    irPathArg,
    '-o',
    targetOutDirArg,
    '-t',
    target,
    '--apply',
    '--approval-scope',
    approvalScope,
  ];
}

export function resolveSpecSynthesisWorkspaceRoot(): string {
  return resolveWorkspaceRoot({ envVar: 'AE_MCP_WORKSPACE_ROOT' });
}

export function resolveSpecCompilePaths(
  inputPath: string,
  outputPath?: string,
  workspaceRoot = resolveSpecSynthesisWorkspaceRoot(),
): ResolvedSpecCompilePaths {
  const resolvedInputPath = resolveWorkspacePath(inputPath, {
    workspaceRoot,
    label: 'ae_spec_compile inputPath',
  });
  const resolvedOutputPath = outputPath !== undefined
    ? resolveWorkspacePath(outputPath, {
      workspaceRoot,
      label: 'ae_spec_compile outputPath',
    })
    : undefined;

  return {
    workspaceRoot,
    inputPath: resolvedInputPath,
    ...(resolvedOutputPath !== undefined ? { outputPath: resolvedOutputPath } : {}),
  };
}

export function resolveSpecValidateInputPath(
  inputPath: string,
  workspaceRoot = resolveSpecSynthesisWorkspaceRoot(),
): string {
  return resolveWorkspacePath(inputPath, {
    workspaceRoot,
    label: 'ae_spec_validate inputPath',
  });
}

export function resolveSpecCodegenPaths(
  irPath: string,
  targets: readonly SpecCodegenTarget[],
  outDir?: string,
  workspaceRoot = resolveSpecSynthesisWorkspaceRoot(),
): ResolvedSpecCodegenPaths {
  const resolvedIrPath = resolveWorkspacePath(irPath, {
    workspaceRoot,
    label: 'ae_spec_codegen irPath',
  });
  const irPathArg = toWorkspaceRelativePath(resolvedIrPath, {
    workspaceRoot,
    label: 'ae_spec_codegen irPath',
  });

  const outBase = outDir || 'generated';
  const outBasePath = resolveWorkspacePath(outBase, {
    workspaceRoot,
    label: 'ae_spec_codegen outDir',
  });
  const outBaseArg = toWorkspaceRelativePath(outBasePath, {
    workspaceRoot,
    label: 'ae_spec_codegen outDir',
  });

  const targetOutDirs = {} as Record<SpecCodegenTarget, string>;
  const targetOutDirArgs = {} as Record<SpecCodegenTarget, string>;
  for (const target of targets) {
    const targetDir = resolveContainedWorkspacePath(outBasePath, target, `ae_spec_codegen ${target} outDir`);
    targetOutDirs[target] = targetDir;
    targetOutDirArgs[target] = toWorkspaceRelativePath(targetDir, {
      workspaceRoot,
      label: `ae_spec_codegen ${target} outDir`,
    });
  }

  return {
    workspaceRoot,
    irPath: resolvedIrPath,
    irPathArg,
    outBase: outBasePath,
    outBaseArg,
    targetOutDirs,
    targetOutDirArgs,
  };
}
