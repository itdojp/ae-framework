import path from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  createSpecCodegenChildProcessOptions,
  resolveSpecCodegenPaths,
  resolveSpecCompilePaths,
} from '../../../src/mcp-server/spec-synthesis-path-policy.js';
import { WorkspacePathPolicyError } from '../../../src/utils/workspace-path-policy.js';

describe('spec synthesis MCP path policy', () => {
  const workspaceRoot = path.resolve(process.cwd(), 'artifacts', 'spec-synthesis-path-policy');

  it('resolves compile input/output paths under the MCP workspace', () => {
    const paths = resolveSpecCompilePaths('specs/sample.md', 'artifacts/spec-synthesis/ae-ir.json', workspaceRoot);

    expect(paths.inputPath).toBe(path.join(workspaceRoot, 'specs', 'sample.md'));
    expect(paths.outputPath).toBe(path.join(workspaceRoot, 'artifacts', 'spec-synthesis', 'ae-ir.json'));
  });

  it('rejects compile output traversal before the compiler write sink', () => {
    expect(() => resolveSpecCompilePaths('specs/sample.md', '../outside.json', workspaceRoot)).toThrow(
      WorkspacePathPolicyError,
    );
    expect(() => resolveSpecCompilePaths('/absolute/spec.md', 'artifacts/ae-ir.json', workspaceRoot)).toThrow(
      WorkspacePathPolicyError,
    );
  });

  it('keeps codegen child-process arguments workspace-relative', () => {
    const paths = resolveSpecCodegenPaths(
      '.ae/ae-ir.json',
      ['typescript', 'react'],
      'artifacts/generated',
      workspaceRoot,
    );

    expect(paths.irPath).toBe(path.join(workspaceRoot, '.ae', 'ae-ir.json'));
    expect(paths.irPathArg).toBe('.ae/ae-ir.json');
    expect(paths.outBaseArg).toBe('artifacts/generated');
    expect(paths.targetOutDirArgs).toEqual({
      typescript: 'artifacts/generated/typescript',
      react: 'artifacts/generated/react',
    });
  });

  it('pins spawned codegen CLI execution to the MCP workspace', () => {
    const options = createSpecCodegenChildProcessOptions(workspaceRoot);

    expect(options.cwd).toBe(workspaceRoot);
    expect(options.env).toMatchObject({
      AE_CODEGEN_WORKSPACE_ROOT: workspaceRoot,
    });
  });

  it('rejects codegen path escapes before spawnSync receives paths', () => {
    expect(() => resolveSpecCodegenPaths('../ae-ir.json', ['typescript'], 'generated', workspaceRoot)).toThrow(
      WorkspacePathPolicyError,
    );
    expect(() => resolveSpecCodegenPaths('.ae/ae-ir.json', ['typescript'], '/var/tmp/generated', workspaceRoot)).toThrow(
      WorkspacePathPolicyError,
    );
  });
});
