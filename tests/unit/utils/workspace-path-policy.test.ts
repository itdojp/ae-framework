import path from 'node:path';
import { mkdirSync, rmSync, symlinkSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import {
  resolveContainedWorkspacePath,
  resolveWorkspacePath,
  toWorkspaceRelativePath,
  WorkspacePathPolicyError,
} from '../../../src/utils/workspace-path-policy.js';

describe('workspace path policy', () => {
  const workspaceRoot = path.resolve(process.cwd(), 'artifacts', 'workspace-path-policy');

  it('resolves workspace-relative paths under the approved root', () => {
    const resolved = resolveWorkspacePath('generated/typescript', {
      workspaceRoot,
      label: 'test output',
    });

    expect(resolved).toBe(path.join(workspaceRoot, 'generated', 'typescript'));
    expect(toWorkspaceRelativePath(resolved, { workspaceRoot })).toBe('generated/typescript');
  });

  it('rejects absolute paths and dot-segment traversal before filesystem access', () => {
    for (const candidate of [
      path.join(workspaceRoot, 'generated'),
      '/var/tmp/generated',
      '../generated',
      'generated/../outside',
      'generated/./typescript',
      '.GIT/config',
      'C:\\temp\\generated',
      'generated\\typescript',
      '//server/share/generated',
    ]) {
      expect(() => resolveWorkspacePath(candidate, { workspaceRoot, label: 'test path' })).toThrow(
        WorkspacePathPolicyError,
      );
    }
  });

  it('contains generated relative files under their output directory', () => {
    const outputDir = path.join(workspaceRoot, 'generated');

    expect(resolveContainedWorkspacePath(outputDir, 'components/ProductForm.tsx')).toBe(
      path.join(outputDir, 'components', 'ProductForm.tsx'),
    );
    expect(() => resolveContainedWorkspacePath(outputDir, '../ProductForm.tsx')).toThrow(WorkspacePathPolicyError);
    expect(() => resolveContainedWorkspacePath(outputDir, 'components/../../ProductForm.tsx')).toThrow(
      WorkspacePathPolicyError,
    );
  });

  it('rejects existing symlink ancestors that resolve outside the workspace', () => {
    const root = path.join(workspaceRoot, `symlink-${Date.now()}`);
    const outside = path.join(process.cwd(), 'artifacts', `workspace-path-policy-outside-${Date.now()}`);
    mkdirSync(root, { recursive: true });
    mkdirSync(outside, { recursive: true });

    try {
      symlinkSync(outside, path.join(root, 'linked-outside'), 'dir');
    } catch {
      rmSync(root, { recursive: true, force: true });
      rmSync(outside, { recursive: true, force: true });
      return;
    }

    try {
      expect(() => resolveWorkspacePath('linked-outside/generated', { workspaceRoot: root })).toThrow(
        WorkspacePathPolicyError,
      );
    } finally {
      rmSync(root, { recursive: true, force: true });
      rmSync(outside, { recursive: true, force: true });
    }
  });
});
