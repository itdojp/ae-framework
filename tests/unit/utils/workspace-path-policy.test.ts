import path from 'node:path';
import { mkdirSync, rmSync, symlinkSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import {
  assertWithinWorkspace,
  resolveArtifactPath,
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

  it('asserts absolute or normalized candidate paths stay inside the approved workspace', () => {
    const resolved = assertWithinWorkspace(path.join(workspaceRoot, 'generated', '..', 'reports'), {
      workspaceRoot,
      label: 'candidate path',
    });

    expect(resolved).toBe(path.join(workspaceRoot, 'reports'));
    expect(() =>
      assertWithinWorkspace(path.join(workspaceRoot, '..', 'outside'), {
        workspaceRoot,
        label: 'candidate path',
      }),
    ).toThrow(WorkspacePathPolicyError);
    expect(() =>
      assertWithinWorkspace('C:\\temp\\outside', {
        workspaceRoot,
        label: 'candidate path',
      }),
    ).toThrow(WorkspacePathPolicyError);
    expect(() =>
      assertWithinWorkspace('C:/temp/outside', {
        workspaceRoot,
        label: 'candidate path',
      }),
    ).toThrow(WorkspacePathPolicyError);
    expect(() =>
      assertWithinWorkspace(path.join(workspaceRoot, '.git', 'config'), {
        workspaceRoot,
        label: 'candidate path',
      }),
    ).toThrow(WorkspacePathPolicyError);
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

  it('resolves artifact paths under an approved artifact root', () => {
    expect(resolveArtifactPath('reports/summary.json', { workspaceRoot, label: 'artifact output' })).toBe(
      path.join(workspaceRoot, 'artifacts', 'reports', 'summary.json'),
    );
    expect(resolveArtifactPath('artifacts/reports/summary.json', { workspaceRoot, label: 'artifact output' })).toBe(
      path.join(workspaceRoot, 'artifacts', 'reports', 'summary.json'),
    );
    expect(
      resolveArtifactPath('summary.json', {
        workspaceRoot,
        artifactRoot: 'reports/conformance',
        label: 'custom artifact output',
      }),
    ).toBe(path.join(workspaceRoot, 'reports', 'conformance', 'summary.json'));
  });

  it('rejects artifact paths outside the approved artifact root', () => {
    expect(() =>
      resolveArtifactPath(path.join(workspaceRoot, 'artifacts', 'summary.json'), {
        workspaceRoot,
        label: 'artifact output',
      }),
    ).toThrow(WorkspacePathPolicyError);
    expect(() =>
      resolveArtifactPath(path.join(workspaceRoot, 'reports', 'summary.json'), {
        workspaceRoot,
        allowAbsolute: true,
        label: 'artifact output',
      }),
    ).toThrow(WorkspacePathPolicyError);
    expect(() =>
      resolveArtifactPath('../summary.json', {
        workspaceRoot,
        label: 'artifact output',
      }),
    ).toThrow(WorkspacePathPolicyError);
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

  it('rejects artifact symlink ancestors that resolve outside the approved artifact root', () => {
    const root = path.join(workspaceRoot, `artifact-symlink-${Date.now()}`);
    const artifactRoot = path.join(root, 'artifacts');
    const outside = path.join(process.cwd(), 'artifacts', `workspace-artifact-policy-outside-${Date.now()}`);
    mkdirSync(artifactRoot, { recursive: true });
    mkdirSync(outside, { recursive: true });

    try {
      symlinkSync(outside, path.join(artifactRoot, 'linked-outside'), 'dir');
    } catch {
      rmSync(root, { recursive: true, force: true });
      rmSync(outside, { recursive: true, force: true });
      return;
    }

    try {
      expect(() =>
        resolveArtifactPath('linked-outside/report.json', {
          workspaceRoot: root,
          artifactRoot,
          label: 'artifact output',
        }),
      ).toThrow(WorkspacePathPolicyError);
    } finally {
      rmSync(root, { recursive: true, force: true });
      rmSync(outside, { recursive: true, force: true });
    }
  });
});
